import OAI.Probability.ContinuumTransition.Model

namespace OAI

universe u_1

section

open scoped Topology BigOperators
open Set Filter

noncomputable section

namespace ContinuumTemperature

abbrev Parameter := ℝ × ℝ

def pressureDomain : Set Parameter := {x | 0 < x.1}

def Supports (P : Parameter → ℝ) (x v : Parameter) : Prop :=
  ∀ y ∈ pressureDomain, P x + v.1 * (y.1 - x.1) + v.2 * (y.2 - x.2) ≤ P y

def IsPartialConjugate (Q : Parameter → ℝ) (H : ℝ → ℝ → ℝ) : Prop :=
  ∀ β d : ℝ, 0 < β → 0 ≤ d →
    IsLUB (range (fun h : ℝ => h * d - Q (β, h))) (H β d)

def quadraticObjective (ξ v : Parameter) (β : ℝ) : ℝ :=
  ξ.1 * v.1 + ξ.2 * v.2 + β / 2 * v.2 ^ 2

theorem strict_face_support {K : Set Parameter} {ξ v : Parameter} {β : ℝ}
    (hmax : ∀ u ∈ K, quadraticObjective ξ u β ≤ quadraticObjective ξ v β)
    {u : Parameter} (hu : u ∈ K) :
    β / 2 * (u.2 - v.2) ^ 2 ≤
      ξ.1 * (v.1 - u.1) + (ξ.2 + β * v.2) * (v.2 - u.2) := by
  have h := hmax u hu
  dsimp [quadraticObjective] at h
  nlinarith [sq_nonneg (u.2 - v.2)]

theorem weighted_maximizer_densities {ι : Type u_1} [Fintype ι]
    {K : Set Parameter} {ξ v : Parameter} {β : ℝ}
    (hβ : 0 < β) (a : ι → ℝ) (z : ι → Parameter)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hz : ∀ i, z i ∈ K) (hv : ∑ i, a i • z i = v)
    (hmax : ∀ u ∈ K, quadraticObjective ξ u β ≤ quadraticObjective ξ v β) :
    ∀ i, a i ≠ 0 → (z i).2 = v.2 := by
  have hfst : ∑ i, a i * (z i).1 = v.1 := by
    simpa only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using congrArg Prod.fst hv
  have hsnd : ∑ i, a i * (z i).2 = v.2 := by
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd hv
  let gap : ι → ℝ := fun i =>
    ξ.1 * (v.1 - (z i).1) + (ξ.2 + β * v.2) * (v.2 - (z i).2)
  have hgap : ∀ i, 0 ≤ gap i := by
    intro i
    exact le_trans (mul_nonneg (by positivity) (sq_nonneg _))
      (strict_face_support hmax (hz i))
  have hsum : ∑ i, a i * gap i = 0 := by
    calc
      ∑ i, a i * gap i =
          ∑ i, (ξ.1 * (a i * v.1 - a i * (z i).1) +
            (ξ.2 + β * v.2) * (a i * v.2 - a i * (z i).2)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [gap]
        ring
      _ = ξ.1 * ((∑ i, a i) * v.1 - ∑ i, a i * (z i).1) +
          (ξ.2 + β * v.2) * ((∑ i, a i) * v.2 - ∑ i, a i * (z i).2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = 0 := by rw [ha1, hfst, hsnd]; ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => mul_nonneg (ha i) (hgap i))).mp hsum
  intro i hi
  have hgi : gap i = 0 := (mul_eq_zero.mp (hzero i (Finset.mem_univ i))).resolve_left hi
  have hstrict := strict_face_support hmax (hz i)
  change β / 2 * ((z i).2 - v.2) ^ 2 ≤ gap i at hstrict
  rw [hgi] at hstrict
  have hs : ((z i).2 - v.2) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((z i).2 - v.2)]
  nlinarith [sq_nonneg ((z i).2 - v.2)]

theorem quadratic_maximizer_mem_group {κ : Type u_1} (K : κ → Set Parameter)
    (hconv : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    {ξ v : Parameter} {β : ℝ} (hβ : 0 < β)
    (hv : v ∈ convexHull ℝ (⋃ i, K i))
    (hmax : ∀ u ∈ convexHull ℝ (⋃ i, K i),
      quadraticObjective ξ u β ≤ quadraticObjective ξ v β) : v ∈ ⋃ i, K i := by
  classical
  obtain ⟨ι, inst, a, z, ha, ha1, hz, hzv⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  let _ := inst
  have hd := weighted_maximizer_densities hβ a z ha ha1
    (fun i => subset_convexHull ℝ _ (hz i)) hzv hmax
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ha1 ▸ one_ne_zero)
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hz i₀)
  have hzk : ∀ i, a i ≠ 0 → z i ∈ K k := by
    intro i hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hz i)
    have hjk : j = k := by
      by_contra hne
      exact Set.disjoint_left.mp (hsep j k hne)
        ⟨z i, hj, hd i hi⟩ ⟨z i₀, hk, hd i₀ hi₀⟩
    simpa only [hjk] using hj
  let z' : ι → Parameter := fun i => if a i = 0 then z i₀ else z i
  have hz' : ∀ i, z' i ∈ K k := by
    intro i
    dsimp [z']
    split_ifs with hi
    · exact hk
    · exact hzk i hi
  have hsumeq : ∑ i, a i • z' i = v := by
    rw [← hzv]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [z']
    split_ifs with hi
    · simp [hi]
    · rfl
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  rw [← hsumeq]
  exact (hconv k).sum_mem (fun i _ => ha i) ha1 (fun i _ => hz' i)

theorem fenchel_eq_of_support {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {β h s d : ℝ}
    (hβ : 0 < β) (hd : 0 ≤ d) (hv : Supports Q (β, h) (s, d)) :
    H β d = h * d - Q (β, h) := by
  have hL := hH β d hβ hd
  apply le_antisymm
  · apply hL.2
    rintro _ ⟨z, rfl⟩
    have hz := hv (β, z) hβ
    dsimp at hz
    nlinarith
  · exact hL.1 (mem_range_self h)

theorem supergradient_of_support {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {β h s d : ℝ}
    (hβ : 0 < β) (hd : 0 ≤ d) (hv : Supports Q (β, h) (s, d)) :
    ∀ β' : ℝ, 0 < β' → H β' d ≤ H β d - s * (β' - β) := by
  have heq := fenchel_eq_of_support hH hβ hd hv
  intro β' hβ'
  apply (hH β' d hβ' hd).2
  rintro _ ⟨z, rfl⟩
  have hz := hv (β', z) hβ'
  dsimp at hz
  nlinarith

theorem concave_one_sided_support {F : ℝ → ℝ}
    (hc : ConcaveOn ℝ (Ioi 0) F) {β : ℝ} (hβ : 0 < β) :
    ∃ l r : ℝ,
      HasDerivWithinAt F l (Iic β) β ∧
      HasDerivWithinAt F r (Ici β) β ∧
      ∀ u : ℝ, (∀ y : ℝ, 0 < y → F y ≤ F β + u * (y - β)) → r ≤ u ∧ u ≤ l := by
  have hmem : β ∈ interior (Ioi (0 : ℝ)) := by simpa using hβ
  let l := -derivWithin (-F) (Iio β) β
  let r := -derivWithin (-F) (Ioi β) β
  have hl : HasDerivWithinAt F l (Iio β) β := by
    simpa only [neg_neg] using (hc.neg.hasDerivWithinAt_leftDeriv_of_mem_interior hmem).neg
  have hr : HasDerivWithinAt F r (Ioi β) β := by
    simpa only [neg_neg] using (hc.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hmem).neg
  refine ⟨l, r, hl.Iic_of_Iio, hr.Ici_of_Ioi, ?_⟩
  intro u hu
  have hposL : ∀ᶠ y : ℝ in 𝓝[<] β, 0 < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hβ)
  have hposR : ∀ᶠ y : ℝ in 𝓝[>] β, 0 < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hβ)
  constructor
  · apply le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr)
    filter_upwards [hposR, eventually_mem_nhdsWithin] with y hy hby
    rw [slope_def_field]
    apply (div_le_iff₀ (sub_pos.mpr hby)).mpr
    linarith [hu y hy]
  · apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl)
    filter_upwards [hposL, eventually_mem_nhdsWithin] with y hy hyb
    rw [slope_def_field]
    apply (le_div_iff_of_neg (sub_neg.mpr hyb)).mpr
    linarith [hu y hy]

theorem canonical_jump_of_two_supports {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {t β h d s₁ s₂ : ℝ}
    (ht : 0 < t) (hβ : 0 < β) (hd : 0 ≤ d)
    (hc : ConcaveOn ℝ (Ioi 0) (fun b => H b d))
    (hs : s₁ < s₂) (hv₁ : Supports Q (β, h) (s₁, d))
    (hv₂ : Supports Q (β, h) (s₂, d)) :
    ∃ l r : ℝ,
      HasDerivWithinAt (fun b => t * H b d / b) l (Iic β) β ∧
      HasDerivWithinAt (fun b => t * H b d / b) r (Ici β) β ∧
      t / β * (s₂ - s₁) ≤ l - r ∧ r < l := by
  obtain ⟨l, r, hl, hr, hbounds⟩ := concave_one_sided_support hc hβ
  have hb₁ := (hbounds (-s₁) (by
    intro y hy
    simpa only [neg_mul, sub_eq_add_neg] using
      supergradient_of_support hH hβ hd hv₁ y hy)).2
  have hb₂ := (hbounds (-s₂) (by
    intro y hy
    simpa only [neg_mul, sub_eq_add_neg] using
      supergradient_of_support hH hβ hd hv₂ y hy)).1
  have hneq : β ≠ 0 := ne_of_gt hβ
  let l' := (t * l * β - t * H β d) / β ^ 2
  let r' := (t * r * β - t * H β d) / β ^ 2
  have hl' : HasDerivWithinAt (fun b => t * H b d / b) l' (Iic β) β := by
    simpa only [Pi.div_def, id_eq, mul_one, l'] using
      (hl.const_mul t).div (hasDerivAt_id β).hasDerivWithinAt hneq
  have hr' : HasDerivWithinAt (fun b => t * H b d / b) r' (Ici β) β := by
    simpa only [Pi.div_def, id_eq, mul_one, r'] using
      (hr.const_mul t).div (hasDerivAt_id β).hasDerivWithinAt hneq
  have heq : l' - r' = t / β * (l - r) := by
    dsimp [l', r']
    field_simp
    ring
  have hgap : t / β * (s₂ - s₁) ≤ l' - r' := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ht.le hβ.le)
  refine ⟨l', r', hl', hr', hgap, ?_⟩
  have hstrict : 0 < t / β * (s₂ - s₁) := mul_pos (div_pos ht hβ) (sub_pos.mpr hs)
  linarith

def SlopeBall (g : Parameter) (γ : ℝ) : Set Parameter :=
  {v | (v.1 - g.1) ^ 2 + (v.2 - g.2) ^ 2 ≤ γ ^ 2}

theorem canonical_interval_of_support_ball {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {t β h γ : ℝ} {g : Parameter}
    (ht : 0 < t) (hβ : 0 < β) (hγ : 0 < γ) (hg : 0 < g.2)
    (hc : ∀ d : ℝ, 0 < d → ConcaveOn ℝ (Ioi 0) (fun b => H b d))
    (hball : ∀ v ∈ SlopeBall g γ, Supports Q (β, h) v) :
    ∃ I : Set ℝ, IsOpen I ∧ OrdConnected I ∧ I.Nonempty ∧ I ⊆ Ioi 0 ∧
      ∀ d ∈ I, ∃ l r : ℝ,
        HasDerivWithinAt (fun b => t * H b d / b) l (Iic β) β ∧
        HasDerivWithinAt (fun b => t * H b d / b) r (Ici β) β ∧
        t * γ / β ≤ l - r ∧ r < l := by
  let δ := min (γ / 2) (g.2 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδγ : δ ≤ γ / 2 := min_le_left _ _
  have hδg : δ ≤ g.2 / 2 := min_le_right _ _
  let I := Ioo (g.2 - δ) (g.2 + δ)
  have hpos : I ⊆ Ioi 0 := by
    intro d hd
    dsimp [I] at hd
    change 0 < d
    linarith [hd.1]
  refine ⟨I, isOpen_Ioo, ordConnected_Ioo, ⟨g.2, ?_⟩, hpos, ?_⟩
  · change g.2 - δ < g.2 ∧ g.2 < g.2 + δ
    constructor <;> linarith
  · intro d hd
    have hdpos := hpos hd
    have hnear : |d - g.2| < γ / 2 := by
      rw [abs_lt]
      dsimp [I] at hd
      constructor <;> linarith [hd.1, hd.2]
    have hsq : (d - g.2) ^ 2 < (γ / 2) ^ 2 := by
      nlinarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    have hv₁ : (g.1 - γ / 2, d) ∈ SlopeBall g γ := by
      dsimp [SlopeBall]
      nlinarith [sq_pos_of_pos hγ]
    have hv₂ : (g.1 + γ / 2, d) ∈ SlopeBall g γ := by
      dsimp [SlopeBall]
      nlinarith [sq_pos_of_pos hγ]
    obtain ⟨l, r, hl, hr, hgap, hstrict⟩ := canonical_jump_of_two_supports hH
      ht hβ hdpos.le (hc d hdpos) (by linarith : g.1 - γ / 2 < g.1 + γ / 2)
      (hball _ hv₁) (hball _ hv₂)
    refine ⟨l, r, hl, hr, ?_, hstrict⟩
    convert hgap using 1
    ring

end ContinuumTemperature
end
end

end OAI
