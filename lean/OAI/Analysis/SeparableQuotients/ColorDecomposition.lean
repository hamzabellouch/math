import OAI.Analysis.SeparableQuotients.FiniteLp

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma convex_sum_le_one {E : Type*} [AddCommGroup E] [Module ℚ E]
    {S : Set E} (hS : Convex ℚ S) (h0 : (0 : E) ∈ S)
    {ι : Type*} [Fintype ι] (a : ι → ℚ) (x : ι → E)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i ≤ 1) (hx : ∀ i, x i ∈ S) :
    (∑ i, a i • x i) ∈ S := by
  let w : Option ι → ℚ := fun i => i.elim (1 - ∑ j, a j) a
  let z : Option ι → E := fun i => i.elim 0 x
  have hw : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ w i := by
    rintro (_ | i) _
    · exact sub_nonneg.mpr hs
    · exact ha i
  have hs' : ∑ i, w i = 1 := by simp [w, Fintype.sum_option]
  have hz : ∀ i ∈ (Finset.univ : Finset (Option ι)), z i ∈ S := by
    rintro (_ | i) _
    · exact h0
    · exact hx i
  simpa [w, z, Fintype.sum_option] using hS.sum_mem hw hs' hz

lemma absConvex_sum_le_one {E : Type*} [AddCommGroup E] [Module ℚ E]
    {S : Set E} (hS : AbsConvex ℚ S) (h0 : (0 : E) ∈ S)
    {ι : Type*} [Fintype ι] (a : ι → ℚ) (x : ι → E)
    (hs : ∑ i, |a i| ≤ 1) (hx : ∀ i, x i ∈ S) :
    (∑ i, a i • x i) ∈ S := by
  let z : ι → E := fun i => if 0 ≤ a i then x i else -x i
  have hz : ∀ i, z i ∈ S := by
    intro i
    dsimp [z]
    split_ifs
    · exact hx i
    · exact hS.1.neg_mem_iff.mpr (hx i)
  have heq : ∀ i, |a i| • z i = a i • x i := by
    intro i
    by_cases hi : 0 ≤ a i
    · simp [z, hi, abs_of_nonneg hi]
    · simp [z, hi, abs_of_neg (lt_of_not_ge hi)]
  simpa only [heq] using convex_sum_le_one hS.2 h0 (fun i => |a i|) z
    (fun i => abs_nonneg _) hs hz

def colorSet (k : ℕ) : Set Γ := {a | Colors.color a = k}

def colorRestrict (k : ℕ) (A : Crop) (x : Array) : Array :=
  restrict (colorSet k) (restrict (A.set .mixed) x)

lemma colorRestrict_eq (k : ℕ) (A : Crop) (x : Array) :
    colorRestrict k A x = restrict (colorSet k ∩ A.set .mixed) x :=
  restrict_restrict _ _ _

lemma mixed_color_unique {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive .mixed (v i) (v j))
    (k : ℕ) (A : Crop) {i j : Fin n}
    (hi : colorRestrict k A (v i) ≠ 0) (hj : colorRestrict k A (v j) ≠ 0) : i = j := by
  have hex : ∀ x : Array, x ≠ 0 → ∃ a, x a ≠ 0 := by
    intro x hx
    by_contra hh
    push Not at hh
    exact hx (Finsupp.ext hh)
  obtain ⟨a, ha⟩ := hex _ hi
  obtain ⟨b, hb⟩ := hex _ hj
  have ha' : a ∈ (v i).support ∧ Colors.color a = k := by
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩
    · intro hz
      simp [colorRestrict, hz] at ha
    · by_contra hh
      simp [colorRestrict, colorSet, hh] at ha
  have hb' : b ∈ (v j).support ∧ Colors.color b = k := by
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩
    · intro hz
      simp [colorRestrict, hz] at hb
    · by_contra hh
      simp [colorRestrict, colorSet, hh] at hb
  rcases lt_trichotomy i j with hij | hij | hij
  · have hh := (h i j hij a ha'.1 b hb'.1).2 rfl
    omega
  · exact hij
  · have hh := (h j i hij b hb'.1 a ha'.1).2 rfl
    omega

lemma colorRestrict_sum {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive .mixed (v i) (v j))
    (k : ℕ) (A : Crop) (i : Fin n) (hi : colorRestrict k A (v i) ≠ 0) :
    colorRestrict k A (∑ j, v j) = colorRestrict k A (v i) := by
  simp only [colorRestrict, restrict_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_contra hj
    exact hji (mixed_color_unique v h k A hj hi)
  · simp

lemma colorRestrict_sum_zero {n : ℕ} (v : Fin n → Array)
    (k : ℕ) (A : Crop) (h : ∀ i, colorRestrict k A (v i) = 0) :
    colorRestrict k A (∑ j, v j) = 0 := by
  simp only [colorRestrict, restrict_sum] at h ⊢
  simp only [h, Finset.sum_const_zero]

lemma TypeI.color_decomposition (e : TypeI .mixed) (k : ℕ) (A : Crop)
    {S : Set Array} (h0 : (0 : Array) ∈ S)
    (h : ∀ i, colorRestrict k A (e.child i) ∈ S) :
    ∃ g ∈ S, colorRestrict k A e.value = (1 / (Family.mixed.m e.weight : ℚ)) • g := by
  by_cases hex : ∃ i, colorRestrict k A (e.child i) ≠ 0
  · obtain ⟨i, hi⟩ := hex
    refine ⟨colorRestrict k A (e.child i), h i, ?_⟩
    simp only [TypeI.value, colorRestrict, restrict_smul]
    congr 1
    exact colorRestrict_sum e.child e.successive k A i hi
  · push Not at hex
    refine ⟨0, h0, ?_⟩
    have hz := colorRestrict_sum_zero e.child k A hex
    simp only [TypeI.value, colorRestrict, restrict_smul] at hz ⊢
    rw [hz, smul_zero]

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma FinitePath.color_decomposition (P : FinitePath .mixed) (k : ℕ) (A : Crop)
    {S : Set Array} (h0 : (0 : Array) ∈ S)
    (h : ∀ i j, colorRestrict k A ((P.piece i).child j) ∈ S) :
    ∃ (i : Fin P.length) (g : Array), g ∈ S ∧
      colorRestrict k A P.value = (1 / (Family.mixed.m (P.raw.weight i) : ℚ)) • g ∧
      (colorRestrict k A P.value ≠ 0 → P.raw.weight i ∈ P.active A) := by
  by_cases hex : ∃ i : Fin P.length, colorRestrict k A (P.raw.piece i) ≠ 0
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨g, hg, heq⟩ := (P.piece i).color_decomposition k A h0 (h i)
    have hv : colorRestrict k A P.value = colorRestrict k A (P.raw.piece i) :=
      colorRestrict_sum (fun i : Fin P.length => P.raw.piece i) P.mixed_successive k A i hi
    refine ⟨i, g, hg, ?_, ?_⟩
    · rw [hv, ← P.value_eq, heq, P.weight_eq]
    · intro _
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      intro hz
      apply hi
      simp only [colorRestrict, hz, restrict_zero]
  · push Not at hex
    have hz : colorRestrict k A P.value = 0 := colorRestrict_sum_zero _ k A hex
    exact ⟨⟨0, P.length_pos⟩, 0, h0, by simp [hz], by simp [hz]⟩

lemma TypeII.color_mem (e : TypeII .mixed) (k : ℕ)
    {S : Set Array} (hS : AbsConvex ℚ S) (h0 : (0 : Array) ∈ S)
    (h : ∀ b i j, colorRestrict k (e.crop b) (((e.path b).piece i).child j) ∈ S) :
    restrict (colorSet k) e.value ∈ S := by
  choose i g hg heq hact using fun b =>
    (e.path b).color_decomposition k (e.crop b) h0 (h b)
  let active : Finset (Fin e.length) := Finset.univ.filter
    (fun b => colorRestrict k (e.crop b) (e.path b).value ≠ 0)
  let j (b : Fin e.length) : ℕ := (e.path b).raw.weight (i b)
  let c (b : Fin e.length) : ℚ :=
    if b ∈ active then e.coefficient b / (Family.mixed.m (j b) : ℚ) else 0
  have jpos : ∀ b, 1 ≤ j b := fun b => (e.path b).valid.weight_pos _ (i b).isLt
  have jinj : Set.InjOn (fun b => j b - 1) active := by
    intro b hb d hd hbd
    by_contra hne
    have hb' := hact b (Finset.mem_filter.mp hb).2
    have hd' := hact d (Finset.mem_filter.mp hd).2
    have hsame : j b = j d := by
      change j b - 1 = j d - 1 at hbd
      have := jpos b
      have := jpos d
      omega
    change j b ∈ _ at hb'
    rw [hsame] at hb'
    exact Finset.disjoint_left.mp (e.disjoint_active hne) hb' hd'
  have hcR : ∑ b, |(c b : ℝ)| ≤
      ∑ b ∈ active, 1 / (Parameters.m Family.mixed.s (j b-1) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ active
    · have hm : 0 < (Family.mixed.m (j b) : ℝ) := by exact_mod_cast Family.mixed.m_pos _
      simp only [c, ite_eq_left hb, Rat.cast_div, Rat.cast_natCast, abs_div, abs_of_pos hm]
      have hb' : colorRestrict k (e.crop b) (e.path b).value ≠ 0 := (Finset.mem_filter.mp hb).2
      simp only [ite_eq_left hb']
      exact div_le_div_of_nonneg_right (e.coefficient_le_one b) hm.le
    · have hb' : ¬ colorRestrict k (e.crop b) (e.path b).value ≠ 0 := by
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hb
      simp [c, hb, hb']
  have hcsR : ∑ b, |(c b : ℝ)| ≤ 1 := by
    calc
      _ ≤ ∑ b ∈ active, 1 / (Parameters.m Family.mixed.s (j b-1) : ℝ) := hcR
      _ = ∑ n ∈ active.image (fun b => j b-1), 1 / (Parameters.m Family.mixed.s n : ℝ) := by
        rw [Finset.sum_image]
        exact fun b hb d hd hbd => jinj hb hd hbd
      _ ≤ ∑' n, 1 / (Parameters.m Family.mixed.s n : ℝ) :=
        Family.mixed.reciprocal_summable.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ 1 := (Parameters.reciprocal_sum_small Family.mixed.s_ge_two).le.trans (by norm_num)
  have hcs : ∑ b, |c b| ≤ 1 := by exact_mod_cast hcsR
  have hv : restrict (colorSet k) e.value = ∑ b, c b • g b := by
    simp only [TypeII.value, restrict_sum, restrict_smul]
    apply Finset.sum_congr rfl
    intro b _
    change e.coefficient b • colorRestrict k (e.crop b) (e.path b).value = _
    by_cases hb : b ∈ active
    · rw [heq b, smul_smul]
      simp only [c, ite_eq_left hb, j, div_eq_mul_inv, one_mul]
    · have hz : colorRestrict k (e.crop b) (e.path b).value = 0 := by
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hb
      simp [c, hb, hz]
  rw [hv]
  exact absConvex_sum_le_one hS h0 c g hcs hg

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.all : Crop := ⟨Set.univ, Set.ordConnected_univ, Set.univ, Set.ordConnected_univ⟩

@[simp] lemma Crop.all_set (f : Family) : Crop.all.set f = Set.univ := by
  cases f <;> simp [Crop.all, Crop.set]

@[simp] lemma restrict_univ (x : Array) : restrict Set.univ x = x := by
  ext a
  simp

@[simp] lemma colorRestrict_all (k : ℕ) (x : Array) :
    colorRestrict k Crop.all x = restrict (colorSet k) x := by
  simp [colorRestrict]

lemma pure_color_restrict (k l : ℕ) (x : Array) (hx : x ∈ Pure l) :
    restrict (colorSet k) x = if k = l then x else 0 := by
  ext a
  by_cases hkl : k = l
  · subst l
    by_cases ha : Colors.color a = k
    · simp [colorSet, ha]
    · simp [colorSet, ha, pure_vanish k x hx a ha]
  · by_cases ha : Colors.color a = k
    · have hl : Colors.color a ≠ l := by omega
      simp [colorSet, hkl, ha, pure_vanish l x hx a hl]
    · simp [colorSet, hkl, ha]

lemma mixedBase_crop (A : Crop) (x : Array) (hx : x ∈ ⋃ k, Pure k) :
    restrict (A.set .mixed) x ∈ ⋃ k, Pure k := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  rw [pure_mixed_crop k A x hk]
  split_ifs
  · exact pure_crop k A x hk
  · exact pure_zero k

lemma mixed_stage_crop (n : ℕ) (A : Crop) (x : Array)
    (hx : x ∈ stage (⋃ k, Pure k) .mixed n) :
    restrict (A.set .mixed) x ∈ stage (⋃ k, Pure k) .mixed n :=
  stage_crop .mixed (Set.mem_iUnion.mpr ⟨0, pure_zero 0⟩) mixedBase_crop n A x hx

lemma mixed_stage_color_hull (k : ℕ) :
    ∀ n x, x ∈ stage (⋃ l, Pure l) .mixed n →
      restrict (colorSet k) x ∈ absConvexHull ℚ (Pure k) := by
  have h0 : (0 : Array) ∈ absConvexHull ℚ (Pure k) := subset_absConvexHull (pure_zero k)
  intro n
  induction n with
  | zero =>
    intro x hx
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
    rw [pure_color_restrict k l x hl]
    split_ifs with hkl
    · subst l
      exact subset_absConvexHull hl
    · exact h0
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · obtain ⟨g, hg, hv⟩ := e.color_decomposition k Crop.all h0 (fun i => by
        simpa only [colorRestrict_all] using ih _ (he i))
      rw [colorRestrict_all] at hv
      rw [hv]
      apply (absConvex_absConvexHull (𝕜 := ℚ) (s := Pure k)).1.smul_mem ?_ hg
      rw [norm_div, norm_one]
      have hm : (1 : ℝ) ≤ Family.mixed.m e.weight := by exact_mod_cast Family.mixed.m_pos _
      simpa only [← Rat.norm_cast_real, Rat.cast_natCast, Real.norm_natCast, one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hm)
    · apply e.color_mem k absConvex_absConvexHull h0
      intro b i j
      exact ih _ (mixed_stage_crop n (e.crop b) _ (he b i j))

/-- Every mixed-stage normer restricts to the absolute convex hull of the pure norming set. -/
lemma full_color_hull (k : ℕ) (x : Array) (hx : x ∈ Full) :
    restrict (colorSet k) x ∈ absConvexHull ℚ (Pure k) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact mixed_stage_color_hull k n x hn

end SeparableQuotient.Norming

namespace SeparableQuotient.LpFinite
open scoped Classical ENNReal
universe u
variable {Γ : Type u} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma absConvex_norm_array : AbsConvex ℚ {f : Γ →₀ ℚ | ‖array p f‖ ≤ 1} := by
  constructor
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    change ‖array p (a • x)‖ ≤ 1
    rw [array_smul, norm_smul, Rat.norm_cast_real]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg a)).trans (by simpa using ha)
  · intro x hx y hy a b ha hb hab
    change ‖array p (a • x + b • y)‖ ≤ 1
    simp only [array_add, array_smul]
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
    calc
      _ ≤ ‖(a : ℝ) • array p x‖ + ‖(b : ℝ) • array p y‖ := norm_add_le _ _
      _ = (a : ℝ) * ‖array p x‖ + (b : ℝ) * ‖array p y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha', Real.norm_of_nonneg hb']
      _ ≤ (a : ℝ) * 1 + (b : ℝ) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hx ha') (mul_le_mul_of_nonneg_left hy hb')
      _ = 1 := by simpa using hab'

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal Classical
open LpFinite

/-- Full mixed normers retain the exact pure ℓr bound on each color. -/
lemma full_color_lp_bound (k : ℕ) (f : Array) (hf : f ∈ Full) :
    ‖array (Family.pure k).exponent (restrict (colorSet k) f)‖ ≤ 1 :=
  absConvexHull_min (fun x hx => pure_lp_bound k x hx) absConvex_norm_array
    (full_color_hull k f hf)

end SeparableQuotient.Norming

namespace SeparableQuotient.LpFinite
open scoped Classical ENNReal
universe u
variable {Γ : Type u}

/-- Real finitely supported vectors in the usual ℓp space. -/
def realArray (p : ℝ≥0∞) (x : Γ →₀ ℝ) : lp (fun _ : Γ => ℝ) p :=
  ⟨fun a => x a, Memℓp.of_exponent_ge (memℓp_zero_iff.mpr x.hasFiniteSupport) (zero_le : 0 ≤ p)⟩

@[simp] lemma realArray_apply (p : ℝ≥0∞) (x : Γ →₀ ℝ) (a : Γ) :
    realArray p x a = x a := rfl

lemma pairing_le {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (x : Γ →₀ ℝ) (f : Γ →₀ ℚ) :
    |x.sum (fun a t => t * (f a : ℝ))| ≤ ‖realArray p x‖ * ‖array q f‖ := by
  have h := lp.tsum_mul_le_mul_norm hpq (realArray p x) (array q f)
  calc
    _ ≤ ∑ a ∈ x.support, |x a * (f a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ x.support, ‖realArray p x a‖ * ‖array q f a‖ := by
      simp only [realArray_apply, array_apply, Real.norm_eq_abs, abs_mul]
    _ ≤ ∑' a, ‖realArray p x a‖ * ‖array q f a‖ :=
      h.1.sum_le_tsum _ (fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := h.2

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.primalExponent (f : Family) : ℝ≥0∞ := f.s
instance Family.primalExponent_fact (f : Family) : Fact (1 ≤ f.primalExponent) :=
  ⟨by change (1 : ℝ≥0∞) ≤ (f.s : ℝ≥0∞); exact_mod_cast (f.s_ge_two.trans' (by omega : 1 ≤ 2))⟩
@[simp] lemma Family.primalExponent_toReal (f : Family) : f.primalExponent.toReal = f.s := by
  simp [Family.primalExponent]
lemma Family.conjugate (f : Family) :
    f.primalExponent.toReal.HolderConjugate f.exponent.toReal := by
  simpa only [Family.primalExponent_toReal, Family.exponent_toReal, Family.r] using
    Parameters.s_r_conjugate f.s_ge_two
end SeparableQuotient.Norming

end

end OAI
