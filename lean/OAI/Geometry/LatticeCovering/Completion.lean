import OAI.Geometry.LatticeCovering.Shears

namespace OAI

section
section

namespace SingleLatticeCovering.Completion
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

lemma projection_mem_image_iff {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →+ Torus n)
    (hker : ∀ x, π x = 0 ↔ x ∈ Γ) (K : Set (RealSpace n)) (x : RealSpace n) :
    π x ∈ π '' K ↔ x ∈ K+(Γ : Set (RealSpace n)) := by
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,ha,x-a,?_,by abel_nf⟩
    apply (hker _).mp
    simp [map_sub,hax]
  · rintro ⟨a,ha,z,hz,rfl⟩
    refine ⟨a,ha,?_⟩
    simp [map_add,(hker z).mpr hz]

lemma projection_image_eq_univ {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →+ Torus n)
    (hsurj : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) : π '' K = univ ↔ K+(Γ : Set (RealSpace n)) = univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    apply (projection_mem_image_iff Γ π hker K x).mp
    rw [h]; trivial
  · intro h
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨x,rfl⟩ := hsurj t
    apply (projection_mem_image_iff Γ π hker K x).mpr
    rw [h]; trivial

lemma projection_scalar_image {n : ℕ} (π : RealSpace n →+ Torus n)
    (K : Set (RealSpace n)) (k : ℕ) (hk : k ≠ 0) :
    (fun t : Torus n => k • t) '' (π '' ((k : ℝ)⁻¹ • K)) = π '' K := by
  have heq (x : RealSpace n) : k • π ((k : ℝ)⁻¹ • x) = π x := by
    rw [← map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk),one_smul]
  rw [←Set.image_smul,Set.image_image,Set.image_image]
  simp only [heq]




theorem completion_with_projection {n : ℕ}
    (Γ : Submodule ℤ (RealSpace n)) (π : RealSpace n →ₜ+ Torus n)
    (hsurj : Function.Surjective π) (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (k : ℕ) (hk : 0 < k)
    (hhole : 1-(torusMeasure n).real (π '' K) <
      (torusMeasure n).real (π '' K)/(k : ℝ)^n) :
    ((1+(k : ℝ)⁻¹) • K)+(Γ : Set (RealSpace n)) = univ := by
  let A := π '' K
  let B := π '' ((k : ℝ)⁻¹ • K)
  have hB : IsCompact B := (hK.smul _).image π.continuous
  have hm : (torusMeasure n).real A ≤ (k : ℝ)^n*(torusMeasure n).real B := by
    have h := torus_measure_image_nsmul n k hk.ne' hB
    change (torusMeasure n).real ((fun t : Torus n => k • t) ''
      (π.toAddMonoidHom '' ((k : ℝ)⁻¹ • K))) ≤ _ at h
    rw [projection_scalar_image π.toAddMonoidHom K k hk.ne'] at h
    exact h
  have hkpow : 0 < (k : ℝ)^n := pow_pos (Nat.cast_pos.mpr hk) n
  have hlow : 1-(torusMeasure n).real A < (torusMeasure n).real B := by
    have hh := (lt_div_iff₀ hkpow).mp hhole
    exact (mul_lt_mul_iff_right₀ hkpow).mp (by dsimp [A] at *; nlinarith)
  have hsum : A+B = univ := add_eq_univ_of_measure_sum (torusMeasure n) hB.measurableSet
    (by linarith)
  apply (projection_image_eq_univ Γ π.toAddMonoidHom hsurj hker _).mp
  rw [hconv.add_smul (show (0 : ℝ) ≤ 1 by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg k)),
    one_smul,Set.image_add]
  exact hsum


theorem complete_almost_cover_projection {n : ℕ} (hn : 2 ≤ n)
    (Γ : Submodule ℤ (RealSpace n)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (π : RealSpace n →ₜ+ Torus n) (hsurj : Function.Surjective π)
    (hker : ∀ x, π x = 0 ↔ x ∈ Γ)
    (K : Set (RealSpace n)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hhole : 1-(torusMeasure n).real (π '' K) ≤ 1/(n : ℝ)^(2*n)) :
    ∃ (L' : Submodule ℤ (RealSpace n)) (_ : DiscreteTopology L'),
      IsZLattice ℝ L' ∧ K+(L' : Set (RealSpace n)) = univ ∧
      (volume K).toReal / ZLattice.covolume L' ≤
        Real.exp 1*((volume K).toReal / ZLattice.covolume Γ) := by
  have hn₀ : 0 < n := by omega
  let a := 1+(n : ℝ)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let L' := contractLattice Γ a ha.ne'
  refine ⟨L',inferInstance,inferInstance,?_,?_⟩
  · apply cover_contractLattice Γ K a ha.ne'
    apply completion_with_projection Γ π hsurj hker K hK hconv n hn₀
    have h := small_hole_strict hn hhole
    simpa only [sub_sub_cancel] using h
  · have heq : (volume K).toReal / ZLattice.covolume L' =
        a^n*((volume K).toReal / ZLattice.covolume Γ) := by
      rw [contractLattice_covolume Γ a ha,inv_pow,div_mul_eq_div_div,div_inv_eq_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_exp n hn₀.ne')
      (div_nonneg ENNReal.toReal_nonneg (ZLattice.covolume_pos Γ).le)


end SingleLatticeCovering.Completion

namespace SingleLatticeCovering.Shear
open MeasureTheory
open scoped BigOperators ENNReal

lemma source_pattern_mono {α : Type*} {q : ℕ}
    {s t : Finset ((Fin q → ℝ) × α)} (hs : SourcePattern s)
    (ht : t.Nonempty) (hts : t ⊆ s) : SourcePattern t := by
  refine ⟨ht,fun l hl r hr he => hs.2.1 l (hts hl) r (hts hr) he,?_⟩
  intro j y
  obtain ⟨v,hv⟩ := hs.2.2 j y
  exact ⟨v,fun l hl hy => hv l (hts hl) hy⟩



lemma retained_load {A : Type*} (s : Finset A) (u : A → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ x ∈ s, u x) - (s.card : ℝ)*τ ≤ ∑ x ∈ s.filter (fun x => τ ≤ u x), u x := by
  classical
  have hdrop : ∑ x ∈ s.filter (fun x => ¬τ ≤ u x), u x ≤ (s.card : ℝ)*τ := by
    calc
      _ ≤ ∑ x ∈ s.filter (fun x => ¬τ ≤ u x), τ := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = ((s.filter (fun x => ¬τ ≤ u x)).card : ℝ)*τ := by simp
      _ ≤ (s.card : ℝ)*τ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le s _) hτ
  have hsum := Finset.sum_filter_add_sum_filter_not s (fun x => τ ≤ u x) u
  linarith

lemma retain_source_pattern {α : Type*} {q : ℕ}
    (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s)
    (u : α → ℝ) (τ A : ℝ) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hload : A+(2^q : ℕ)*τ ≤ ∑ l ∈ s, u l.2) :
    ∃ t : Finset ((Fin q → ℝ) × α), t ⊆ s ∧ SourcePattern t ∧
      (∀ l ∈ t, τ ≤ u l.2) ∧ A ≤ ∑ l ∈ t, u l.2 := by
  classical
  let t := s.filter (fun l => τ ≤ u l.2)
  have hc : (s.card : ℝ) ≤ (2^q : ℕ) := by exact_mod_cast source_card_le_two_pow hs
  have htload : A ≤ ∑ l ∈ t, u l.2 := by
    have hd := retained_load s (fun l => u l.2) τ hτ
    have hm := mul_le_mul_of_nonneg_right hc hτ
    change A ≤ ∑ l ∈ s.filter (fun l => τ ≤ u l.2), u l.2
    linarith
  have hn : t.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at htload
    exact (not_le_of_gt hA) htload
  refine ⟨t,Finset.filter_subset _ _,source_pattern_mono hs hn (Finset.filter_subset _ _),?_,htload⟩
  exact fun l hl => (Finset.mem_filter.mp hl).2

lemma finite_weight_load_bounds {A : Type*} (s : Finset A) (w u : A → ℝ)
    (κ ρ c C ε : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hweight : κ ≤ ∑ x ∈ s, w x)
    (hlo : ∀ x ∈ s, c*ρ*w x ≤ u x)
    (hup : ∀ x ∈ s, u x ≤ C*ρ*w x)
    (hcap : ∀ x ∈ s, w x ≤ ε) :
    c*κ*ρ ≤ ∑ x ∈ s, u x ∧ ∀ x ∈ s, u x ≤ C*ρ*ε := by
  constructor
  · have hs := Finset.sum_le_sum hlo
    rw [←Finset.mul_sum] at hs
    have hm := mul_le_mul_of_nonneg_left hweight (mul_nonneg hc hρ)
    nlinarith
  · intro x hx
    exact (hup x hx).trans (mul_le_mul_of_nonneg_left (hcap x hx) (mul_nonneg hC hρ))

lemma exponential_pattern_bound {α : Type*} {q : ℕ}
    (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s)
    (u : α → ℝ) (L A : ℝ) (hL : 1 ≤ L) (hA : A ≤ ∑ l ∈ s, u l.2) :
    ENNReal.ofReal L^(s.card-1) * (∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2))) ≤
      ENNReal.ofReal (Real.exp ((2^q : ℕ)*Real.log L-A/2)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp : (∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2))) =
      ENNReal.ofReal (Real.exp (-(∑ l ∈ s, u l.2)/2)) := by
    rw [←ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),←Real.exp_sum]
    congr 2
    rw [←Finset.sum_div,Finset.sum_neg_distrib]
  rw [hp,←ENNReal.ofReal_pow hL0.le,←ENNReal.ofReal_mul (pow_nonneg hL0.le _)]
  have hpow : L^(s.card-1)=Real.exp ((s.card-1 : ℕ)*Real.log L) := by
    rw [Real.exp_nat_mul,Real.exp_log hL0]
  rw [hpow,←Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hc : ((s.card-1 : ℕ) : ℝ) ≤ (2^q : ℕ) := by
    exact_mod_cast (Nat.sub_le s.card 1).trans (source_card_le_two_pow hs)
  have hm := mul_le_mul_of_nonneg_right hc (Real.log_nonneg hL)
  linarith


end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

noncomputable def labelPattern {α : Type*} {D : ℕ}
    (P : Finset (Fin D → ℝ)) (a : (Fin D → ℝ) → α) :
    Finset ((Fin D → ℝ) × α) := by
  classical
  exact P.image (fun l => (l,a l))

lemma mem_labelPattern {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (l : (Fin D → ℝ) × α) :
    l ∈ labelPattern P a ↔ l.1 ∈ P ∧ l.2=a l.1 := by
  classical
  simp [labelPattern,Prod.ext_iff,eq_comm]

lemma labelPattern_source {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (hP : P.Nonempty) (hPb : SuffixBinary P) :
    Shear.SourcePattern (labelPattern P a) := by
  classical
  refine ⟨Finset.Nonempty.image hP _,?_,?_⟩
  · intro l hl r hr he
    obtain ⟨_,hl⟩ := (mem_labelPattern P a l).mp hl
    obtain ⟨_,hr⟩ := (mem_labelPattern P a r).mp hr
    rw [hl,hr,he]
  · intro j y
    obtain ⟨v,hv⟩ := hPb j y
    exact ⟨v,fun l hl hy => hv l.1 ((mem_labelPattern P a l).mp hl).1 hy⟩

lemma sum_labelPattern {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (f : ((Fin D → ℝ) × α) → ℝ) :
    ∑ l ∈ labelPattern P a, f l = ∑ l ∈ P, f (l,a l) := by
  classical
  apply Finset.sum_image
  intro x hx y hy he
  exact congrArg Prod.fst he

lemma labelPattern_card {α : Type*} {D : ℕ} (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) : (labelPattern P a).card=P.card := by
  classical
  apply Finset.card_image_of_injective
  intro x y he
  exact congrArg Prod.fst he

lemma suffix_card_le {D : ℕ} (P : Finset (Fin D → ℝ)) (hPb : SuffixBinary P) :
    P.card ≤ 2^D := by
  classical
  by_cases hP : P.Nonempty
  · have hc := Shear.source_card_le_two_pow (labelPattern_source P (fun _ => ()) hP hPb)
    simpa only [labelPattern_card] using hc
  · simp [Finset.not_nonempty_iff_eq_empty.mp hP]



lemma labelPattern_mem_all {α : Type*} {D : ℕ}
    (A : ℕ → Finset ℝ) (labels : Finset α) (P : Finset (Fin D → ℝ))
    (a : (Fin D → ℝ) → α) (hP : P.Nonempty) (hPb : SuffixBinary P)
    (ha : ∀ l ∈ P, a l ∈ labels) (hA : ∀ l ∈ P, ∀ j : Fin D, l j ∈ A j.val) :
    labelPattern P a ∈ Shear.allPatterns A labels D := by
  apply (Shear.mem_allPatterns A labels D _).mpr
  refine ⟨?_,labelPattern_source P a hP hPb⟩
  intro l hl
  obtain ⟨hl,he⟩ := (mem_labelPattern P a l).mp hl
  apply (Shear.mem_alphabetPoints A labels D l).mpr
  exact ⟨hA l.1 hl,he ▸ ha l.1 hl⟩

lemma retained_mem_all {α : Type*} {D : ℕ}
    (A : ℕ → Finset ℝ) (labels : Finset α)
    (s t : Finset ((Fin D → ℝ) × α)) (hs : s ∈ Shear.allPatterns A labels D)
    (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ Shear.allPatterns A labels D := by
  obtain ⟨hsub,hsource⟩ := (Shear.mem_allPatterns A labels D s).mp hs
  exact (Shear.mem_allPatterns A labels D t).mpr
    ⟨hts.trans hsub,Shear.source_pattern_mono hsource ht hts⟩


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded
open scoped BigOperators





theorem section_labeled_retained {α : Type*} [Fintype α] {m D : ℕ}
    (P : Finset (Fin D → ℝ)) (hP : P.Nonempty) (hPb : SuffixBinary P)
    (N : Submodule ℤ (Fin D → ℝ)) (hraw : ∀ l ∈ P, l ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (y : Fin D → ℝ)
    (K : Set (Fin (m+D) → ℝ)) (J : α → Set (Fin m → ℝ))
    (u : α → ℝ) (w : (Fin D → ℝ) → ℝ) (κ ρ c C ε τ A : ℝ)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hweight : κ ≤ ∑ l ∈ P, w l) (hcap : ∀ l ∈ P, w l ≤ ε)
    (hsection : ∀ l ∈ P, ∃ a : α,
      (∀ j ∈ J a, Fin.append j (y-M l) ∈ K) ∧ c*ρ*w l ≤ u a ∧ u a ≤ C*ρ*w l)
    (hload : A+(2^D : ℕ)*τ ≤ c*κ*ρ)
    (alphabet : ℕ → Finset ℝ) (halph : ∀ l ∈ P, ∀ j : Fin D, l j ∈ alphabet j.val) :
    ∃ s : Finset ((Fin D → ℝ) × α),
      s ∈ Shear.allPatterns alphabet (Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ C*ρ*ε)) D ∧
      (∀ l ∈ s, l.1 ∈ N) ∧
      (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) ∧
      A ≤ ∑ l ∈ s, u l.2 := by
  classical
  obtain ⟨l₀,hl₀⟩ := hP
  obtain ⟨a₀,ha₀⟩ := hsection l₀ hl₀
  have hex : ∀ l : Fin D → ℝ, ∃ a : α, l ∈ P →
      (∀ j ∈ J a, Fin.append j (y-M l) ∈ K) ∧ c*ρ*w l ≤ u a ∧ u a ≤ C*ρ*w l := by
    intro l
    by_cases hl : l ∈ P
    · obtain ⟨a,ha⟩ := hsection l hl
      exact ⟨a,fun _ => ha⟩
    · exact ⟨a₀,fun h => (hl h).elim⟩
  choose a ha using hex
  have hbnds := Shear.finite_weight_load_bounds P w (fun l => u (a l)) κ ρ c C ε hρ hc hC
    hweight (fun l hl => (ha l hl).2.1) (fun l hl => (ha l hl).2.2) hcap
  let s₀ := labelPattern P a
  have hs₀ : Shear.SourcePattern s₀ := labelPattern_source P a ⟨l₀,hl₀⟩ hPb
  have hload₀ : A+(2^D : ℕ)*τ ≤ ∑ l ∈ s₀, u l.2 := by
    rw [sum_labelPattern]
    exact hload.trans hbnds.1
  obtain ⟨s,hsub,hsource,hthreshold,hsum⟩ :=
    Shear.retain_source_pattern s₀ hs₀ u τ A hτ hA hload₀
  refine ⟨s,?_,?_,?_,hsum⟩
  · apply (Shear.mem_allPatterns _ _ _ _).mpr
    refine ⟨?_,hsource⟩
    intro l hl
    have hmem := hsub hl
    obtain ⟨hlP,hlA⟩ := (mem_labelPattern P a l).mp hmem
    apply (Shear.mem_alphabetPoints _ _ _ _).mpr
    refine ⟨halph l.1 hlP,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hthreshold l hl,?_⟩⟩
    rw [hlA]
    exact hbnds.2 l.1 hlP
  · intro l hl
    exact hraw l.1 ((mem_labelPattern P a l).mp (hsub hl)).1
  · intro l hl
    obtain ⟨hlP,hlA⟩ := (mem_labelPattern P a l).mp (hsub hl)
    rw [hlA]
    exact (ha l.1 hlP).1


end SingleLatticeCovering.Vertical

noncomputable section
namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion
open scoped BigOperators Pointwise ENNReal



def columnMap {m D : ℕ} (Z : Fin D → (Fin m → ℝ)) :
    (Fin D → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun l := ∑ j, l j • Z j
  map_add' l r := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a l := by simp [Finset.smul_sum,smul_smul]

@[simp] lemma columnMap_apply {m D : ℕ} (Z : Fin D → (Fin m → ℝ)) (l : Fin D → ℝ) :
    columnMap Z l = Shear.Pattern.linearShift Z l := rfl

abbrev joinedLattice {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) : Submodule ℤ (Fin (m+D) → ℝ) :=
  image (finProduct L N) (triangular (LinearEquiv.refl ℝ _) M (columnMap Z))

lemma joined_point_mem {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) {h : Fin m → ℝ} {l : Fin D → ℝ}
    (hh : h ∈ L) (hl : l ∈ N) :
    Fin.append (h+columnMap Z l) (M l) ∈ joinedLattice L N M Z := by
  apply (mem_image _ _ _).mpr
  refine ⟨Fin.append h l,?_,?_⟩
  · simpa only [mem_finProduct,Fin.append_left,Fin.append_right] using ⟨hh,hl⟩
  · exact triangular_append _ _ _ h l

lemma joined_covolume {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    ZLattice.covolume (joinedLattice L N M Z) =
      ZLattice.covolume L * ZLattice.covolume (image N M) := by
  rw [joinedLattice,triangular_lattice_covolume,image_covolume]
  simp


def horizontalHole {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+D) → ℝ)) (Γ : Submodule ℤ (Fin (m+D) → ℝ))
    (y : Fin D → ℝ) : Set (Torus m) :=
  latticeProjection L '' {x | Fin.append x y ∉ K+(Γ : Set (Fin (m+D) → ℝ))}



lemma covered_of_section {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (x : Fin m → ℝ) (y l : Fin D → ℝ) (hl : l ∈ N)
    (J : Set (Fin m → ℝ)) (hJ : ∀ j ∈ J, Fin.append j (y-M l) ∈ K)
    (hx : latticeProjection L (x-columnMap Z l) ∈ latticeProjection L '' J) :
    Fin.append x y ∈ K+(joinedLattice L N M Z : Set (Fin (m+D) → ℝ)) := by
  obtain ⟨j,hj,hjx⟩ := hx
  let h := x-columnMap Z l-j
  have hh : h ∈ L := by
    apply (latticeProjection_eq_zero_iff L h).mp
    dsimp [h]
    rw [map_sub]
    simpa only [columnMap_apply] using sub_eq_zero.mpr hjx.symm
  refine ⟨Fin.append j (y-M l),hJ j hj,Fin.append (h+columnMap Z l) (M l),
    joined_point_mem L N M Z hh hl,?_⟩
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro k <;>
    simp only [Pi.add_apply,Fin.append_left,Fin.append_right,Pi.sub_apply,h] <;> ring

lemma horizontal_hole_subset {α : Type*} {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (J : α → Set (Fin m → ℝ)) (y : Fin D → ℝ)
    (s : Finset ((Fin D → ℝ) × α))
    (hraw : ∀ l ∈ s, l.1 ∈ N)
    (hsection : ∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) :
    horizontalHole L K (joinedLattice L N M Z) y ⊆
      ⋂ l ∈ s, Shear.translate ((latticeProjection L '' J l.2)ᶜ)
        (latticeProjection L (Shear.Pattern.linearShift Z l.1)) := by
  rintro t ⟨x,hx,rfl⟩
  simp only [Set.mem_iInter]
  intro l hl
  change latticeProjection L x-latticeProjection L (columnMap Z l.1) ∉ latticeProjection L '' J l.2
  rw [←map_sub]
  intro hc
  exact hx (covered_of_section L N M Z K x y l.1 (hraw l hl) (J l.2) (hsection l hl) hc)



end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion Shear
open scoped BigOperators Pointwise ENNReal

instance torusMeasure_neg (n : ℕ) : (torusMeasure n).IsNegInvariant :=
  inferInstanceAs ((Measure.addHaarMeasure ⊤ : Measure (Torus n)).IsNegInvariant)




theorem finite_family_lattice_shear {α : Type*} [Fintype α] {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (J : α → Set (Fin m → ℝ))
    (hJ : ∀ a, IsCompact (J a)) (u : α → ℝ) (labels : Finset α)
    (hhole : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)))
    (alphabet : ℕ → Finset ℝ) (Lstar : ℝ) (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (D+1),
      (allPatterns alphabet labels q).card : ℕ) : ℝ) < Lstar) :
    ∃ Z : Fin D → (Fin m → ℝ), ∀ (y : Fin D → ℝ)
      (s : Finset ((Fin D → ℝ) × α)), s ∈ allPatterns alphabet labels D →
      (∀ l ∈ s, l.1 ∈ N) →
      (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (y-M l.1) ∈ K) →
      ∀ A : ℝ, A ≤ ∑ l ∈ s, u l.2 →
        torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤
          ENNReal.ofReal (Real.exp ((2^D : ℕ)*Real.log Lstar-A/2)) := by
  classical
  let U : α → Set (Torus m) := fun a => (latticeProjection L '' J a)ᶜ
  have hU : ∀ a, MeasurableSet (U a) := fun a =>
    ((hJ a).image (latticeProjection L).continuous).isClosed.measurableSet.compl
  let η : α → ℝ≥0∞ := fun a => if a ∈ labels then ENNReal.ofReal (Real.exp (-u a/2)) else 1
  have hη0 : ∀ a, η a ≠ 0 := by
    intro a; dsimp [η]; split
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    · exact one_ne_zero
  have hηt : ∀ a, η a ≠ ∞ := by
    intro a; dsimp [η]; split <;> simp
  have hUη : ∀ a, torusMeasure m (U a) ≤ η a := by
    intro a; dsimp [η]; split
    · exact hhole a (by assumption)
    · exact prob_le_one
  have hL0 : 0 < Lstar := lt_of_lt_of_le zero_lt_one hLstar
  have hQ : (∑ q ∈ Finset.range (D+1),
      ((allPatterns alphabet labels q).card : ℝ≥0∞)) < ENNReal.ofReal Lstar := by
    rw [←Nat.cast_sum]
    exact ENNReal.natCast_lt_ofReal.mpr hcost
  obtain ⟨Z,hZ⟩ := source_simultaneous_shear (torusMeasure m)
    (latticeProjection L).toAddMonoidHom (latticeProjection_surjective L) U hU
    η hη0 hηt hUη
    (ENNReal.ofReal Lstar) (ENNReal.ofReal_pos.mpr hL0).ne' ENNReal.ofReal_ne_top D
    (allPatterns alphabet labels)
    (fun q _ s hs => ((mem_allPatterns alphabet labels q s).mp hs).2)
    (allPatterns_sliceClosed alphabet labels D) hQ
  refine ⟨Z,fun y s hs hraw hsection A hload => ?_⟩
  have hmain := hZ D le_rfl s hs
  simp only [restrictColumns_self] at hmain
  have hp : (∏ l ∈ s, η l.2) = ∏ l ∈ s, ENNReal.ofReal (Real.exp (-u l.2/2)) := by
    apply Finset.prod_congr rfl
    intro l hl
    have hm := ((mem_allPatterns alphabet labels D s).mp hs).1 hl
    have ha := ((mem_alphabetPoints alphabet labels D l).mp hm).2
    simp only [η,ite_eq_left ha]
  rw [hp] at hmain
  apply le_trans (measure_mono (horizontal_hole_subset L N M Z K J y s hraw hsection))
  apply hmain.trans
  exact exponential_pattern_bound s ((mem_allPatterns alphabet labels D s).mp hs).2
    u Lstar A hLstar hload


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal

lemma add_lattice_cover_iff {E : Type*} [AddCommGroup E] [Module ℤ E]
    (Γ : Submodule ℤ E) (K : Set E) (x z : E) (hz : z ∈ Γ) :
    x+z ∈ K+(Γ : Set E) ↔ x ∈ K+(Γ : Set E) := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    change a+b = x+z at hab
    refine ⟨a,ha,b-z,Γ.sub_mem hb hz,?_⟩
    calc a+(b-z) = (a+b)-z := by abel
         _ = x := by rw [hab]; abel
  · rintro ⟨a,ha,b,hb,hab⟩
    refine ⟨a,ha,b+z,Γ.add_mem hb hz,?_⟩
    change a+b=x at hab
    change a+(b+z)=x+z
    rw [←add_assoc,hab]

lemma horizontalHole_reduce {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) (K : Set (Fin (m+D) → ℝ))
    (y₀ k : Fin D → ℝ) (hk : k ∈ N) :
    horizontalHole L K (joinedLattice L N M Z) (y₀+M k) ⊆
      Shear.translate (horizontalHole L K (joinedLattice L N M Z) y₀)
        (latticeProjection L (columnMap Z k)) := by
  rintro t ⟨x,hx,rfl⟩
  change latticeProjection L x-latticeProjection L (columnMap Z k) ∈
    horizontalHole L K (joinedLattice L N M Z) y₀
  rw [←map_sub]
  refine ⟨x-columnMap Z k,?_,rfl⟩
  intro hc
  have hg : Fin.append (columnMap Z k) (M k) ∈ joinedLattice L N M Z := by
    simpa only [zero_add] using joined_point_mem L N M Z L.zero_mem hk
  have h := (add_lattice_cover_iff (joinedLattice L N M Z) K
    (Fin.append (x-columnMap Z k) y₀) (Fin.append (columnMap Z k) (M k)) hg).mpr hc
  apply hx
  convert h using 1
  ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [Pi.add_apply,Pi.sub_apply,Fin.append_left,Fin.append_right] ; abel



theorem all_height_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ))
    (hints : ∀ k : Fin D → ℤ, (fun j => (k j : ℝ)) ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (ε : ℝ≥0∞)
    (hcell : ∀ z : Fin D → ℝ, (∀ j, 0 ≤ z j ∧ z j < 1) →
      torusMeasure m (horizontalHole L K (joinedLattice L N M Z) (M z)) ≤ ε) :
    ∀ y : Fin D → ℝ, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ε := by
  intro y
  let z := M.symm y
  let k : Fin D → ℝ := fun j => (⌊z j⌋ : ℤ)
  let z₀ : Fin D → ℝ := fun j => Int.fract (z j)
  have hk : k ∈ N := hints (fun j => ⌊z j⌋)
  have hy : y = M z₀+M k := by
    rw [←map_add]
    have hz : z₀+k = z := by
      ext j
      exact Int.fract_add_floor (z j)
    rw [hz]
    exact (M.apply_symm_apply y).symm
  rw [hy]
  apply le_trans (measure_mono (horizontalHole_reduce L N M Z K (M z₀) k hk))
  simp only [Shear.translate,sub_eq_add_neg,measure_preimage_add_right]
  exact hcell z₀ (fun j => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal


def appendTorus (m D : ℕ) : (Torus m × Torus D) →ₜ+ Torus (m+D) where
  toFun t := Fin.append t.1 t.2
  map_zero' := by ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  map_add' x y := by ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Fin.append_left]
      fun_prop
    · simp only [Fin.append_right]
      fun_prop

lemma appendTorus_surjective (m D : ℕ) : Function.Surjective (appendTorus m D) :=
  (Fin.appendEquiv m D).surjective

lemma appendTorus_measurePreserving (m D : ℕ) :
    MeasurePreserving (appendTorus m D) ((torusMeasure m).prod (torusMeasure D))
      (torusMeasure (m+D)) :=
  by
    let : Measure.IsAddHaarMeasure ((torusMeasure m).prod (torusMeasure D)) :=
      Measure.prod.instIsAddHaarMeasure (torusMeasure m) (torusMeasure D)
    exact AddMonoidHom.measurePreserving (appendTorus m D).continuous (appendTorus_surjective m D)
      (by simp)


def productProjection {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (N : Submodule ℤ (Fin D → ℝ))
    [DiscreteTopology N] [IsZLattice ℝ N] : (Fin (m+D) → ℝ) →ₜ+ Torus (m+D) where
  toFun x := Fin.append (latticeProjection L (fun j => x (Fin.castAdd D j)))
    (latticeProjection N (fun j => x (Fin.natAdd m j)))
  map_zero' := by
    change Fin.append (latticeProjection L 0) (latticeProjection N 0) = 0
    rw [map_zero,map_zero]
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  map_add' x y := by
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Pi.add_apply,Fin.append_left]
      change latticeProjection L ((fun j => x (Fin.castAdd D j))+
        (fun j => y (Fin.castAdd D j))) k = _
      simp
    · simp only [Pi.add_apply,Fin.append_right]
      change latticeProjection N ((fun j => x (Fin.natAdd m j))+
        (fun j => y (Fin.natAdd m j))) k = _
      simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Fin.append_left]
      exact (continuous_apply k).comp ((latticeProjection L).continuous.comp
        (continuous_pi (fun j => continuous_apply _)))
    · simp only [Fin.append_right]
      exact (continuous_apply k).comp ((latticeProjection N).continuous.comp
        (continuous_pi (fun j => continuous_apply _)))

@[simp] lemma productProjection_apply {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin (m+D) → ℝ) : productProjection L N x =
      Fin.append (latticeProjection L (fun j => x (Fin.castAdd D j)))
        (latticeProjection N (fun j => x (Fin.natAdd m j))) := rfl

@[simp] lemma productProjection_append {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin m → ℝ) (z : Fin D → ℝ) :
    productProjection L N (Fin.append x z) =
      Fin.append (latticeProjection L x) (latticeProjection N z) := by
  simp only [productProjection_apply,Fin.append_left,Fin.append_right]

lemma productProjection_surjective {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N] :
    Function.Surjective (productProjection L N) := by
  intro t
  obtain ⟨x,hx⟩ := latticeProjection_surjective L (fun j => t (Fin.castAdd D j))
  obtain ⟨z,hz⟩ := latticeProjection_surjective N (fun j => t (Fin.natAdd m j))
  refine ⟨Fin.append x z,?_⟩
  rw [productProjection_append,hx,hz]
  exact (Fin.appendEquiv m D).apply_symm_apply t

lemma productProjection_eq_zero_iff {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin (m+D) → ℝ) : productProjection L N x = 0 ↔ x ∈ finProduct L N := by
  rw [mem_finProduct,←latticeProjection_eq_zero_iff L,←latticeProjection_eq_zero_iff N]
  constructor
  · intro h
    constructor
    · ext j; simpa only [productProjection_apply,Fin.append_left,Pi.zero_apply] using congr_fun h (Fin.castAdd D j)
    · ext j; simpa only [productProjection_apply,Fin.append_right,Pi.zero_apply] using congr_fun h (Fin.natAdd m j)
  · rintro ⟨hL,hN⟩
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k
    · simpa only [productProjection_apply,Pi.zero_apply,Fin.append_left] using congr_fun hL k
    · simpa only [productProjection_apply,Pi.zero_apply,Fin.append_right] using congr_fun hN k


def joinedProjection {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    (Fin (m+D) → ℝ) →ₜ+ Torus (m+D) :=
  (productProjection L N).comp
    ((triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm.toContinuousLinearEquiv :
      (Fin (m+D) → ℝ) →ₜ+ (Fin (m+D) → ℝ))

lemma joinedProjection_surjective {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    Function.Surjective (joinedProjection L N M Z) :=
  (productProjection_surjective L N).comp (triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm.surjective

lemma joinedProjection_eq_zero_iff {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (x : Fin (m+D) → ℝ) : joinedProjection L N M Z x = 0 ↔ x ∈ joinedLattice L N M Z :=
  productProjection_eq_zero_iff L N _

@[simp] lemma joinedProjection_append {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (x : Fin m → ℝ) (z : Fin D → ℝ) :
    joinedProjection L N M Z (Fin.append x (M z)) =
      Fin.append (latticeProjection L (x-columnMap Z z)) (latticeProjection N z) := by
  change productProjection L N
    ((triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm (Fin.append x (M z))) = _
  simp only [triangular,LinearEquiv.coe_symm_mk,Fin.append_left,Fin.append_right,
    LinearEquiv.symm_apply_apply,LinearEquiv.refl_symm,LinearEquiv.refl_apply]
  exact productProjection_append L N _ _


end SingleLatticeCovering.CoverGeometry


end
end
end

end OAI
