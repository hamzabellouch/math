import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.SurfaceSquare

namespace OAI

/-! Indexed Transfer. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
open Filter
open scoped ENNReal

section SectionGrowth
variable (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]

theorem exponent_le_kappaSigma {n k : ℕ} {D A : WeilDivisor X.scheme}
    (hk : k ≤ n) (hA : IsAmpleDivisor A)
    (hpos : 0 < divisorSectionLimsup X D A k) :
    (k : WithBot ℕ) ≤ kappaSigma X n D := by
  classical
  exact Finset.le_sup (f := fun j : ℕ => (j : WithBot ℕ))
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), A, hA, hpos⟩)

theorem divisorSectionLimsup_eq_zero_of_kappaSigma_eq_one
    {n k : ℕ} {D A : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ))
    (hk : 2 ≤ k) (hkn : k ≤ n) (hA : IsAmpleDivisor A) :
    divisorSectionLimsup X D A k = 0 := by
  by_contra hne
  have hpos : 0 < divisorSectionLimsup X D A k := pos_iff_ne_zero.mpr hne
  have hle := exponent_le_kappaSigma X hkn hA hpos
  rw [hsigma] at hle
  have hle' : k ≤ 1 := by exact_mod_cast hle
  omega

end SectionGrowth

theorem le_limsup_of_eventually_le_on_multiples
    (a : ℕ → ℝ≥0∞) {r : ℕ} (hr : 0 < r) {c : ℝ≥0∞}
    (h : ∀ᶠ m in atTop, c ≤ a (r * m)) :
    c ≤ limsup a atTop := by
  have ht : Tendsto (fun m : ℕ => r * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hr) tendsto_id
  exact (le_limsup_of_frequently_le h.frequently).trans ht.limsup_comp_le_limsup

theorem positive_limsup_of_quadratic_growth_on_multiples
    (a : ℕ → ℝ≥0∞) {r : ℕ} (hr : 0 < r) {c : ℝ≥0∞} (hc : 0 < c)
    (h : ∀ᶠ m in atTop, c * (r * m : ℕ) ^ 2 ≤ a (r * m)) :
    0 < limsup (fun m : ℕ => a m / (m : ℝ≥0∞) ^ 2) atTop := by
  apply hc.trans_le
  apply le_limsup_of_eventually_le_on_multiples _ hr
  filter_upwards [h, eventually_gt_atTop 0] with m hm hmpos
  have hn : (r * m : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hr hmpos)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hn))
    (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))).2
  exact hm

section SectionGrowth
variable (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]

theorem no_quadratic_growth_on_multiples_of_kappaSigma_eq_one
    {n : ℕ} {D A : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ)) (hn : 2 ≤ n)
    (hA : IsAmpleDivisor A) {r : ℕ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : 0 < c) :
    ¬ ∀ᶠ m in atTop,
      c * (r * m : ℕ) ^ 2 ≤ sectionDimension X ((r * m) • D + A) := by
  intro hgrowth
  have hp := positive_limsup_of_quadratic_growth_on_multiples
    (fun m => sectionDimension X (m • D + A)) hr hc hgrowth
  change 0 < divisorSectionLimsup X D A 2 at hp
  rw [divisorSectionLimsup_eq_zero_of_kappaSigma_eq_one X hsigma (by decide) hn hA] at hp
  exact (lt_irrefl _ hp)

theorem sectionDimension_le_of_injective
    (Y : ComplexProjectiveVariety) [StalkwiseNormal Y.scheme]
    (D : WeilDivisor X.scheme) (E : WeilDivisor Y.scheme) :
    letI := schemeFieldAlgebra (.of ℂ) X.structureMap
    letI := schemeFieldAlgebra (.of ℂ) Y.structureMap
    ∀ F : divisorSectionsOver (.of ℂ) X.structureMap D →ₗ[ℂ]
        divisorSectionsOver (.of ℂ) Y.structureMap E,
      Function.Injective F → sectionDimension X D ≤ sectionDimension Y E := by
  dsimp only
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  intro F hF
  exact ENat.toENNReal_mono (Cardinal.toENat.monotone' (F.rank_le_of_injective hF))

theorem sectionDimension_le_of_nonzero_section
    {D E : WeilDivisor X.scheme} {s : X.scheme.functionField}
    (hs : s ≠ 0) (hsec : IsDivisorSection (E - D) s) :
    sectionDimension X D ≤ sectionDimension X E := by
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let F : divisorSectionsOver (.of ℂ) X.structureMap D →ₗ[ℂ]
      divisorSectionsOver (.of ℂ) X.structureMap E := {
    toFun := fun f => ⟨f.1 * s, by
      have hf := divisorSection_mul f.2 hsec
      change IsDivisorSection E _
      have hDE : D + (E - D) = E := by abel
      simpa only [hDE] using hf⟩
    map_add' := fun f g => Subtype.ext (add_mul _ _ _)
    map_smul' := by
      intro a f
      apply Subtype.ext
      change (a • f.1) * s = a • (f.1 * s)
      exact smul_mul_assoc a f.1 s }
  exact sectionDimension_le_of_injective X X D E F (fun f g h =>
    Subtype.ext (mul_right_cancel₀ hs (congrArg Subtype.val h)))

theorem exists_fixed_ample_twist_sectionDimension_le
    (D P : WeilDivisor X.scheme) :
    ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧
      ∀ m : ℕ, sectionDimension X (m • D + P) ≤ sectionDimension X (m • D + A) := by
  obtain ⟨B, hB⟩ := exists_ampleDivisor_of_projective X
  obtain ⟨A, hA, s, hs, hsec⟩ := exists_ample_twist_dominating B P hB
  refine ⟨A, hA, fun m => sectionDimension_le_of_nonzero_section X hs ?_⟩
  simpa only [add_sub_add_left_eq_sub] using hsec

theorem no_quadratic_growth_with_fixed_twist
    {n : ℕ} {D : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ)) (hn : 2 ≤ n)
    (P : WeilDivisor X.scheme) {r : ℕ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : 0 < c) :
    ¬ ∀ᶠ m in atTop,
      c * (r * m : ℕ) ^ 2 ≤ sectionDimension X ((r * m) • D + P) := by
  obtain ⟨A, hA, hAP⟩ := exists_fixed_ample_twist_sectionDimension_le X D P
  intro hgrowth
  apply no_quadratic_growth_on_multiples_of_kappaSigma_eq_one X hsigma hn hA hr hc
  filter_upwards [hgrowth] with m hm
  exact hm.trans (hAP (r * m))

end SectionGrowth
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Filter
open scoped ENNReal

section WeilPushforward
variable {W X : Scheme} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X]
    (u : W ⟶ X) [IsProper u] (hu : IsBirationalMorphism u)

noncomputable def birationalPrimeLift (p : PrimeDivisor X) : PrimeDivisor W :=
  Classical.choose (exists_unique_prime_over_of_proper_birational u hu p)

lemma birationalPrimeLift_spec (p : PrimeDivisor X) :
    u (birationalPrimeLift u hu p).1 = p.1 ∧
      IsIso (u.stalkMap (birationalPrimeLift u hu p).1) ∧
      ∀ w : W, u w = p.1 → w = (birationalPrimeLift u hu p).1 :=
  Classical.choose_spec (exists_unique_prime_over_of_proper_birational u hu p)

lemma birationalPrimeLift_injective : Function.Injective (birationalPrimeLift u hu) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = u (birationalPrimeLift u hu p).1 := (birationalPrimeLift_spec u hu p).1.symm
    _ = u (birationalPrimeLift u hu q).1 := congrArg (fun v : PrimeDivisor W => u v.1) hpq
    _ = q.1 := (birationalPrimeLift_spec u hu q).1

noncomputable def birationalWeilPushforward : WeilDivisor W →+ WeilDivisor X :=
  Finsupp.comapDomain.addMonoidHom (birationalPrimeLift_injective u hu)

@[simp] lemma birationalWeilPushforward_apply (P : WeilDivisor W) (p : PrimeDivisor X) :
    birationalWeilPushforward u hu P p = P (birationalPrimeLift u hu p) := rfl

theorem birationalWeilPushforward_single_of_contracted
    (q : PrimeDivisor W) (hq : 1 < Order.coheight (u q.1)) (a : ℤ) :
    birationalWeilPushforward u hu (Finsupp.single q a) = 0 := by
  classical
  ext p
  rw [birationalWeilPushforward_apply, Finsupp.single_apply, Finsupp.zero_apply]
  apply ite_eq_right
  intro h
  have he : u q.1 = p.1 := by
    rw [h]
    exact (birationalPrimeLift_spec u hu p).1
  rw [he, p.2] at hq
  exact (lt_irrefl _ hq)

variable [IsLocallyNoetherian W] [IsDominant u]

theorem birationalWeilPushforward_cartierPullback
    {D : WeilDivisor X} {P : WeilDivisor W} (hP : IsCartierPullback u D P) :
    birationalWeilPushforward u hu P = D := by
  ext p
  let q := birationalPrimeLift u hu p
  have hq : u q.1 = p.1 := (birationalPrimeLift_spec u hu p).1
  let : IsIso (u.stalkMap q.1) := (birationalPrimeLift_spec u hu p).2.1
  have hp : Order.coheight (u q.1) = 1 := by rw [hq]; exact p.2
  have he : (⟨u q.1, hp⟩ : PrimeDivisor X) = p := Subtype.ext hq
  change P q = D p
  simpa only [he] using IsCartierPullback.coeff_eq_of_stalk_iso u q hp hP

theorem divisorSection_birational_descent
    {P : WeilDivisor W} {s : X.functionField}
    (hsec : IsDivisorSection P (dominantFunctionFieldMap u s)) :
    IsDivisorSection (birationalWeilPushforward u hu P) s := by
  by_cases hs : s = 0
  · exact Or.inl hs
  rcases hsec with hzero | hsec
  · exact ((map_ne_zero (dominantFunctionFieldMap u)).mpr hs hzero).elim
  right
  intro p
  let q := birationalPrimeLift u hu p
  have hq : u q.1 = p.1 := (birationalPrimeLift_spec u hu p).1
  let : IsIso (u.stalkMap q.1) := (birationalPrimeLift_spec u hu p).2.1
  have hp : Order.coheight (u q.1) = 1 := by rw [hq]; exact p.2
  have horder := order_dominantFunctionFieldMap_of_stalk_iso u q hp s hs
  have h := hsec q
  rw [horder, hq] at h
  exact h

end WeilPushforward

section ProjectiveDescent
variable (W X : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (hcomplex : u ≫ X.structureMap = W.structureMap)

include hu hcomplex

theorem birational_sections_linear_injection (P : WeilDivisor W.scheme) :
    letI := schemeFieldAlgebra (.of ℂ) W.structureMap
    letI := schemeFieldAlgebra (.of ℂ) X.structureMap
    ∃ F : divisorSectionsOver (.of ℂ) W.structureMap P →ₗ[ℂ]
        divisorSectionsOver (.of ℂ) X.structureMap (birationalWeilPushforward u hu P),
      Function.Injective F ∧ ∀ r, dominantFunctionFieldMap u (F r).1 = r.1 := by
  dsimp only
  let := schemeFieldAlgebra (.of ℂ) W.structureMap
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  obtain ⟨φ, hφ⟩ := hu
  let e := partialIsoFunctionFieldEquiv φ
  have he (s : W.scheme.functionField) : dominantFunctionFieldMap u (e s) = s := by
    apply e.injective
    exact partialIso_dominantFunctionFieldMap u φ hφ _
  let F : divisorSectionsOver (.of ℂ) W.structureMap P →ₗ[ℂ]
      divisorSectionsOver (.of ℂ) X.structureMap (birationalWeilPushforward u ⟨φ, hφ⟩ P) := {
    toFun := fun s => ⟨e s.1, divisorSection_birational_descent u ⟨φ, hφ⟩ (by
      rw [he]
      exact s.2)⟩
    map_add' := fun _ _ => Subtype.ext (map_add e _ _)
    map_smul' := by
      intro a s
      apply Subtype.ext
      apply (dominantFunctionFieldMap u).injective
      change dominantFunctionFieldMap u (e (schemeFieldScalar (.of ℂ) W.structureMap a * s.1)) =
        dominantFunctionFieldMap u (schemeFieldScalar (.of ℂ) X.structureMap a * e s.1)
      rw [he, map_mul, dominantFunctionFieldMap_scalar _ _ _ _ hcomplex, he] }
  refine ⟨F, ?_, fun r => he r.1⟩
  intro r s h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

theorem sectionDimension_le_birationalWeilPushforward (P : WeilDivisor W.scheme) :
    sectionDimension W P ≤ sectionDimension X (birationalWeilPushforward u hu P) := by
  obtain ⟨F, hF, _⟩ := birational_sections_linear_injection W X u hu hcomplex P
  exact sectionDimension_le_of_injective W X _ _ F hF

theorem exists_fixed_ample_twist_on_birational_model
    {D : WeilDivisor X.scheme} {L : WeilDivisor W.scheme}
    (hL : IsCartierPullback u D L) (P : WeilDivisor W.scheme) :
    ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧ ∀ m : ℕ,
      sectionDimension W (m • L + P) ≤ sectionDimension X (m • D + A) := by
  obtain ⟨A, hA, hAP⟩ := exists_fixed_ample_twist_sectionDimension_le X D
    (birationalWeilPushforward u hu P)
  refine ⟨A, hA, fun m => ?_⟩
  have hdes := sectionDimension_le_birationalWeilPushforward W X u hu hcomplex (m • L + P)
  rw [map_add, map_nsmul, birationalWeilPushforward_cartierPullback u hu hL] at hdes
  exact hdes.trans (hAP m)

theorem no_quadratic_growth_on_birational_model
    {n : ℕ} {D : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ)) (hn : 2 ≤ n)
    {L : WeilDivisor W.scheme} (hL : IsCartierPullback u D L)
    (P : WeilDivisor W.scheme) {r : ℕ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : 0 < c) :
    ¬ ∀ᶠ m in Filter.atTop,
      c * (r * m : ℕ) ^ 2 ≤ sectionDimension W ((r * m) • L + P) := by
  obtain ⟨A, hA, hAP⟩ := exists_fixed_ample_twist_on_birational_model W X u hu hcomplex hL P
  intro hgrowth
  apply no_quadratic_growth_on_multiples_of_kappaSigma_eq_one X hsigma hn hA hr hc
  filter_upwards [hgrowth] with m hm
  exact hm.trans (hAP (r * m))

end ProjectiveDescent
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Filter
open scoped ENNReal

theorem sectionDimension_mono (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    {D E : WeilDivisor X.scheme} (hDE : D ≤ E) :
    sectionDimension X D ≤ sectionDimension X E := by
  apply sectionDimension_le_of_nonzero_section X (s := 1) one_ne_zero
  right
  intro p
  simpa only [order_one, zero_add, Finsupp.sub_apply] using sub_nonneg.mpr (hDE p)

theorem sectionDimension_le_of_cartierPullback
    (W V : ComplexProjectiveVariety) [StalkwiseNormal W.scheme] [StalkwiseNormal V.scheme]
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hq : q ≫ V.structureMap = W.structureMap)
    {D : WeilDivisor V.scheme} {P : WeilDivisor W.scheme}
    (hP : IsCartierPullback q D P) : sectionDimension V D ≤ sectionDimension W P := by
  obtain ⟨F, hF, _⟩ := dominant_sections_linear_injection W V q hq D P hP
  exact sectionDimension_le_of_injective V W D P F hF

theorem exists_fixed_ample_twist_of_effective_comparison
    (W X V : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal V.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (huC : u ≫ X.structureMap = W.structureMap)
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hqC : q ≫ V.structureMap = W.structureMap)
    {D : WeilDivisor X.scheme} {L P : WeilDivisor V.scheme}
    {K M Q : WeilDivisor W.scheme}
    (hK : IsCartierPullback u D K) (hM : IsCartierPullback q L M)
    (hQ : IsCartierPullback q P Q) (hcomparison : M ≤ K) :
    ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧ ∀ m : ℕ,
      sectionDimension V (m • L + P) ≤ sectionDimension X (m • D + A) := by
  obtain ⟨A, hA, hAW⟩ := exists_fixed_ample_twist_on_birational_model W X u hu huC hK Q
  refine ⟨A, hA, fun m => ?_⟩
  calc
    sectionDimension V (m • L + P) ≤ sectionDimension W (m • M + Q) :=
      sectionDimension_le_of_cartierPullback W V q hqC ((hM.nsmul m).add hQ)
    _ ≤ sectionDimension W (m • K + Q) :=
      sectionDimension_mono W (by
        simpa only [add_comm Q] using add_le_add_right (nsmul_le_nsmul_right hcomparison m) Q)
    _ ≤ sectionDimension X (m • D + A) := hAW m

theorem no_quadratic_growth_under_effective_comparison
    (W X V : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal V.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (huC : u ≫ X.structureMap = W.structureMap)
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hqC : q ≫ V.structureMap = W.structureMap)
    {n : ℕ} {D : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ)) (hn : 2 ≤ n)
    {L P : WeilDivisor V.scheme} {K M Q : WeilDivisor W.scheme}
    (hK : IsCartierPullback u D K) (hM : IsCartierPullback q L M)
    (hQ : IsCartierPullback q P Q) (hcomparison : M ≤ K)
    {r : ℕ} (hr : 0 < r) {c : ℝ≥0∞} (hc : 0 < c) :
    ¬ ∀ᶠ m in atTop,
      c * (r * m : ℕ) ^ 2 ≤ sectionDimension V ((r * m) • L + P) := by
  obtain ⟨A, hA, hAX⟩ := exists_fixed_ample_twist_of_effective_comparison W X V
    u hu huC q hqC hK hM hQ hcomparison
  intro hgrowth
  apply no_quadratic_growth_on_multiples_of_kappaSigma_eq_one X hsigma hn hA hr hc
  filter_upwards [hgrowth] with m hm
  exact hm.trans (hAX (r * m))

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Filter
open scoped ENNReal

theorem exists_fixed_ample_twist_of_indexed_effective_comparison
    (W X V : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal V.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (huC : u ≫ X.structureMap = W.structureMap)
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hqC : q ≫ V.structureMap = W.structureMap)
    {d : ℕ} {D : WeilDivisor X.scheme} {L P : WeilDivisor V.scheme}
    {K M Q : WeilDivisor W.scheme}
    (hK : IsCartierPullback u (d • D) K) (hM : IsCartierPullback q L M)
    (hQ : IsCartierPullback q P Q) (hcomparison : M ≤ K) :
    ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧ ∀ m : ℕ,
      sectionDimension V (m • L + P) ≤ sectionDimension X ((d * m) • D + A) := by
  obtain ⟨A, hA, hAV⟩ := exists_fixed_ample_twist_of_effective_comparison W X V
    u hu huC q hqC hK hM hQ hcomparison
  refine ⟨A, hA, fun m => ?_⟩
  simpa only [smul_smul, Nat.mul_comm m d] using hAV m

theorem no_quadratic_growth_under_indexed_effective_comparison
    (W X V : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal V.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (huC : u ≫ X.structureMap = W.structureMap)
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hqC : q ≫ V.structureMap = W.structureMap)
    {n d : ℕ} (hd : 0 < d) {D : WeilDivisor X.scheme}
    (hsigma : kappaSigma X n D = (1 : WithBot ℕ)) (hn : 2 ≤ n)
    {L P : WeilDivisor V.scheme} {K M Q : WeilDivisor W.scheme}
    (hK : IsCartierPullback u (d • D) K) (hM : IsCartierPullback q L M)
    (hQ : IsCartierPullback q P Q) (hcomparison : M ≤ K)
    {r : ℕ} (hr : 0 < r) {c : ℝ≥0∞} (hc : 0 < c) :
    ¬ ∀ᶠ m in atTop,
      c * (r * m : ℕ) ^ 2 ≤ sectionDimension V ((r * m) • L + P) := by
  obtain ⟨A, hA, hAX⟩ := exists_fixed_ample_twist_of_indexed_effective_comparison W X V
    u hu huC q hqC hK hM hQ hcomparison
  have hd0 : (d : ℝ≥0∞) ^ 2 ≠ 0 := by simp [Nat.ne_of_gt hd]
  have hdt : (d : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hpos : 0 < c / (d : ℝ≥0∞) ^ 2 := ENNReal.div_pos (ne_of_gt hc) hdt
  intro hgrowth
  apply no_quadratic_growth_on_multiples_of_kappaSigma_eq_one X hsigma hn hA
    (Nat.mul_pos hd hr) hpos
  filter_upwards [hgrowth] with m hm
  have hscale : c / (d : ℝ≥0∞) ^ 2 * ((d * r) * m : ℕ) ^ 2 =
      c * (r * m : ℕ) ^ 2 := by
    rw [Nat.mul_assoc, Nat.cast_mul, mul_pow, ← mul_assoc,
      ENNReal.div_mul_cancel hd0 hdt]
  rw [hscale, Nat.mul_assoc]
  exact hm.trans (hAX (r * m))

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Filter
open scoped ENNReal

theorem exists_indexed_ample_twist_of_rational_comparison
    (W X V : ComplexProjectiveVariety)
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal V.scheme]
    (u : W.scheme ⟶ X.scheme) [IsProper u] [IsDominant u]
    (hu : IsBirationalMorphism u) (huC : u ≫ X.structureMap = W.structureMap)
    (q : W.scheme ⟶ V.scheme) [IsDominant q]
    (hqC : q ≫ V.structureMap = W.structureMap)
    {D : WeilDivisor X.scheme} (hD : IsCartierDivisor D)
    {L : QWeilDivisor V.scheme} {K M : QWeilDivisor W.scheme}
    (hK : IsQCartierPullback u (rationalWeilDivisor D) K)
    (hM : IsQCartierPullback q L M) (hcomparison : M ≤ K)
    (P : WeilDivisor V.scheme) (hP : IsCartierDivisor P) :
    ∃ d : ℕ, 0 < d ∧ ∃ L' : WeilDivisor V.scheme,
      IsCartierDivisor L' ∧ (d : ℚ) • L = rationalWeilDivisor L' ∧
      ∃ A : WeilDivisor X.scheme, IsAmpleDivisor A ∧ ∀ m : ℕ,
        sectionDimension V (m • L' + P) ≤ sectionDimension X ((d * m) • D + A) := by
  obtain ⟨K', hK'⟩ := exists_cartierPullback u D hD
  have heK : K = rationalWeilDivisor K' := hK.eq_integral hK'
  obtain ⟨d, hd, L', M', hL', heL, heM, hM'⟩ := hM
  obtain ⟨Q, hQ⟩ := exists_cartierPullback q P hP
  have hle : M' ≤ d • K' := by
    intro p
    have hcoeff := DFunLike.congr_fun heM p
    change (d : ℚ) * M p = (M' p : ℚ) at hcoeff
    have hp := hcomparison p
    rw [heK] at hp
    change M p ≤ (K' p : ℚ) at hp
    have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg d : (0 : ℚ) ≤ d)
    rw [hcoeff] at hmul
    change M' p ≤ (d : ℤ) * K' p
    exact_mod_cast hmul
  obtain ⟨A, hA, hAX⟩ := exists_fixed_ample_twist_of_indexed_effective_comparison W X V
    u hu huC q hqC (hK'.nsmul d) hM' hQ hle
  exact ⟨d, hd, L', hL', heL, A, hA, hAX⟩

end NumericalDimensionOne

end OAI
