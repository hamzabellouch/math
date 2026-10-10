import OAI.Probability.SignedSweeps.SubsetSweep

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

def upperInclusionMap : (Finset A → ℝ) →ₗ[ℝ] (Finset A → ℝ) where
  toFun μ T := ∑ S : Finset A, if T ⊆ S then μ S else 0
  map_add' := by
    intro μ ν
    ext T
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  map_smul' := by
    intro a μ
    ext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp

lemma upperInclusion_permutation (g : Equiv.Perm A) :
    Commute (upperInclusionMap (A := A)) (subsetRepresentation A g) := by
  change upperInclusionMap * subsetRepresentation A g = subsetRepresentation A g * upperInclusionMap
  apply LinearMap.ext
  intro μ
  funext T
  change (∑ S : Finset A, if T ⊆ S then μ (S.image (g⁻¹ : Equiv.Perm A)) else 0) =
    ∑ S : Finset A, if T.image (g⁻¹ : Equiv.Perm A) ⊆ S then μ S else 0
  apply Fintype.sum_equiv g.symm.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding, Equiv.Perm.coe_inv]
  simp only [Finset.image_subset_image_iff g.symm.injective]

lemma upperInclusion_average (H : Subgroup (Equiv.Perm A)) :
    Commute (upperInclusionMap (A := A)) (realGroupAverage ((subsetRepresentation A).comp H.subtype)) := by
  unfold realGroupAverage
  apply Commute.smul_right
  apply Commute.sum_right
  intro g _
  exact upperInclusion_permutation g.1

lemma subsetAverage_apply (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) (T : Finset A) :
    realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T =
      (Fintype.card H : ℝ)⁻¹ * ∑ g : H, μ (T.image ((g.1)⁻¹ : Equiv.Perm A)) := by
  classical
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    subsetRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul]

lemma subsetAverage_nonneg (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (T : Finset A) :
    0 ≤ realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T := by
  classical
  rw [subsetAverage_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun g _ => hμ _))

lemma subsetAverage_card_support (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) (k : ℕ)
    (hμ : ∀ S, S.card ≠ k → μ S = 0) (T : Finset A) (hT : T.card ≠ k) :
    realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T = 0 := by
  classical
  rw [subsetAverage_apply]
  have hs : ∀ g : H, μ (T.image ((g.1)⁻¹ : Equiv.Perm A)) = 0 := by
    intro g
    apply hμ
    rwa [Finset.card_image_of_injective _ (g.1⁻¹).injective]
  simp only [hs, Finset.sum_const_zero, mul_zero]

lemma subsetAverage_mass (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) :
    (∑ T, realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T) = ∑ T, μ T := by
  classical
  simp only [subsetAverage_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (g : H) : (∑ T : Finset A, μ (T.image ((g.1)⁻¹ : Equiv.Perm A))) = ∑ T, μ T := by
    simpa only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding, Equiv.Perm.coe_inv]
      using g.1.symm.finsetCongr.sum_comp μ
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma upperInclusion_pointMass (S : Finset A) :
    upperInclusionMap (fun U => if U = S then 1 else 0) =
      (fun T => if T ⊆ S then 1 else 0) := by
  ext T
  change (∑ U : Finset A, if T ⊆ U then (if U = S then (1 : ℝ) else 0) else 0) = _
  have he (U : Finset A) :
      (if T ⊆ U then (if U = S then (1 : ℝ) else 0) else 0) =
      (if U = S then (if T ⊆ U then 1 else 0) else 0) := by split_ifs <;> rfl
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sweptSubsetLaw (d : ℕ) (S T : Finset (Fin (2 ^ d))) : ℝ :=
  subsetSweep d (fun U => if U = S then 1 else 0) T

lemma upperInclusion_sweep (d : ℕ) :
    Commute (upperInclusionMap (A := Fin (2 ^ d))) (subsetSweep d) := by
  unfold subsetSweep
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
  exact upperInclusion_average _

lemma subsetSweep_law_properties (d : ℕ) (μ : Finset (Fin (2 ^ d)) → ℝ) (k : ℕ)
    (hμ : ∀ S, 0 ≤ μ S) (hcard : ∀ S, S.card ≠ k → μ S = 0) :
    (∀ T, 0 ≤ subsetSweep d μ T) ∧
      (∀ T, T.card ≠ k → subsetSweep d μ T = 0) ∧
      (∑ T, subsetSweep d μ T) = ∑ T, μ T := by
  have h (L : List (Fin d)) (μ : Finset (Fin (2 ^ d)) → ℝ)
      (hμ : ∀ S, 0 ≤ μ S) (hcard : ∀ S, S.card ≠ k → μ S = 0) :
      (∀ T, 0 ≤ (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T) ∧
      (∀ T, T.card ≠ k → (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T = 0) ∧
      (∑ T, (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T) = ∑ T, μ T := by
    induction L with
    | nil => exact ⟨hμ, hcard, rfl⟩
    | cons i L ih =>
      obtain ⟨ihp, ihc, ihm⟩ := ih
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact ⟨subsetAverage_nonneg _ _ ihp, subsetAverage_card_support _ _ _ ihc,
        (subsetAverage_mass _ _).trans ihm⟩
  simpa only [subsetSweep, List.ofFn_eq_map, List.map_reverse] using
    h (List.finRange d).reverse μ hμ hcard

lemma sweptSubsetLaw_nonneg (d : ℕ) (S T : Finset (Fin (2 ^ d))) : 0 ≤ sweptSubsetLaw d S T := by
  apply (subsetSweep_law_properties d (fun U => if U = S then 1 else 0) S.card _ _).1
  · intro U; split_ifs <;> norm_num
  · intro U hU; rw [ite_eq_right (fun he => hU (congrArg Finset.card he))]

lemma sweptSubsetLaw_card_support (d : ℕ) (S T : Finset (Fin (2 ^ d))) (hT : T.card ≠ S.card) :
    sweptSubsetLaw d S T = 0 := by
  apply (subsetSweep_law_properties d (fun U => if U = S then 1 else 0) S.card _ _).2.1 T hT
  · intro U; split_ifs <;> norm_num
  · intro U hU; rw [ite_eq_right (fun he => hU (congrArg Finset.card he))]

lemma sweptSubsetLaw_mass (d : ℕ) (S : Finset (Fin (2 ^ d))) : (∑ T, sweptSubsetLaw d S T) = 1 := by
  have h := (subsetSweep_law_properties d (fun U => if U = S then 1 else 0) S.card
    (fun U => by split_ifs <;> norm_num) (fun U hU => by
      rw [ite_eq_right (fun he => hU (congrArg Finset.card he))])).2.2
  simpa only [sweptSubsetLaw, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

lemma sweptSubsetLaw_upper_inclusion (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    (∑ U : Finset (Fin (2 ^ d)), if T ⊆ U then sweptSubsetLaw d S U else 0) ≤
      ((S.card : ℝ) / (2 ^ d : ℕ)) ^ T.card := by
  change upperInclusionMap (subsetSweep d (fun U => if U = S then 1 else 0)) T ≤ _
  have h := congrArg (fun F : Module.End ℝ (Finset (Fin (2 ^ d)) → ℝ) =>
    F (fun U => if U = S then 1 else 0) T) (upperInclusion_sweep d).eq
  change upperInclusionMap (subsetSweep d (fun U => if U = S then 1 else 0)) T =
    subsetSweep d (upperInclusionMap (fun U => if U = S then 1 else 0)) T at h
  rw [h, upperInclusion_pointMass]
  exact subsetSweep_upper_inclusion d S T

end SignedSweeps
end

end OAI
