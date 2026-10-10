import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace OAI

/-! # The quantitative positive metric from an invertible star intertwiner

This is the final geometric step of Paulsen's theorem. The intertwiner may
map to a different Hilbert space. Its positive metric on the original space
and its positive square root yield the actual similarity unit, with exactly
the product of the forward and inverse operator norms.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The square of any bounded star intertwiner is a metric for the original
homomorphism, without an invertibility assumption. -/
theorem intertwiner_metric_identity (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) (a : A) :
    (W.adjoint.comp W).comp (π.1 (star a)) =
      (π.1 a).adjoint.comp (W.adjoint.comp W) := by
  have hadj : (π.1 a).adjoint.comp W.adjoint = W.adjoint.comp (σ (star a)) := by
    simpa only [adjoint_comp, map_star, star_eq_adjoint] using
      congrArg ContinuousLinearMap.adjoint (hW a)
  calc
    (W.adjoint.comp W).comp (π.1 (star a)) =
        W.adjoint.comp (W.comp (π.1 (star a))) := comp_assoc _ _ _
    _ = W.adjoint.comp ((σ (star a)).comp W) := by rw [hW]
    _ = (W.adjoint.comp (σ (star a))).comp W := (comp_assoc _ _ _).symm
    _ = ((π.1 a).adjoint.comp W.adjoint).comp W := by rw [← hadj]
    _ = (π.1 a).adjoint.comp (W.adjoint.comp W) := comp_assoc _ _ _

/-- The metric of a bounded linear isomorphism has an explicit inverse. -/
def intertwinerMetricUnit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) : (H →L[ℂ] H)ˣ where
  val := W.adjoint.comp W
  inv := L.comp L.adjoint
  val_inv := by
    change W.adjoint.comp (W.comp (L.comp L.adjoint)) = 1
    rw [← comp_assoc W L, hWL, one_def, id_comp]
    rw [← adjoint_comp, hLW, adjoint_one]
  inv_val := by
    change L.comp (L.adjoint.comp (W.adjoint.comp W)) = 1
    rw [← comp_assoc L.adjoint W.adjoint, ← adjoint_comp, hWL, adjoint_one,
      one_def, id_comp, hLW]

/-- The metric is positive because it is an adjoint square. -/
theorem intertwinerMetric_nonneg (W : H →L[ℂ] K) : 0 ≤ W.adjoint.comp W := by
  exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self W)

/-- A square root of the positive metric preserves both operator norms
needed for the sharp similarity estimate. -/
theorem exists_positive_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      0 ≤ (S : H →L[ℂ] H) ∧
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  let Q := intertwinerMetricUnit W L hLW hWL
  have hQ : 0 ≤ (Q : H →L[ℂ] H) := intertwinerMetric_nonneg W
  have hu : IsUnit (CFC.sqrt (Q : H →L[ℂ] H)) :=
    (CFC.isUnit_sqrt_iff _ hQ).mpr Q.isUnit
  obtain ⟨S, hS⟩ := hu
  have hSstar : star (S : H →L[ℂ] H) = (S : H →L[ℂ] H) := by
    rw [hS]
    exact (CFC.sqrt_nonneg _).star_eq
  have hSq : (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = (Q : H →L[ℂ] H) := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self _ hQ
  have hmetric : star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) =
      W.adjoint.comp W := by rw [hSstar, hSq]; rfl
  have hnorm : ‖(S : H →L[ℂ] H)‖ = ‖W‖ := by
    have h := CStarRing.norm_star_mul_self (x := (S : H →L[ℂ] H))
    rw [hmetric, norm_adjoint_comp_self] at h
    nlinarith [norm_nonneg (S : H →L[ℂ] H), norm_nonneg W]
  have hunit : S * S = Q := Units.ext hSq
  have hinvSq : (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) =
      L.comp L.adjoint := by
    have h := congrArg (fun U : (H →L[ℂ] H)ˣ => (↑U⁻¹ : H →L[ℂ] H)) hunit
    calc
      (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) = ↑((S * S)⁻¹) := by
        simp only [mul_inv_rev, Units.val_mul]
      _ = (↑Q⁻¹ : H →L[ℂ] H) := h
      _ = L.comp L.adjoint := rfl
  have hSstarU : star S = S := Units.ext hSstar
  have hinvstar : star (↑S⁻¹ : H →L[ℂ] H) = (↑S⁻¹ : H →L[ℂ] H) := by
    rw [← Units.coe_star, star_inv, hSstarU]
  have hinvnorm : ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
    have h := CStarRing.norm_star_mul_self (x := (↑S⁻¹ : H →L[ℂ] H))
    rw [hinvstar, hinvSq] at h
    have hLL := norm_adjoint_comp_self L.adjoint
    rw [adjoint_adjoint, adjoint.norm_map] at hLL
    rw [hLL] at h
    nlinarith [norm_nonneg (↑S⁻¹ : H →L[ℂ] H), norm_nonneg L]
  exact ⟨S, by rw [hS]; exact CFC.sqrt_nonneg _, hmetric, hnorm, hinvnorm⟩

/-- The positive metric construction gives an invertible star intertwiner. -/
theorem exists_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  obtain ⟨S, _, hS⟩ := exists_positive_sqrt_metric_unit W L hLW hWL
  exact ⟨S, hS⟩

/-- An invertible bounded intertwiner into a star representation supplies
similarity on the original space with its exact condition-number bound. -/
theorem quantitative_similarity_of_intertwiner (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  obtain ⟨S, hmetric, hnorm, hinvnorm⟩ := exists_sqrt_metric_unit W L hLW hWL
  refine ⟨S, by rw [hnorm, hinvnorm], ?_⟩
  intro a
  have h := intertwiner_metric_identity π σ W hW a
  change (W.adjoint.comp W) * π.1 (star a) = star (π.1 a) * (W.adjoint.comp W) at h
  rw [← hmetric] at h
  have he := congrArg (fun X : H →L[ℂ] H =>
    star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) h
  simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
    Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
    Units.mul_inv_cancel_left, mul_one, one_mul] using he

end KadisonSimilarity

end

end OAI
