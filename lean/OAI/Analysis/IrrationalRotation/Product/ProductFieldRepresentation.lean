import OAI.Analysis.IrrationalRotation.Model.ProductFactorStructure
import OAI.Analysis.IrrationalRotation.Product.ProductProjectionFields
import OAI.Analysis.IrrationalRotation.Product.ProductFactorSource

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

theorem exists_covariantFieldRepresentation {θ : ℕ → ℝ}
    {A : Hilbert →L[ℂ] Hilbert} (hA : A ∈ factor θ) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ A F ‖A‖ := by
  obtain ⟨F, hbound, hm, hrep, _⟩ := exists_unique_field hA
  refine ⟨F, norm_nonneg A, hbound, hm, hrep, ?_⟩
  filter_upwards [field_conjugacy hA F hrep] with x hx
  have hrot : rotationIterate θ 1 x = rotation θ x := by
    funext i
    change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
    simp only [Int.cast_one, one_mul]
  rw [← hrot]
  exact hx 1

theorem exists_covariantFieldRepresentation_with_trace {θ : ℕ → ℝ}
    {A : Hilbert →L[ℂ] Hilbert} (hA : A ∈ factor θ) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ A F ‖A‖ ∧
      vectorTrace traceVector A = centralDiagonalIntegral F := by
  obtain ⟨F, hF⟩ := exists_covariantFieldRepresentation hA
  exact ⟨F, hF, hF.vectorTrace_eq⟩

theorem exists_covariantProjectionField {θ : ℕ → ℝ}
    {P : Hilbert →L[ℂ] Hilbert} (hPm : P ∈ factor θ) (hP : IsStarProjection P) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ P F 1 ∧ ∀ x, IsStarProjection (F x) := by
  classical
  obtain ⟨F, hbound, hm, hrep, _⟩ := exists_unique_field hPm
  have hproj := field_isStarProjection hPm hP F hrep
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hproj)
  let G : Base → Fiber →L[ℂ] Fiber := fun x => if x ∈ N then 0 else F x
  have hgood : ∀ᵐ x ∂baseMeasure, x ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hGF : G =ᵐ[baseMeasure] F := by
    filter_upwards [hgood] with x hx
    simp only [G, ite_eq_right hx]
  have hGrep : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => G x (ξ x) := by
    intro ξ
    filter_upwards [hrep ξ, hGF] with x hξ hx
    rw [hx]
    exact hξ
  have hGproj : ∀ x, IsStarProjection (G x) := by
    intro x
    by_cases hx : x ∈ N
    · simp only [G, ite_eq_left hx]
      exact IsStarProjection.zero _
    · simp only [G, ite_eq_right hx]
      by_contra hn
      exact hx (hsub hn)
  refine ⟨G, ⟨by norm_num, ?_, ?_, hGrep, ?_⟩, hGproj⟩
  · intro x
    exact IsStarProjection.norm_le _ (hGproj x)
  · intro v
    have heq : (fun x => G x v) = N.piecewise (fun _ => (0 : Fiber)) (fun x => F x v) := by
      funext x
      by_cases hx : x ∈ N <;> simp [G, Set.piecewise, hx]
    rw [heq]
    exact (stronglyMeasurable_const : StronglyMeasurable (fun _ : Base => (0 : Fiber))).piecewise
      hN (hm v)
  · filter_upwards [field_conjugacy hPm G hGrep] with x hx
    have hrot : rotationIterate θ 1 x = rotation θ x := by
      funext i
      change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
      simp only [Int.cast_one, one_mul]
    rw [← hrot]
    exact hx 1

end Invariant233.ProductModel

end

end OAI
