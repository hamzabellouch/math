import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector
import OAI.Analysis.IrrationalRotation.Operators.ProjectionAtomOrbit

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem field_isStarProjection {θ : ℕ → ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hP : P ∈ factor θ) (hp : IsStarProjection P)
    (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, IsStarProjection (F x) := by
  obtain ⟨G, _, _, hG, huniq, _, _, hproj⟩ :=
    L2Multiplication.scalar_multiplier_fields_complete
      (default : HilbertBasis ℤ ℂ Fiber) P (factor_commutes_scalarMultiplier θ hP)
  filter_upwards [huniq F hF, hproj hp] with x hGF hx
  rwa [← hGF]

theorem projection_vectorTrace_mem_Ioo {θ : ℕ → ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hP : P ∈ factor θ) (hp : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    0 < (vectorTrace traceVector P).re ∧ (vectorTrace traceVector P).re < 1 := by
  have htrace := traceVector_faithfulTracial θ
  have hpos := ProjectionAtomOrbit.vectorTrace_pos_of_faithful traceVector htrace hP hp hP0
  have hcomp : 1 - P ∈ factor θ := sub_mem (one_mem _) hP
  have hcomp0 : (1 : Hilbert →L[ℂ] Hilbert) - P ≠ 0 := by
    intro h
    exact hP1 (sub_eq_zero.mp h).symm
  have hposcomp := ProjectionAtomOrbit.vectorTrace_pos_of_faithful
    traceVector htrace hcomp hp.one_sub hcomp0
  have hn : ‖traceVector‖ = 1 := htrace.1
  have heq : (vectorTrace traceVector (1 - P)).re =
      1 - (vectorTrace traceVector P).re := by
    simp [vectorTrace, inner_sub_right, inner_self_eq_norm_sq_to_K, hn]
  rw [heq] at hposcomp
  exact ⟨hpos, sub_pos.mp hposcomp⟩

theorem integral_central_mem_Ioo {θ : ℕ → ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hP : P ∈ factor θ) (hp : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    0 < ∫ x, (inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
        (F x (lp.single 2 (0 : ℤ) (1 : ℂ)))).re ∂baseMeasure ∧
      (∫ x, (inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
        (F x (lp.single 2 (0 : ℤ) (1 : ℂ)))).re ∂baseMeasure) < 1 := by
  have hint : Integrable (fun x => inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
      (F x (lp.single 2 (0 : ℤ) (1 : ℂ)))) baseMeasure := by
    apply (L2.integrable_inner (𝕜 := ℂ) traceVector (P traceVector)).congr
    filter_upwards [Lp.coeFn_const 2 baseMeasure (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber),
      hF traceVector] with x hx hPx
    change inner ℂ (traceVector x) (P traceVector x) = _
    rw [hPx]
    change traceVector x = _ at hx
    rw [hx]
    rfl
  have heq := congrArg Complex.re (vectorTrace_eq_integral_central P F hF)
  have hi : (∫ x, (inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
      (F x (lp.single 2 (0 : ℤ) (1 : ℂ)))).re ∂baseMeasure) =
      (vectorTrace traceVector P).re := by
    change (∫ x, RCLike.re (inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
      (F x (lp.single 2 (0 : ℤ) (1 : ℂ)))) ∂baseMeasure) = _
    rw [integral_re hint]
    exact heq.symm
  rw [hi]
  exact projection_vectorTrace_mem_Ioo hP hp hP0 hP1

end Invariant233.ProductModel

end

end OAI
