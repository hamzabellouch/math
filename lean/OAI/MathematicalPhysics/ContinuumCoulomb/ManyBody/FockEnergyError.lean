import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockCoefficientNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorNorm

namespace OAI

/-! Operator errors control every normalized occupation-sector energy with
polynomial mode dependence. The tensor and exterior norms are identified. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock HubbardGlobal

theorem occupationInner_fockCoordinates {Q : ℕ} (x y : Space Q) :
    occupationInner Q x y = inner ℂ (fockCoordinates Q x) (fockCoordinates Q y) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply',fockCoordinates_apply,
    occupationInner,occupationBasis,fockBasis,starRingEnd_apply]

theorem occupationNormSq_fockCoordinates {Q : ℕ} (x : Space Q) :
    occupationNormSq Q x = ‖fockCoordinates Q x‖^2 := by
  simp only [fockCoordinates_norm_sq,occupationNormSq,fockMass,occupationBasis,fockBasis,
    Complex.normSq_eq_norm_sq]

theorem occupationInner_operator_error {Q : ℕ} (T U : Module.End ℂ (Space Q))
    (ε : ℝ) (hε : ‖fockOperator (T-U)‖ ≤ ε) (x : Space Q) :
    |(occupationInner Q x (T x)).re-(occupationInner Q x (U x)).re| ≤
      ε*occupationNormSq Q x := by
  rw [occupationInner_fockCoordinates,occupationInner_fockCoordinates,
    ← Complex.sub_re,← inner_sub_right,← map_sub,← LinearMap.sub_apply,
    ← fockOperator_coordinates]
  calc
    _ ≤ ‖inner ℂ (fockCoordinates Q x) (fockOperator (T-U) (fockCoordinates Q x))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖fockCoordinates Q x‖*‖fockOperator (T-U) (fockCoordinates Q x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖fockCoordinates Q x‖*(ε*‖fockCoordinates Q x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((fockOperator (T-U)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
    _ = _ := by rw [occupationNormSq_fockCoordinates]; ring

theorem finiteTensorState_occupationMass {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State n Q) (hc : Laughlin.Antisymmetric c) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) =
      occupationNormSq Q (normalizedTensorExterior n Q c) := by
  rw [finiteTensorState_mass v hv hL2 hpartial (fun a b => by
    split_ifs with h <;> simpa only [h,ite_true,ite_false] using ho a b) c,
    normalizedTensorExterior_norm n Q c hc]

end ContinuumCoulomb

end

end OAI
