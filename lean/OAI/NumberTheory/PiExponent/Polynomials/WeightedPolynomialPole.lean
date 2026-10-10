import OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound

namespace OAI

noncomputable section
namespace PiExponent.WeightedPolynomialPole
open WeightedCurveDegree PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

def coordinateOrder (v : AddValuation K (WithTop ℤ)) (x : K) : ℤ := by
  classical
  exact if h : x = 0 then 0 else integerOrder v (Units.mk0 x h)

def coordinatePole (v : AddValuation K (WithTop ℤ)) (x : ι → K) (w : ι → ℚ) : ℚ :=
  weightedPole w (fun i => (coordinateOrder v (x i) : ℚ))

@[simp] theorem realValuation_of_ne_zero (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) :
    realValuation v x = ((coordinateOrder v x : ℝ) : WithTop ℝ) := by
  rw [coordinateOrder, dite_eq_right hx, realValuation_apply]
  have h : v x = (integerOrder v (Units.mk0 x hx) : WithTop ℤ) :=
    (coe_integerOrder v (Units.mk0 x hx)).symm
  rw [h, WithTop.map_coe]

theorem coordinate_order_lower (v : AddValuation K (WithTop ℤ))
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι) :
    ((-(w i : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (x i) := by
  by_cases hx : x i = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v (x i) hx]
    apply WithTop.coe_le_coe.mpr
    have h := (div_le_iff₀ (hw i)).mp
      (div_le_weightedPole w (fun j => (coordinateOrder v (x j) : ℚ)) i)
    have hq : -(w i) * coordinatePole v x w ≤ (coordinateOrder v (x i) : ℚ) := by
      dsimp [coordinatePole]
      nlinarith
    exact_mod_cast hq

theorem framePolynomial_order_lower {m : ℕ} [Algebra ℂ K]
    (v : AddValuation K (WithTop ℤ)) (x : Fin (m+1) → K)
    (w : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (N : ℝ)
    (hc : ∀ c : ℂ, (0 : WithTop ℝ) ≤ realValuation v (algebraMap ℂ K c))
    (p : MvPolynomial (Fin (m+1)) ℂ)
    (hp : PiExponentApprox.HasWeightedDegreeLE (fun i => (w i : ℝ)) N p) :
    ((-N * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (MvPolynomial.aeval x p) := by
  apply PolynomialPoleBound.framePolynomial_order_lower
    (realValuation v) x (fun i => (w i : ℝ)) (coordinatePole v x w) N
      _ (coordinate_order_lower v x w hw) hc p hp
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder v (x i) : ℚ))

end PiExponent.WeightedPolynomialPole

end

end OAI
