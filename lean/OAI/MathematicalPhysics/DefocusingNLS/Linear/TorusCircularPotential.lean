import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusPrincipalPotential
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusConjugation

namespace OAI

/-! # The two physical multiplication blocks of the actual principal potential -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure T)
noncomputable local instance torusCircularPotentialMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusCircularPotentialProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

attribute [local irreducible] torusPrincipalPotential torusL2Product torusL2Conjugation
  expandingCircularCoefficient expandingAnticircularCoefficient

theorem torusPrincipalPotential_circular (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q : FourierL2)
    (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a k L q x‖ ^ (2 * m) ≤ M) (v : H) :
    torusPrincipalPotential m (expandingUnitTorusFunction a k L q)
      (expandingUnitTorusFunction a k L q).continuous M hM hQB v =
    (-Complex.I) •
      (torusL2Product (expandingUnitTorusFunction a k L
        (expandingCircularCoefficient a k L ha ha1 hk hL m q)) v +
       torusL2Product (expandingUnitTorusFunction a k L
        (expandingAnticircularCoefficient a k L ha ha1 hk hL m q)) (torusL2Conjugation v)) := by
  let A := expandingUnitTorusFunction a k L (expandingCircularCoefficient a k L ha ha1 hk hL m q)
  let B := expandingUnitTorusFunction a k L (expandingAnticircularCoefficient a k L ha ha1 hk hL m q)
  have hp : torusPrincipalPotential m (expandingUnitTorusFunction a k L q)
      (expandingUnitTorusFunction a k L q).continuous M hM hQB v =ᵐ[volume]
      (fun x => -Complex.I * oddPowerDerivative m (expandingUnitTorusFunction a k L q x) (v x)) := by
    unfold torusPrincipalPotential
    exact torusPrincipalAction_ae m (expandingUnitTorusFunction a k L q)
      (expandingUnitTorusFunction a k L q).continuous M hM hQB v
  apply Lp.ext
  filter_upwards [hp, torusL2Product_ae A v, torusL2Product_ae B (torusL2Conjugation v),
    torusL2Conjugation_ae v, Lp.coeFn_add (torusL2Product A v) (torusL2Product B (torusL2Conjugation v)),
    Lp.coeFn_smul (-Complex.I) (torusL2Product A v + torusL2Product B (torusL2Conjugation v))]
    with x hp hA hB hJ hadd hsmul
  rw [hp, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hA, hB, hJ]
  dsimp only [A, B]
  rw [expandingCircular_unit a k L ha ha1 hk hL, expandingAnticircular_unit a k L ha ha1 hk hL]
  simp only [oddPowerDerivative, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul, starRingEnd_apply]

end DefocusingNLS

end OAI
