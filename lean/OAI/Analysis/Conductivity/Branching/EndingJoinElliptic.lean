import Mathlib
import OAI.Analysis.Conductivity.Walls.EndingJoinCutoff

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

local instance endingJoinEllipticMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance endingJoinEllipticBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma delayedEndingTensor_measurable (lam k J L K R : ℝ) :
    Measurable (delayedEndingTensor lam k J L K R) :=
  (alignedEndingTensor_measurable _ _ _ _ _).comp (measurable_id.sub measurable_const)

lemma endingJoinTensor_measurable {D : Coord3 → Mat3} (hD : Measurable D) (lam k J L K : ℝ) :
    Measurable (endingJoinTensor D lam k J L K) := by
  have hh : Measurable (fun x : Coord3 => endingJoinCutoff (x 0)) := endingJoinCutoff_smooth.continuous.measurable.comp (measurable_pi_apply (0:Fin 3))
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  exact ((measurable_const.sub hh).mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hD))).add
    (hh.mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (delayedEndingTensor_measurable _ _ _ _ _ _))))

lemma endingJoinTensor_symm {D : Coord3 → Mat3} (hD : ∀ x,(D x).IsSymm) (lam k J L K : ℝ) (x : Coord3) :
    (endingJoinTensor D lam k J L K x).IsSymm :=
  ((hD x).smul _).add ((alignedEndingTensor_symm _ _ _ _ _ _).smul _)

lemma convexTensor_quadratic (A B : Mat3) (t : ℝ) (v : Coord3) :
    v ⬝ᵥ (((1-t) • A+t • B)*ᵥv)=(1-t)*(v ⬝ᵥ (A*ᵥv))+t*(v ⬝ᵥ (B*ᵥv)) := by
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]

lemma endingJoinTensor_bounds {D : Coord3 → Mat3} {lam k J L K c C : ℝ}
    (hD : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧ v ⬝ᵥ (D x*ᵥv)≤C*(v ⬝ᵥ v))
    (hE : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v)) (x v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (endingJoinTensor D lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (endingJoinTensor D lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  rw [endingJoinTensor,convexTensor_quadratic]
  have hd := hD x v
  have he := hE (x-Pi.single 0 7) v
  change c*(v ⬝ᵥv)≤v ⬝ᵥ(delayedEndingTensor lam k J L K 7 x*ᵥv) ∧
    v ⬝ᵥ(delayedEndingTensor lam k J L K 7 x*ᵥv)≤C*(v ⬝ᵥv) at he
  have ht := endingJoinCutoff_bounds (x 0)
  have ht' : 0≤1-endingJoinCutoff (x 0) := sub_nonneg.mpr ht.2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hd.1 ht',mul_le_mul_of_nonneg_left he.1 ht.1]
  · nlinarith [mul_le_mul_of_nonneg_left hd.2 ht',mul_le_mul_of_nonneg_left he.2 ht.1]

end ScalarConductivity

end

end OAI
