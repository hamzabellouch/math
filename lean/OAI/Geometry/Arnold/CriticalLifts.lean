import OAI.Geometry.Arnold.FixedPoints

namespace OAI

universe uα

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma vec_five_two {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 2 = c := rfl
lemma vec_five_three {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 3 = d := rfl
lemma vec_five_four {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 4 = e := rfl

def zeroVector : CV := ![0, 1/2, -Complex.I/2, 1/2, Complex.I/2]
def otherVector (r : ℝ) : CV := ![0, (1+(r:ℂ))/4, Complex.I/2, (1-(r:ℂ))/4, -Complex.I/2]

lemma zeroVector_unit : IsUnitQuadric zeroVector := by
  constructor
  · norm_num [normSquared, zeroVector, Fin.sum_univ_succ, Complex.normSq_apply]
  · apply Complex.ext <;> norm_num [quadricPolynomial, zeroVector, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two]

lemma otherVector_unit (r : ℝ) (hr : r^2 = 3) : IsUnitQuadric (otherVector r) := by
  constructor
  · norm_num [normSquared, otherVector, Fin.sum_univ_succ, Complex.normSq_apply]
    nlinarith
  · apply Complex.ext <;> norm_num [quadricPolynomial, otherVector, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith

def zeroLift : UnitQuadric := ⟨zeroVector,zeroVector_unit⟩
def plusLift : UnitQuadric := ⟨otherVector (Real.sqrt 3),otherVector_unit _ (Real.sq_sqrt (by norm_num))⟩
def minusLift : UnitQuadric := ⟨otherVector (-Real.sqrt 3),otherVector_unit _ (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))⟩

lemma zeroVector_factors : sphereFactors zeroVector = qzero := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, sphereFactors, leftSphere, rightSphere, moment_real, zeroVector, qzero, pole, east]

lemma otherVector_factors (r : ℝ) (_hr : r^2 = 3) :
    sphereFactors (otherVector r) = (![r/2,0,-1/2], ![1/2,0,-r/2]) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, sphereFactors, leftSphere, rightSphere, moment_real, otherVector] <;> nlinarith

lemma plusLift_factors : sphereFactors plusLift = qplus :=
  otherVector_factors _ (Real.sq_sqrt (by norm_num))
lemma minusLift_factors : sphereFactors minusLift = qminus := by
  simpa [minusLift, qminus] using otherVector_factors (-Real.sqrt 3) (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))

lemma core_zeroVector : core zeroVector = 0 := by
  have he := core_unit zeroLift (by rfl)
  change core zeroVector = _ at he
  rw [he]
  have hL : leftSphere zeroVector = pole := congrArg Prod.fst zeroVector_factors
  have hR : rightSphere zeroVector = -east := congrArg Prod.snd zeroVector_factors
  change leftOperator 0 zeroVector - rightOperator 2 zeroVector + mixedField zeroVector - pairing zeroVector • selfField zeroVector = _
  simp only [mixedField, pairing, selfField, hL, hR]
  ext i
  fin_cases i <;> norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, pole, east,
    leftOperator, rightOperator, rotor_apply, zeroVector, Fin.sum_univ_succ, Pi.single_apply]

lemma core_otherVector (r : ℝ) (hr : r^2 = 3) :
    core (otherVector r) = (-(3*r/2)) • (Complex.I • otherVector r) := by
  let z : UnitQuadric := ⟨otherVector r, otherVector_unit r hr⟩
  have he := core_unit z (by rfl)
  change core (otherVector r) = _ at he
  rw [he]
  have hL : leftSphere (otherVector r) = ![r/2,0,-1/2] := congrArg Prod.fst (otherVector_factors r hr)
  have hR : rightSphere (otherVector r) = ![1/2,0,-r/2] := congrArg Prod.snd (otherVector_factors r hr)
  change leftOperator 0 (otherVector r) - rightOperator 2 (otherVector r) + mixedField (otherVector r) - pairing (otherVector r) • selfField (otherVector r) = _
  simp only [mixedField, pairing, selfField, hL, hR]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, leftOperator, rightOperator,
      rotor_apply, otherVector, Fin.sum_univ_succ, Pi.single_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hr, congrArg (fun s : ℝ ↦ r*s) hr]

end ArnoldCounterexample.Construction

end

end OAI
