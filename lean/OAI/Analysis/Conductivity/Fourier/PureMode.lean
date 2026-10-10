import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingGradient

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def pureModeValue (f : ℝ → ℝ) (a : Fin 3) (x : Coord3) : ℝ :=
  f (x 0)*cos (x a)

def pureModePotential (f : ℝ → ℝ) (a : Fin 3) : Fin 3 → Fin 3 → Coord3 → ℝ :=
  wedgePotential 0 a (fun x => deriv f (x 0)*sin (x a))

def pureModeTensor (q : ℝ) (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (fun i => if i=a then q else 1)

lemma pureModeValue_diff {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : Fin 3) :
    Differentiable ℝ (pureModeValue f a) := by
  unfold pureModeValue
  fun_prop

lemma pureModePotential_diff {f : ℝ → ℝ} (hf : Differentiable ℝ (deriv f))
    (a i j : Fin 3) : Differentiable ℝ (pureModePotential f a i j) := by
  exact wedgePotential_diff (by fun_prop) _ _ _ _

lemma pureModeValue_direction {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (a i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (pureModeValue f a) x =
      (if i=0 then deriv f (x 0)*cos (x a) else 0) +
      (if i=a then -f (x 0)*sin (x a) else 0) := by
  have h := direction_scalar_cos hf 1 i a x
  simp only [one_mul] at h
  unfold pureModeValue
  rw [h]
  simp_rw [@eq_comm _ a i,@eq_comm _ (0:Fin 3) i]
  split_ifs <;> ring

lemma pureModePotential_curl {f : ℝ → ℝ} (hf : Differentiable ℝ (deriv f))
    {a : Fin 3} (ha : a≠0) (x : Coord3) (i : Fin 3) :
    potentialCurl (pureModePotential f a) x i =
      (if i=0 then deriv f (x 0)*cos (x a) else 0) -
      (if i=a then deriv (deriv f) (x 0)*sin (x a) else 0) := by
  rw [pureModePotential,potentialCurl_wedge (by fun_prop)]
  have ha' := direction_scalar_sin hf 1 a a x
  have h0 := direction_scalar_sin hf 1 0 a x
  simp only [one_mul,ha,Ne.symm ha,ite_true,ite_false,mul_one,mul_zero,add_zero,zero_add] at ha' h0
  rw [ha',h0]
  ring_nf

lemma pureMode_constitution {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) {a : Fin 3} (ha : a≠0) (x : Coord3)
    (q : ℝ) (heq : deriv (deriv f) (x 0) = q*f (x 0)) :
    pureModeTensor q a *ᵥ (fun i => direction (Pi.single i 1) (pureModeValue f a) x) =
      potentialCurl (pureModePotential f a) x := by
  ext i
  rw [pureModeTensor,mulVec_diagonal]
  simp only [pureModeValue_direction hf,pureModePotential_curl hf' ha,heq]
  by_cases h0 : i=0
  · subst i
    simp [Ne.symm ha]
  · by_cases hai : i=a
    · subst i
      simp [ha]
      ring
    · simp [h0,hai]

lemma pureModeTensor_quadratic (q : ℝ) (a : Fin 3) (v : Coord3) :
    v ⬝ᵥ (pureModeTensor q a *ᵥ v) = ∑ i, (if i=a then q else 1)*(v i)^2 := by
  simp only [pureModeTensor,mulVec_diagonal,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pureModeTensor_bounds {q : ℝ} (hq₁ : 1/8 ≤ q) (hq₂ : q ≤ 10)
    (a : Fin 3) (v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (pureModeTensor q a *ᵥ v) ∧
      v ⬝ᵥ (pureModeTensor q a *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  rw [pureModeTensor_quadratic]
  simp only [dotProduct,Finset.mul_sum,←sq]
  constructor <;> apply Finset.sum_le_sum <;> intro i _
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    split <;> linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    split <;> linarith

end ScalarConductivity

end

end OAI
