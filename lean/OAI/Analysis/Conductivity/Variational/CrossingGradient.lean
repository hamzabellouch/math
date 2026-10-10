import Mathlib
import OAI.Analysis.Conductivity.Flux.PotentialCurl

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma direction_scalar_cos {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i a : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y 0)*cos (r*y a)) x =
      f (x 0)*(-r*sin (r*x a)*(if a=i then 1 else 0)) +
      cos (r*x a)*(deriv f (x 0)*(if (0:Fin 3)=i then 1 else 0)) := by
  rw [direction_mul (by fun_prop) (by fun_prop),direction_cos_coord,direction_scalar_coord hf]

def crossingValue3 (L : ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  crossingValue L (x 0) (x a) (x b)

lemma crossingValue3_diff (L : ℝ) (a b : Fin 3) : Differentiable ℝ (crossingValue3 L a b) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  unfold crossingValue3 crossingValue
  fun_prop

lemma crossingValue3_direction (L : ℝ) (a b i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (crossingValue3 L a b) x =
      (if i=0 then crossingCurrentZ L (x 0) (x a) (x b) else 0) +
      (if i=a then -crossingFirst L (x 0)*sin (x a) else 0) +
      (if i=b then -2*crossingSecond L (x 0)*sin (2*x b) else 0) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  have he : crossingValue3 L a b = fun x =>
      crossingFirst L (x 0)*cos (1*x a)+crossingSecond L (x 0)*cos (2*x b) := by
    funext x; simp [crossingValue3,crossingValue]
  rw [he,direction_add (by fun_prop) (by fun_prop),direction_scalar_cos hf,direction_scalar_cos hg]
  simp only [one_mul,crossingCurrentZ]
  simp_rw [@eq_comm _ a i, @eq_comm _ b i, @eq_comm _ (0 : Fin 3) i]
  split_ifs <;> ring

def crossingTensor (L : ℝ) (a b : Fin 3) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    (if i=0 ∧ j=0 then 1 else 0) +
    (if i=a ∧ j=a then crossingXX L (x 0) (x a) (x b) else 0) +
    (if i=b ∧ j=b then crossingYY L (x 0) (x a) (x b) else 0) +
    (if i=a ∧ j=b then crossingXY L (x 0) (x a) (x b) else 0) +
    (if i=b ∧ j=a then crossingXY L (x 0) (x a) (x b) else 0)

lemma crossingTensor_mulVec (L : ℝ) (a b : Fin 3) (x v : Coord3) (i : Fin 3) :
    (crossingTensor L a b x *ᵥ v) i =
      (if i=0 then v 0 else 0) +
      (if i=a then crossingXX L (x 0) (x a) (x b)*v a+crossingXY L (x 0) (x a) (x b)*v b else 0) +
      (if i=b then crossingXY L (x 0) (x a) (x b)*v a+crossingYY L (x 0) (x a) (x b)*v b else 0) := by
  simp only [Matrix.mulVec,dotProduct,crossingTensor,add_mul,Finset.sum_add_distrib,
    ite_and,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero,one_mul]
  split_ifs <;> ring

lemma crossingTensor_constitution {L : ℝ} (hL : 0<L) {a b : Fin 3}
    (ha : a≠0) (hb : b≠0) (hab : a≠b) (x : Coord3) :
    crossingTensor L a b x *ᵥ (fun i => direction (Pi.single i 1) (crossingValue3 L a b) x) =
      potentialCurl (crossingPotential L a b) x := by
  ext i
  rw [crossingTensor_mulVec,crossingPotential_curl L ha hb hab]
  simp only [crossingValue3_direction,ha,hb,Ne.symm ha,Ne.symm hb,hab,Ne.symm hab,
    ite_true,ite_false,zero_add,add_zero]
  obtain ⟨hfx,hfy⟩ := crossing_current_constitution hL (x 0) (x a) (x b)
  rw [←hfx,←hfy]

end ScalarConductivity

end

end OAI
