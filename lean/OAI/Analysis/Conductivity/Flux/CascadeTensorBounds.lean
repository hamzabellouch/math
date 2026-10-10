import Mathlib
import OAI.Analysis.Conductivity.Fourier.PureMode

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cubic_axes {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) :
    a=1 ∧ b=2 ∨ a=2 ∧ b=1 := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma crossingTensor_symm (L : ℝ) (a b : Fin 3) (x : Coord3) :
    (crossingTensor L a b x).IsSymm := by
  ext i j
  simp only [transpose_apply,crossingTensor]
  simp_rw [and_comm]
  ring

lemma crossingTensor_quadratic {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b)
    (L : ℝ) (x v : Coord3) :
    v ⬝ᵥ (crossingTensor L a b x *ᵥ v) =
      (v 0)^2 + crossingXX L (x 0) (x a) (x b)*(v a)^2+
      2*crossingXY L (x 0) (x a) (x b)*v a*v b+
      crossingYY L (x 0) (x a) (x b)*(v b)^2 := by
  rcases cubic_axes ha hb hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [dotProduct,Fin.sum_univ_three,crossingTensor_mulVec] <;> ring

lemma dotProduct_cubic_axes {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) (v : Coord3) :
    v ⬝ᵥ v = (v 0)^2+(v a)^2+(v b)^2 := by
  rcases cubic_axes ha hb hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [dotProduct,Fin.sum_univ_three] <;> ring

lemma crossingTensor_bounds {L : ℝ}
    (hL : ∀ z x y X Y : ℝ,
      (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
      crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2))
    {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) (x v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (crossingTensor L a b x *ᵥ v) ∧
      v ⬝ᵥ (crossingTensor L a b x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  rw [crossingTensor_quadratic ha hb hab,dotProduct_cubic_axes ha hb hab]
  obtain ⟨hl,hu⟩ := hL (x 0) (x a) (x b) (v a) (v b)
  constructor <;> nlinarith [sq_nonneg (v 0)]

lemma pureModeTensor_symm (q : ℝ) (a : Fin 3) : (pureModeTensor q a).IsSymm := by
  exact isSymm_diagonal _

lemma pureModeTensor_normal {a : Fin 3} (ha : a≠0) (q : ℝ) :
    pureModeTensor q a *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  ext i
  rw [pureModeTensor,mulVec_diagonal]
  by_cases hi : i=0
  · subst i; simp [Ne.symm ha]
  · simp [Pi.single_eq_of_ne hi]

lemma crossingTensor_normal {a b : Fin 3} (ha : a≠0) (hb : b≠0)
    (L : ℝ) (x : Coord3) :
    crossingTensor L a b x *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  ext i
  rw [crossingTensor_mulVec]
  simp [ha,hb,Pi.single_eq_of_ne,Pi.single_apply,eq_comm]

lemma crossingTensor_continuous (L : ℝ) (a b : Fin 3) :
    Continuous (crossingTensor L a b) := by
  have hf := (crossingResidualFirst_smooth L).continuous
  have hg := (crossingResidualSecond_smooth L).continuous
  have hff := (crossingFirst_smooth L).continuous
  have hgg := (crossingSecond_smooth L).continuous
  have hxx : Continuous (fun x : Coord3 => crossingXX L (x 0) (x a) (x b)) := by
    unfold crossingXX crossingHxx
    fun_prop (disch := intro x; positivity)
  have hyy : Continuous (fun x : Coord3 => crossingYY L (x 0) (x a) (x b)) := by
    unfold crossingYY crossingHxx
    fun_prop (disch := intro x; positivity)
  have hxy : Continuous (fun x : Coord3 => crossingXY L (x 0) (x a) (x b)) := by
    unfold crossingXY crossingHxy
    fun_prop (disch := intro x; positivity)
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  unfold crossingTensor
  split_ifs <;> fun_prop

end ScalarConductivity

end

end OAI
