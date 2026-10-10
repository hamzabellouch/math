import Mathlib
import OAI.Analysis.AffineBernstein.FlatFCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma flatInverseTrace_hessian (φ : E → ℝ) (v : ι → E) (x : E)
    (hd : (flatBlockHessian φ v x).det ≠ 0) :
    flatInverseTrace (flatBlockHessian φ v x) v φ x = Fintype.card ι := by
  exact matrix_inverse_contraction_self hd

lemma flatInverseTrace_neg_hessian (φ : E → ℝ) (v : ι → E) (x : E)
    (hd : (-flatBlockHessian φ v x).det ≠ 0) :
    flatInverseTrace (-flatBlockHessian φ v x) v φ x = -(Fintype.card ι : ℝ) := by
  have hh := matrix_inverse_contraction_self hd
  simp only [Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib] at hh
  change -flatInverseTrace (-flatBlockHessian φ v x) v φ x = _ at hh
  linarith

/- The exact local flat-chart f equation. At the center of the flat normal
chart its angular terms equal the spherical covariant terms; no derivative
of a determinant or scalar density has been omitted. -/
theorem flat_f_equation_of_log_euler {W : Set E} (hW : IsOpen W)
    {φ t : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ W) (ht : ContDiffOn ℝ ∞ t W)
    (hpos : ∀ y ∈ W, 0 < φ y) (v : ι → E) (w : κ → E)
    {x : E} (hx : x ∈ W) {c : ℝ}
    (hBd : (-flatBlockHessian φ v x).det ≠ 0)
    (hRd : (flatBlockHessian φ w x).det ≠ 0)
    (he : flatInverseTrace (-flatBlockHessian φ v x) v t x -
      c*flatInversePair (-flatBlockHessian φ v x) v t t x +
      flatInverseTrace (flatBlockHessian φ w x) w t x +
      flatInversePair (flatBlockHessian φ w x) w t t x = 0) :
    let B := -flatBlockHessian φ v x
    let R := flatBlockHessian φ w x
    let p := fun y => Real.log (φ y)
    let f := fun y => t y-p y
    (Fintype.card κ : ℝ) - Fintype.card ι + φ x * flatInverseTrace B v f x -
      φ x * flatInversePair B v p p x - c*φ x*flatInversePair B v t t x +
      φ x * flatInverseTrace R w f x + 2*φ x*flatInversePair R w p f x +
      φ x * flatInversePair R w f f x = 0 := by
  let B := -flatBlockHessian φ v x
  let R := flatBlockHessian φ w x
  let p := fun y => Real.log (φ y)
  let f := fun y => t y-p y
  have hp : ContDiffOn ℝ ∞ p W := hφ.log (fun y hy => ne_of_gt (hpos y hy))
  have hpt := (hp.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have htt := (ht.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hB := flat_log_hessian_trace hW hφ hpos hx B v
  have hR := flat_log_hessian_trace hW hφ hpos hx R w
  rw [flatInverseTrace_neg_hessian φ v x hBd] at hB
  rw [flatInverseTrace_hessian φ w x hRd] at hR
  have hfB := flatInverseTrace_sub hW ht hp hx B v
  have hfR := flatInverseTrace_sub hW ht hp hx R w
  have hpp := flatInversePair_sub_self htt hpt R
    (flatBlockHessian_isSymm (hφ.contDiffAt (hW.mem_nhds hx)) w) w
  have hpf := flatInversePair_sub_right (f := p) htt hpt R w
  change flatInverseTrace B v t x - c*flatInversePair B v t t x +
    flatInverseTrace R w t x + flatInversePair R w t t x = 0 at he
  change flatInverseTrace B v f x = flatInverseTrace B v t x-flatInverseTrace B v p x at hfB
  change flatInverseTrace R w f x = flatInverseTrace R w t x-flatInverseTrace R w p x at hfR
  change flatInversePair R w f f x = flatInversePair R w t t x -
    2*flatInversePair R w p t x+flatInversePair R w p p x at hpp
  change flatInversePair R w p f x = flatInversePair R w p t x-flatInversePair R w p p x at hpf
  change -(Fintype.card ι : ℝ) = φ x *(flatInverseTrace B v p x+flatInversePair B v p p x) at hB
  change (Fintype.card κ : ℝ) = φ x *(flatInverseTrace R w p x+flatInversePair R w p p x) at hR
  change (Fintype.card κ : ℝ) - Fintype.card ι + φ x * flatInverseTrace B v f x -
      φ x * flatInversePair B v p p x - c*φ x*flatInversePair B v t t x +
      φ x * flatInverseTrace R w f x + 2*φ x*flatInversePair R w p f x +
      φ x * flatInversePair R w f f x = 0
  rw [hfB,hfR,hpp,hpf]
  nlinarith [congrArg (fun z : ℝ => φ x*z) he]

end AffineBernstein
end

end OAI
