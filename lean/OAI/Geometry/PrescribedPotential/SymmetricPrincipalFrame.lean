import Mathlib
import OAI.Geometry.PrescribedPotential.FrozenPoisson

namespace OAI

/-! Symmetric Principal Frame. -/

section

 

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
open EllipticKernel FrozenPoisson
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]

def principalApply (e : OrthonormalBasis ι ℝ E) (L : SecondOrder E)
    (H : E →L[ℝ] E →L[ℝ] F) : F :=
  ∑ i, ∑ j, ((L (rankTwo (e i) (e j))+L (rankTwo (e j) (e i)))/2) • H (e i) (e j)

lemma rankOne_add (v w : E) : rankOne (v+w) = rankOne v+rankOne w+rankTwo v w+rankTwo w v := by
  ext x y
  simp only [rankOne,rankTwo,_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    realInner_apply,inner_add_left,_root_.smul_apply,smul_eq_mul]
  ring

lemma principal_coefficient_gram (L : SecondOrder E) (T : E →L[ℝ] E)
    (h : ∀ v, L (rankOne v) = ‖T v‖^2) (v w : E) :
    (L (rankTwo v w)+L (rankTwo w v))/2 = inner ℝ (T v) (T w) := by
  have hh := h (v+w)
  rw [rankOne_add] at hh
  simp only [map_add,h] at hh
  rw [norm_add_sq_real] at hh
  linarith only [hh]

lemma bilinear_basis_expansion (e : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    H v w = ∑ i, ∑ j, (inner ℝ (e i) v * inner ℝ (e j) w) • H (e i) (e j) := by
  conv_lhs => rw [← e.sum_repr' v,← e.sum_repr' w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [mul_comm]

lemma principalApply_gram [CompleteSpace E] (e : OrthonormalBasis ι ℝ E)
    (L : SecondOrder E) (T : E →L[ℝ] E) (h : ∀ v, L (rankOne v) = ‖T v‖^2)
    (H : E →L[ℝ] E →L[ℝ] F) :
    principalApply e L H = ∑ k, H (T.adjoint (e k)) (T.adjoint (e k)) := by
  simp only [principalApply,principal_coefficient_gram L T h]
  conv_rhs => arg 2; ext k; rw [bilinear_basis_expansion e H]
  calc
    _ = ∑ i, ∑ j, (∑ k, inner ℝ (e i) (T.adjoint (e k))*inner ℝ (e j) (T.adjoint (e k))) • H (e i) (e j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [ContinuousLinearMap.adjoint_inner_right]
      rw [← e.sum_inner_mul_inner (T (e i)) (T (e j))]
      exact sum_congr rfl (fun k _ => by rw [real_inner_comm (e k) (T (e j))])
    _ = _ := by
      simp only [Finset.sum_smul]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]

lemma principalApply_symmetric (e : OrthonormalBasis ι ℝ E) (L : SecondOrder E)
    (H : E →L[ℝ] E →L[ℝ] F) (hH : ∀ v w, H v w = H w v) :
    principalApply e L H = ∑ i, ∑ j, L (rankTwo (e i) (e j)) • H (e i) (e j) := by
  have he : (∑ i, ∑ j, L (rankTwo (e j) (e i)) • H (e i) (e j)) =
      ∑ i, ∑ j, L (rankTwo (e i) (e j)) • H (e i) (e j) := by
    rw [Finset.sum_comm]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => congrArg (fun v : F => L (rankTwo (e i) (e j)) • v) (hH _ _)))
  simp only [principalApply,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,mul_smul,add_smul,Finset.sum_add_distrib,← Finset.smul_sum]
  rw [he]
  module

end HigherJet

end
end

end OAI
