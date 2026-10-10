import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieProductDifferential
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace OAI

/-! # Nilpotence detected by iterating a group difference map -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nilpotent_fderiv_of_iterate_zero (f : V → V) (hf : DifferentiableAt ℝ f 0)
    (h0 : f 0 = 0) (n : ℕ) (hn : ∀ x, f^[n] x = 0) :
    IsNilpotent (fderiv ℝ f 0) := by
  have hi := hf.hasFDerivAt.iterate h0 n
  have he : f^[n] = fun _ => 0 := funext hn
  rw [he] at hi
  exact ⟨n, hi.unique (hasFDerivAt_const 0 (0 : V))⟩

theorem nilpotent_difference_fderiv
    [Group V] [LieGroup (𝓘(ℝ, V)) ⊤ V]
    (hone : (1 : V) = 0) (f : V → V) (hf : DifferentiableAt ℝ f 0)
    (h0 : f 0 = 0) (n : ℕ)
    (hn : ∀ x, (fun y => f y * (-y))^[n] x = 0) :
    IsNilpotent (fderiv ℝ f 0 - ContinuousLinearMap.id ℝ V) := by
  have hg : HasFDerivAt (fun y : V => -y) (-ContinuousLinearMap.id ℝ V) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : V)).neg
  have hm := HasMFDerivAt.mul_at_one hf.hasFDerivAt.hasMFDerivAt
    hg.hasMFDerivAt
    (h0.trans hone.symm) (by rw [neg_zero]; exact hone.symm)
  have hd : HasFDerivAt (fun y => f y * (-y))
      (fderiv ℝ f 0 - ContinuousLinearMap.id ℝ V) 0 := by
    rw [sub_eq_add_neg]
    exact HasMFDerivAt.hasFDerivAt hm
  have hz : f 0 * (- (0 : V)) = 0 := by rw [h0, neg_zero, ← hone, one_mul]
  have hnil := nilpotent_fderiv_of_iterate_zero _ hd.differentiableAt hz n hn
  rwa [hd.fderiv] at hnil

end PolycyclicRecognition

end

end OAI
