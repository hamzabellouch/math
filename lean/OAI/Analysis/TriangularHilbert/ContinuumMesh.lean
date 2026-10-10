import OAI.Analysis.TriangularHilbert.DiscreteMax

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma gridLift_pi (D : Finset ℤ) {h : ℝ} (hh : 0 < h) {κ : Type uκ}
    (U : κ → D → D → ℂ) (z : ℝ×ℝ) :
    gridLift D h (fun i j k => U k i j) z = fun k => gridLift D h (U k) z := by
  funext k
  simp only [gridLift_eq hh]
  split_ifs <;> rfl

lemma sampled_moment_integral_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (K k) z)) =
      ∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
        (fun m => h*(m:ℤ)) (fun _ _ => K k) i j) := by
  have he (z : ℝ×ℝ) : finiteMoment (fun k => sampledKernelOutput B C h (K k) z) =
      gridLift (sampleIndices h M) h (fun i j => finiteMoment (fun k =>
        kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h (fun m => h*(m:ℤ))
          (fun _ _ => K k) i j)) z := by
    simp_rw [← gridLift_kernelOutput_eq B C hh hsB hsC]
    rw [← gridLift_pi _ hh,gridLift_comp hh _ finiteMoment finiteMoment_zero]
  simp_rw [he]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_cubic_integral_eq (B : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) :
    (∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3) = matrixCubic (sampledMatrix B h M) h := by
  simp_rw [← gridLift_sampled B hh hsB,gridLift_comp hh _ (fun w : ℂ => ‖w‖^3) (by simp)]
  rw [integral_gridLift _ _ _ hh.le]
  rfl

lemma sampled_moment_le (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C h (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B (gridSquare h z)‖^3)+(∫ z : ℝ×ℝ, ‖C (gridSquare h z)‖^3)) := by
  rw [sampled_moment_integral_eq B C hh hsB hsC,sampled_cubic_integral_eq B hh hsB,sampled_cubic_integral_eq C hh hsC]
  exact finiteHardOutput_moment (sampleIndices h M) (sampledMatrix B h M) (sampledMatrix C h M) hh r R hr hb
end
end TriangularHilbert.Heat
end

end OAI
