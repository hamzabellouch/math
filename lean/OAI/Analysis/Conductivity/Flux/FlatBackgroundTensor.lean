import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusFluxDecay
import OAI.Analysis.Conductivity.Sources.TorusMoments

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def flatBackgroundTensor (s : Fin 3→ℝ) : Mat3 := !![1,0,0;0,s 0,s 1;0,s 1,s 2]

lemma flatBackgroundTensor_symm (s : Fin 3→ℝ) : (flatBackgroundTensor s).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma flatBackgroundTensor_flux {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : Differentiable ℝ u) (j : Fin 2) (x : Coord3) :
    (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j=
      flatModeFlux s (fun y => u y j) x := by
  have hd (i : Fin 3) : gradientColumns (fderiv ℝ u x) i j=
      fderiv ℝ (fun y => u y j) x (flatAxis i) := by
    rw [potential_component_fderiv hu]
    rfl
  ext i
  fin_cases i <;>
    simp [Matrix.col_apply,Fin.sum_univ_three,hd,flatBackgroundTensor,
      flatModeFlux,Fin.reduceFinMk,Matrix.vecMul,dotProduct]

lemma flatBackgroundTensor_source {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) (x : Coord3) :
    symmetricSource (fun _ => flatBackgroundTensor s) u j x=
      flatTensorLaplacian s (fun y => u y j) x := by
  have he : (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j)=
      flatModeFlux s (fun y => u y j) := funext (flatBackgroundTensor_flux (hu.differentiable (by simp)) j)
  unfold symmetricSource
  rw [he,flatModeFlux_divergence (((contDiff_pi.mp hu) j).contDiffAt)]

lemma flatBackgroundTensor_crossFlux {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : Differentiable ℝ u) (x : Coord3) :
    symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x=
      flatCrossFlux s (fun y => u y 0) (fun y => u y 1) x := by
  unfold symmetricCrossFlux flatCrossFlux
  rw [flatBackgroundTensor_flux hu,flatBackgroundTensor_flux hu]

end ScalarConductivity

end
end

end OAI
