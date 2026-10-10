import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_center [IsManifold I2 ∞ T] (F : T → E3) (p : T) :
    surfaceParameter F p ((extChartAt I2 p) p) = F p := by
  simp [surfaceParameter]
omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_smooth [IsManifold I2 ∞ T]
    {F : T → E3} (hF : ContMDiff I2 𝓘(ℝ,E3) ∞ F) (p : T) :
    ContDiffAt ℝ ∞ (surfaceParameter F p) ((extChartAt I2 p) p) := by
  have hh := (contMDiffAt_iff.mp (hF p)).2
  simpa only [surfaceParameter,I2,mfld_simps,chartAt_self_eq,Function.id_comp,contDiffWithinAt_univ] using hh

omit [IsManifold I2 ∞ T] in
lemma surfaceParameter_derivative [IsManifold I2 ∞ T]
    {F : T → E3} (hF : ContMDiff I2 𝓘(ℝ,E3) ∞ F) (p : T) :
    fderiv ℝ (surfaceParameter F p) ((extChartAt I2 p) p) = mfderiv I2 𝓘(ℝ,E3) F p := by
  have hh : (mfderiv I2 𝓘(ℝ,E3) F p : E2 →L[ℝ] E3) =
      fderivWithin ℝ (writtenInExtChartAt I2 𝓘(ℝ,E3) p F) (range I2) ((extChartAt I2 p) p) :=
    ((hF p).mdifferentiableAt (by simp)).mfderiv_abuse
  simp only [surfaceParameter,I2,writtenInExtChartAt,mfld_simps,chartAt_self_eq,
    Function.id_comp,fderivWithin_univ] at hh ⊢
  exact hh.symm

lemma surfaceParameter_maximum {F : T → E3} {p : T}
    (hp : ∀ q : T, ‖F q‖^2 ≤ ‖F p‖^2) :
    IsLocalMax (fun z => ‖surfaceParameter F p z‖^2) ((extChartAt I2 p) p) := by
  apply Filter.Eventually.of_forall
  intro z
  change ‖surfaceParameter F p z‖^2 ≤ ‖surfaceParameter F p ((extChartAt I2 p) p)‖^2
  rw [surfaceParameter_center]
  exact hp ((extChartAt I2 p).symm z)

end CKSSchwarzschild

end

end OAI
