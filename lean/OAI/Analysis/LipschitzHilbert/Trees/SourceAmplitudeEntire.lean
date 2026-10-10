import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! Every affine slice of the actual source amplitude is entire. All
packet assignments, masks, stopping masses and boundary masses stay fixed
while the complex shift parameters vary. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourcePacketAmplitude_affine_entire (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (offset direction : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    Differentiable ℂ (fun z : ℂ => g.sourcePacketAmplitude tops slope precision cutoff
      weight K gap packets assigned stop value (fun j => offset j+z*direction j)
      a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Differentiable.fun_sum
  intro s _
  apply Differentiable.smul_const
  unfold packetPathProduct
  apply Differentiable.fun_finsetProd
  intro j _
  unfold sourceTransition analyticTransition
  fun_prop

theorem sourcePacketAmplitude_affine_pairing_entire (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (offset direction : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (test : E →L[ℂ] ℂ) :
    Differentiable ℂ (fun z : ℂ => test (g.sourcePacketAmplitude tops slope precision cutoff
      weight K gap packets assigned stop value (fun j => offset j+z*direction j)
      a x level cell)) :=
  test.differentiable.comp (g.sourcePacketAmplitude_affine_entire tops slope precision cutoff
    weight K gap packets assigned stop value offset direction a x level cell)

end LipschitzHilbert.AngularGrid

end

end OAI
