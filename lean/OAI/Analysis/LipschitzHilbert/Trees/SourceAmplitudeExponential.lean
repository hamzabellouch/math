import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeEntire
import OAI.Analysis.LipschitzHilbert.Trees.SourceExponentialIntegral

namespace OAI

/-! The actual source packet path is a single exponential of the sum of
its logarithmic transition ratios. This exact formula is used to integrate
an affine phase slice on sets where those finitely many logs are bounded. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pathLogCombination (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) : ℂ :=
  ∑ j ∈ Finset.Ico lower upper,
    phase j*(Real.log (mass (j+1) (g.index (j+1) slope)/
      boundary j (g.index (j+1) slope)):ℂ)

theorem packetPathProduct_affine_exp (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (offset direction : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) (z : ℂ) :
    g.packetPathProduct (analyticTransition mass boundary (fun j => offset j+z*direction j))
      lower upper slope =
    Complex.exp (g.pathLogCombination mass boundary offset lower upper slope+
      z*g.pathLogCombination mass boundary direction lower upper slope) := by
  unfold packetPathProduct analyticTransition pathLogCombination
  rw [← Complex.exp_sum]
  congr 1
  simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourcePacketAmplitude_affine_exp (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (offset direction : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (z : ℂ) :
    let mass := fun j c => g.mass tops slope precision cutoff weight j c x
    let boundary := fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
      (fun j => offset j+z*direction j) a x level cell =
    ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
      Complex.exp (g.pathLogCombination mass boundary offset level (stop s) (slope (assigned s))+
        z*g.pathLogCombination mass boundary direction level (stop s) (slope (assigned s))) •
        g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x s := by
  intro mass boundary
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact g.packetPathProduct_affine_exp mass boundary offset direction level (stop s) (slope (assigned s)) z

end LipschitzHilbert.AngularGrid

end

end OAI
