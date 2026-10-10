import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeExponential
import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeMeasurable
import OAI.Analysis.LipschitzHilbert.Trees.SourceFiniteExponentialIntegral

namespace OAI

/-! The integrated affine slices of the original source packet amplitude
are entire on bounded logarithmic-coefficient exhaustions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourcePathLog (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (s : ℝ) (x : X) : ℂ :=
  g.pathLogCombination (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    phase lower upper s

theorem measurable_sourcePathLog (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (s : ℝ) :
    Measurable (g.sourcePathLog tops slope precision cutoff weight K gap phase lower upper s) := by
  unfold sourcePathLog pathLogCombination
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (((g.measurable_mass tops slope precision cutoff weight hw _ _).div
    (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap _ _)).log.complex_ofReal)

theorem sourcePacketAmplitude_integral_affine_entire_on
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (offset direction : ℕ → ℂ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (A : Set X) (hA : MeasurableSet A) (V B : σ → ℝ)
    (hV : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, 0 ≤ V s)
    (hB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, 0 ≤ B s)
    (hvV : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤ V s)
    (hcB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePathLog tops slope precision cutoff weight K gap offset level (stop s)
        (slope (assigned s)) x‖ ≤ B s)
    (hdB : ∀ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell, ∀ x ∈ A,
      ‖g.sourcePathLog tops slope precision cutoff weight K gap direction level (stop s)
        (slope (assigned s)) x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b) (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in A, ⟪b x,
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => offset j+z*direction j) a x level cell⟫_ℂ ∂μ) := by
  have heq (z : ℂ) (x : X) := g.sourcePacketAmplitude_affine_exp tops slope precision cutoff
    weight K gap packets assigned stop (value x) offset direction a x level cell z
  simp only at heq
  simp_rw [heq]
  exact source_integral_finite_exponential_pairing_entire_on μ
    (g.packetSet packets (fun s => slope (assigned s)) stop level cell) A hA
    (fun s x => g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s)
    (fun s => g.sourcePathLog tops slope precision cutoff weight K gap offset level (stop s) (slope (assigned s)))
    (fun s => g.sourcePathLog tops slope precision cutoff weight K gap direction level (stop s) (slope (assigned s)))
    (fun s _ => g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)
    (fun s _ => g.measurable_sourcePathLog tops slope precision cutoff weight hw K gap offset level (stop s) _)
    (fun s _ => g.measurable_sourcePathLog tops slope precision cutoff weight hw K gap direction level (stop s) _)
    V B hV hB hvV hcB hdB b hb T hbT

end LipschitzHilbert.AngularGrid

end

end OAI
