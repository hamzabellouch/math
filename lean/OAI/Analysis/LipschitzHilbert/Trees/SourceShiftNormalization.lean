import OAI.Analysis.LipschitzHilbert.Phase.SourceAmplitudeInterpolation
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftSimplex
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedAmplitude

namespace OAI

/-! The root-mass normalization is absorbed into the actual packet
values before interpolation. This identifies the interpolated family
with the normalized moments supplied by the packet tree. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

omit [MeasurableSpace X] [Fintype ι] in
theorem sourceShiftFamily_complex_weight (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (c : X → ℂ) (z : ι → ℂ) (x : X) :
    g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      (fun x s => c x • value x s) phaseIndex a level cell z x =
      c x • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
        value phaseIndex a level cell z x :=
  g.sourcePacketAmplitude_smul_value tops slope precision cutoff weight K gap packets assigned stop
    (value x) (fun j => z (phaseIndex j)) a x level cell (c x)

omit [MeasurableSpace X] [Fintype ι] in
theorem sourceShiftFamily_real_weight (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (c : X → ℝ) (z : ι → ℂ) (x : X) :
    g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      (fun x s => (c x:ℂ) • value x s) phaseIndex a level cell z x =
      c x • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
        value phaseIndex a level cell z x := by
  exact (g.sourceShiftFamily_complex_weight tops slope precision cutoff weight K gap packets assigned
    stop value phaseIndex a level cell (fun x => (c x:ℂ)) z x).trans
    (algebraMap_smul ℂ (c x) _)

theorem sourceShiftFamily_normalized_diagonal_lp [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phaseIndex : ℕ → ι) (a : ℝ) (level : ℕ) (cell : ℤ)
    (n : X → ℝ) (hn : Measurable n) (r p C mu : ℝ)
    (hp1 : 1 < p) (hC : 0 ≤ C) (hmu : 0 ≤ mu)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^r) • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
          value phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x)‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^r) • g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
          value phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x)‖^p ∂μ)^(1/p) ≤ C) :
    let central := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖(n x^r) • central x‖^p) μ ∧
      (∫ x, ‖(n x^r) • central x‖^p ∂μ)^(1/p) ≤ C := by
  let V := fun x s => ((n x^r:ℝ):ℂ) • value x s
  have hV : ∀ s, Measurable (fun x => V x s) :=
    fun s => ((hn.pow_const r).complex_ofReal).smul (hv s)
  have heq (z : ι → ℂ) (x : X) :
      g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
        phaseIndex a level cell z x = (n x^r) •
      g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
        phaseIndex a level cell z x :=
    g.sourceShiftFamily_real_weight tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (fun x => n x^r) z x
  have hi : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ := by
    intro i eta
    simpa only [heq] using hvint i eta
  have hb : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop V
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C := by
    intro i eta
    simpa only [heq] using hvertex i eta
  have h := g.sourceShiftFamily_diagonal_lp μ tops slope precision cutoff weight hp hw hwmeas hK
    gap packets assigned stop V hV hassigned heligible phaseIndex a level cell
    (sourceShiftSimplex mu) (sourceShiftSimplex_convex mu) (mu^2) p C mu
    (fun _ h _ => h.1 _) (fun _ h => sourceShiftSimplex_sq_sum mu _ h) hp1 hC
    (sourceShiftSimplex_vertex hmu) hi hb
  simpa only [heq] using h

end LipschitzHilbert.AngularGrid

end

end OAI
