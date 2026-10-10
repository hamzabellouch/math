import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeBounds
import OAI.Analysis.LipschitzHilbert.Trees.SourceSimplexLpExhaustion

namespace OAI

/-! The original source family satisfies the analytic simplex estimate.
Only its vertex moments remain as input; measurability, analytic slices,
bounded exhaustion, and the full-set limiting argument are proved here. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

def sourceShiftFamily (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (z : ι → ℂ) (x : X) : EuclideanSpace ℂ κ :=
  g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
    (value x) (fun j => z (phaseIndex j)) a x level cell

theorem sourceShiftFamily_diagonal_lp [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phaseIndex : ℕ → ι) (a : ℝ) (level : ℕ) (cell : ℤ)
    (D : Set (ι → ℝ)) (hD : Convex ℝ D) (B p C mu : ℝ)
    (hDpos : ∀ v ∈ D, ∀ i, 0 ≤ v i) (hDsq : ∀ v ∈ D, (∑ i, (v i)^2) ≤ B)
    (hp1 : 1 < p) (hC : 0 ≤ C) (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
          phaseIndex a level cell (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    let central := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop
      value phaseIndex a level cell (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖central x‖^p) μ ∧ (∫ x, ‖central x‖^p ∂μ)^(1/p) ≤ C := by
  let F := g.sourceShiftFamily tops slope precision cutoff weight K gap packets assigned stop value
    phaseIndex a level cell
  let R := g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell
  have hR := g.measurable_sourceAmplitudeRadius tops slope precision cutoff weight hwmeas K gap
    packets assigned stop value hv a level cell
  apply source_simplex_lp_of_exhaustions μ (sourceExhaustion R)
    (sourceExhaustion_measurable R hR) (sourceExhaustion_mono R) (sourceExhaustion_covers R)
    F D hD p C mu hp1 hC
  · intro z
    exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
      packets assigned stop value hv (fun j => z (phaseIndex j)) a level cell
  · intro n z
    refine ⟨∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
      Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖z (phaseIndex j)‖)*(n:ℝ))*(n:ℝ),?_⟩
    intro x hx
    exact g.sourcePacketAmplitude_norm_on_exhaustion tops slope precision cutoff weight K gap
      packets assigned stop value a level cell (fun j => z (phaseIndex j)) n x hx
  · intro n b hb hbB v _ v' _ eta
    obtain ⟨T,hT⟩ := hbB
    let offset := fun j => (v (phaseIndex j):ℂ)+(eta (phaseIndex j):ℂ)*Complex.I
    let direction := fun j => (v' (phaseIndex j):ℂ)-(v (phaseIndex j):ℂ)
    have heq (z : ℂ) : (fun j => phaseTubeLine v v' eta z (phaseIndex j)) =
        (fun j => offset j+z*direction j) := by
      funext j
      dsimp only [phaseTubeLine,offset,direction]
      ring
    change Differentiable ℂ (fun z => ∫ x in sourceExhaustion R n,
      ⟪b x,g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => phaseTubeLine v v' eta z (phaseIndex j)) a x level cell⟫_ℂ ∂μ)
    simp_rw [heq]
    exact g.sourcePacketAmplitude_integral_entire_on_exhaustion μ tops slope precision cutoff weight
      hwmeas K gap packets assigned stop value hv a level cell n offset direction b hb T hT
  · intro n
    refine ⟨Real.exp B*(n:ℝ),?_⟩
    intro v hvD eta x hx
    have hf : ‖F (phaseTubePoint v eta) x‖ ≤ (n:ℝ) := by
      apply (g.sourcePacketAmplitude_norm_le_radius tops slope precision cutoff weight hp hw hK
        gap packets assigned stop value a level cell hassigned heligible
        (fun j => phaseTubePoint v eta (phaseIndex j)) _ x).trans hx
      intro j
      simpa [phaseTubePoint] using hDpos v hvD (phaseIndex j)
    have hd : ‖gaussianPhaseDamping (phaseTubePoint v eta)‖ ≤ Real.exp B := by
      rw [gaussianPhaseDamping_norm]
      apply Real.exp_le_exp.mpr
      exact (sub_le_self _ (Finset.sum_nonneg fun i _ => sq_nonneg (eta i))).trans (hDsq v hvD)
    rw [norm_smul]
    exact mul_le_mul hd hf (norm_nonneg _) (Real.exp_pos _).le
  · exact hvertices
  · exact hvint
  · exact hvertex

end LipschitzHilbert.AngularGrid

end

end OAI
