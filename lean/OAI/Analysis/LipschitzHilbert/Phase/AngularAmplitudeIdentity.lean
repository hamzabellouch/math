import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! The actual shared source amplitude is entire on every affine complex
line. Its equal-coordinate value gives exactly the boundary-weighted
packet sum, and its block identity uses the same amplitude for all shifts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

def sourceBoundaryCoefficient (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (N : ℕ) (top : ι) (a : ℝ) (x : X) : ℝ :=
  ∏ j ∈ Finset.range N,
    (g.mass tops slope precision cutoff weight j (g.index j (slope top)) x /
      g.sourceBoundaryMass tops slope precision cutoff weight K gap j
        (g.index (j+1) (slope top)) x)^a

theorem sourcePacketAmplitude_entire_line (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (phase direction : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    Differentiable ℂ (fun z : ℂ => g.sourcePacketAmplitude tops slope precision cutoff
      weight K gap packets assigned stop value (fun j => phase j + z * direction j)
      a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Differentiable.fun_sum
  intro s _
  apply Differentiable.smul _ (differentiable_const _)
  unfold packetPathProduct sourceTransition analyticTransition
  fun_prop

/-- Exact source equation (30), summed over the packets of one root. -/
theorem sourcePacketAmplitude_equal_coordinates (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (x : X) (root : ℤ) :
    ((g.mass tops slope precision cutoff weight 0 root x ^ a : ℝ) : ℂ) •
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value (fun _ => (a : ℂ)) a x 0 root =
      ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop 0 root,
        ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
          (stop s) (assigned s) a x : ℝ) : ℂ) • value s := by
  unfold sourcePacketAmplitude packetAmplitude
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨hsp, hroot, _⟩ := Finset.mem_filter.mp hs
  have heq := g.source_normalized_endpoint tops slope precision cutoff weight hp hw hK gap
    (stop s) (assigned s) (hassigned s hsp) (heligible s hsp) a x
  dsimp only at heq
  rw [hroot] at heq
  simp only [sourcePacketBase, smul_smul]
  rw [← mul_assoc]
  simpa only [sourceBoundaryCoefficient, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun c : ℂ => c • value s) heq

/-- The same family has the exact block decomposition at arbitrary
endpoints. Shift-specific endpoints enter only as arguments here. -/
theorem sourcePacketAmplitude_block (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    {lower upper : ℕ} (hlu : lower ≤ upper) (parent : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      value phase a x lower parent =
    g.packetResidual packets (fun s => slope (assigned s)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper parent +
    ∑ c ∈ g.packetBlockCells packets (fun s => slope (assigned s)) stop lower upper parent,
      g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
        lower upper (g.packetBlockRepresentative packets (fun s => slope (assigned s)) stop
          lower upper parent c) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          value phase a x upper c := by
  exact g.packetAmplitude_canonical_block packets (fun s => slope (assigned s)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x) hlu parent

end LipschitzHilbert.AngularGrid

end

end OAI
