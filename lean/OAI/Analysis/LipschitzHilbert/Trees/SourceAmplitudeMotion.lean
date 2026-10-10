import OAI.Analysis.LipschitzHilbert.Estimates.WeightedAmplitudeMotion
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularIdentity
import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeAssembly

namespace OAI

/-! The exact source analytic family inherits motion from its endpoint
weights and original interval packet sums. Different endpoint coefficients
allow the common top mask to be evaluated at each spatial point. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem sourcePacketAmplitude_single_top_motion (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) M) (a : ℝ) (z0 z1 : X)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x0 y0 x1 y1 A D B ε : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff0 jet l u x0 y0‖ ≤ B)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff1 jet l u x1 y1-U (P.rawInterval coeff0 jet l u x0 y0)‖ ≤ ε) :
    let n := fun z j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) z
    let m := fun z j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope top)) z
    let w0 := segmentWeight (n z0) (boundaryLog (n z0) (m z0)) phase a start
    let w1 := segmentWeight (n z1) (boundaryLog (n z1) (m z1)) phase a start
    ‖w1 M‖+(∑ j ∈ Finset.Ico start M, ‖w1 (j+1)-w1 j‖) ≤ A →
    ‖w1 M-w0 M‖+(∑ j ∈ Finset.Ico start M,
      ‖(w1 (j+1)-w0 (j+1))-(w1 j-w0 j)‖) ≤ D →
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
        (fun _ : Fin N => top) stop (fun j => P.rawBand coeff1 jet j x1 y1)
        phase a z1 start (g.index start (slope top))-
      U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
        (fun _ : Fin N => top) stop (fun j => P.rawBand coeff0 jet j x0 y0)
        phase a z0 start (g.index start (slope top)))‖ ≤ A*ε+D*B := by
  dsimp only
  intro hweight hweightdiff
  rw [g.sourcePacketAmplitude_single_top tops slope precision cutoff weight hp hw hK gap
    phase M top htop he a z1 stop hmax]
  rw [g.sourcePacketAmplitude_single_top tops slope precision cutoff weight hp hw hK gap
    phase M top htop he a z0 stop hmax]
  exact P.stopping_amplitude_motion coeff0 coeff1 jet stop hstop start M hstart hmax
    _ _ x0 y0 x1 y1 A D B ε U hB hε hweight hweightdiff hinterval hmotion

/-- Summing the actual single-top motion bounds charges the snapshot
mass of the node, with no loss from the number of eligible tops. -/
theorem sourcePacketAmplitude_node_motion {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (K : ℕ) (gap : ℕ → ℝ) (bands : Finset σ) (stop : ι → σ → ℕ)
    (value0 value1 : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ j ∈ bands, g.eligible cutoff (precision t) (stop t j))
    (phase : ℕ → ℂ) (a : ℝ) (z0 z1 : X) (level : ℕ) (cell : ℤ)
    (U : E →ₗᵢ[ℂ] E) (A C : ℝ) (hA : 0 ≤ A)
    (hw : ∀ t ∈ g.cellTops tops slope precision cutoff level cell, 0 ≤ weight t z0)
    (hC : ∀ t ∈ g.cellTops tops slope precision cutoff level cell, weight t z0 ≤ C)
    (hmotion : ∀ t ∈ g.cellTops tops slope precision cutoff level cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value1 t) phase a z1 level (g.index level (slope t))-
        U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value0 t) phase a z0 level (g.index level (slope t)))‖ ≤
        A*(weight t z0)^4) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
        Prod.fst (fun p => stop p.1 p.2) (fun p => value1 p.1 p.2) phase a z1 level cell-
      U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
        Prod.fst (fun p => stop p.1 p.2) (fun p => value0 p.1 p.2) phase a z0 level cell)‖ ≤
      (A*C^3)*g.mass tops slope precision cutoff weight level cell z0 := by
  rw [g.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    bands stop value1 he phase a z1 level cell,
    g.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    bands stop value0 he phase a z0 level cell, map_sum, ← Finset.sum_sub_distrib]
  exact g.node_amplitude_fourth_envelope tops slope precision cutoff weight _
    level cell z0 A C hA hw hC hmotion

end LipschitzHilbert.AngularGrid

end

end OAI
