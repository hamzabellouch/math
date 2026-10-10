import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualSplit

namespace OAI

/-! The fixed reference packet collection from §§8 and 10 contains
every short residual packet. Positive per-length reference envelopes
therefore dominate the actual block envelopes by subset summation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def sourceReferencePackets {σ : Type*} (packets : Finset σ)
    (length angle : σ → ℝ) (referenceLength referenceSlope cone w : ℝ) : Finset σ :=
  packets.filter (fun q => length q ≤ referenceLength ∧
    |angle q-referenceSlope| ≤ cone*(w/length q))

def referenceScaleEnvelope {σ : Type*} {N : ℕ} (Q : Finset σ)
    (lengthIndex : σ → Fin N) (envelope : σ → ℝ) (k : Fin N) : ℝ :=
  ∑ q ∈ Q.filter (fun q => lengthIndex q = k), envelope q

theorem referenceScaleEnvelope_nonneg {σ : Type*} {N : ℕ} (Q : Finset σ)
    (lengthIndex : σ → Fin N) (envelope : σ → ℝ) (h : ∀ q ∈ Q, 0 ≤ envelope q)
    (k : Fin N) : 0 ≤ referenceScaleEnvelope Q lengthIndex envelope k := by
  exact Finset.sum_nonneg (fun q hq => h q (Finset.mem_filter.mp hq).1)

theorem referenceScaleEnvelope_sum {σ : Type*} {N : ℕ} (Q : Finset σ)
    (lengthIndex : σ → Fin N) (envelope : σ → ℝ) :
    (∑ k, referenceScaleEnvelope Q lengthIndex envelope k) = ∑ q ∈ Q, envelope q := by
  exact Finset.sum_fiberwise Q lengthIndex envelope

theorem referenceScaleEnvelope_domination {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (P Q : Finset σ) (lengthIndex : σ → Fin N) (value : σ → E)
    (error main : σ → ℝ) (hPQ : P ⊆ Q)
    (herror : ∀ q ∈ Q, 0 ≤ error q) (hmain : ∀ q ∈ Q, 0 ≤ main q)
    (hvalue : ∀ q ∈ P, ‖value q‖ ≤ error q+main q) (k : Fin N) :
    (∑ q ∈ P.filter (fun q => lengthIndex q = k), ‖value q‖) ≤
      referenceScaleEnvelope Q lengthIndex error k+referenceScaleEnvelope Q lengthIndex main k := by
  calc
    _ ≤ ∑ q ∈ P.filter (fun q => lengthIndex q = k), (error q+main q) :=
      Finset.sum_le_sum (fun q hq => hvalue q (Finset.mem_filter.mp hq).1)
    _ ≤ ∑ q ∈ Q.filter (fun q => lengthIndex q = k), (error q+main q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ hPQ
      · intro q hq _
        exact add_nonneg (herror q (Finset.mem_filter.mp hq).1)
          (hmain q (Finset.mem_filter.mp hq).1)
    _ = _ := Finset.sum_add_distrib

namespace AngularGrid

theorem short_residual_subset_reference {σ : Type*} (g : AngularGrid)
    (packets : Finset σ) (assignedSlope length angle : σ → ℝ)
    (hlen : ∀ q, 0 < length q) {w B referenceLength C referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (hangle : ∀ q ∈ packets, |angle q-assignedSlope q| ≤ C*(w/length q))
    (lower upper : ℕ) (hwidth : g.width lower ≤ B*g.width upper) :
    (g.packetSet (packets.filter fun q => length q ≤ referenceLength) assignedSlope
      (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
      lower (g.index lower referenceSlope)).filter
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)) < upper) ⊆
      sourceReferencePackets packets length angle referenceLength referenceSlope (C+B^3) w := by
  intro q hq
  obtain ⟨hq,hupper⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq,hcell,hlower⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqp,hshort⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqp,hshort,
    g.source_parent_residual_cone hw hB (hlen q) (hzero q hqp) ⟨hlower,hupper⟩ hwidth
      hcell (hangle q hqp)⟩

theorem fixedPathResidualPackets_subset_reference {ι σ : Type*} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (length angle : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength C : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (hR : 0 < referenceLength)
    (level : ℕ → ℕ) (count : ℕ) (pathTop : ι)
    (hprecision : precision pathTop = w/referenceLength)
    (hreference : ∀ j < count, g.eligible (g.rootWidth/B^2) (precision pathTop) (level (j+1)))
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (hangle : ∀ q ∈ packets, |angle q-slope (assigned q)| ≤ C*(w/length q)) :
    g.fixedPathResidualPackets tops slope precision (g.rootWidth/B^2) packets assigned
      (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
      level count (slope pathTop) ⊆
      sourceReferencePackets packets length angle referenceLength (slope pathTop) (C+B^3) w := by
  intro q hq
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  obtain ⟨hqp,hshort,hcone⟩ := g.fixedPathResidualPackets_geometry tops slope precision
    packets assigned length angle hlen hw hB0 hR level count pathTop hprecision hreference
    hzero hangle hq
  have hp : B^2 ≤ B^3 := by nlinarith [sq_nonneg (B-1)]
  exact Finset.mem_filter.mpr ⟨hqp,hshort.le,hcone.trans
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hp) (div_nonneg hw.le (hlen q).le))⟩

theorem short_residual_reference_envelope {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (g : AngularGrid) (packets : Finset σ)
    (assignedSlope : σ → ℝ) (length : Fin N → ℝ) (lengthIndex : σ → Fin N)
    (angle : σ → ℝ) (hlen : ∀ k, 0 < length k)
    {w B referenceLength C referenceSlope : ℝ} (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length (lengthIndex q)) 0)
    (hangle : ∀ q ∈ packets, |angle q-assignedSlope q| ≤ C*(w/length (lengthIndex q)))
    (lower upper : ℕ) (hwidth : g.width lower ≤ B*g.width upper)
    (value : σ → E) (error main : σ → ℝ)
    (herror : ∀ q ∈ packets, 0 ≤ error q) (hmain : ∀ q ∈ packets, 0 ≤ main q)
    (hvalue : ∀ q ∈ packets, ‖value q‖ ≤ error q+main q) (k : Fin N) :
    let Q := sourceReferencePackets packets (length ∘ lengthIndex) angle
      referenceLength referenceSlope (C+B^3) w
    let stop := fun k => g.lastEligible (g.rootWidth/B^2) (w/length k) (div_pos hw (hlen k))
    (∑ q ∈ ((g.packetSet (packets.filter fun q => length (lengthIndex q) ≤ referenceLength)
      assignedSlope (stop ∘ lengthIndex) lower (g.index lower referenceSlope)).filter
        (fun q => stop (lengthIndex q) < upper)).filter (fun q => lengthIndex q = k), ‖value q‖) ≤
      referenceScaleEnvelope Q lengthIndex error k+referenceScaleEnvelope Q lengthIndex main k := by
  dsimp only
  apply referenceScaleEnvelope_domination
  · exact g.short_residual_subset_reference packets assignedSlope (length ∘ lengthIndex) angle
      (fun q => hlen (lengthIndex q)) hw hB hzero hangle lower upper hwidth
  · intro q hq
    exact herror q (Finset.mem_filter.mp hq).1
  · intro q hq
    exact hmain q (Finset.mem_filter.mp hq).1
  · intro q hq
    exact hvalue q (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1

end AngularGrid
end LipschitzHilbert

end

end OAI
