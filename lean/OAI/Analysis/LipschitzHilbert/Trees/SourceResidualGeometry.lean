import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualVariation
import OAI.Analysis.LipschitzHilbert.Trees.SourceTerminalScale

namespace OAI

/-! The fixed residual packet collection uses only endpoints at which
the reference top is still eligible. Its packets are shorter than that
top and lie in the reference angular cone. These are the geometric
hypotheses of the existing reference-line variation estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem not_eligible_above_lastEligible (g : AngularGrid)
    (cutoff precision : ℝ) (hp : 0 < precision)
    (hzero : g.eligible cutoff precision 0) {k : ℕ}
    (hk : g.lastEligible cutoff precision hp < k) :
    ¬g.eligible cutoff precision k := by
  intro he
  exact (not_le.mpr hk) ((g.eligible_iff_le_lastEligible cutoff precision hp hzero k).mp he)

/-- The definition with natural subtraction stays monotone even at
empty scales that were already ineligible at level zero. -/
theorem lastEligible_antitone_precision_global (g : AngularGrid) (cutoff p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) :
    g.lastEligible cutoff q hq ≤ g.lastEligible cutoff p hp := by
  unfold lastEligible
  apply Nat.sub_le_sub_right
  apply Nat.find_le
  intro he
  apply Nat.find_spec (g.exists_ineligible cutoff p hp)
  apply (mul_le_mul_of_nonneg_right hpq (by positivity)).trans
  exact he

theorem source_length_stopping_antitone {N : ℕ} (g : AngularGrid)
    (cutoff : ℝ) {w : ℝ} (hw : 0 < w) (length : Fin N → ℝ)
    (hlen : ∀ j, 0 < length j) (horder : Antitone length) :
    Antitone (fun j => g.lastEligible cutoff (w/length j) (div_pos hw (hlen j))) := by
  intro i j hij
  exact g.lastEligible_antitone_precision_global cutoff _ _ (div_pos hw (hlen i))
    (div_pos hw (hlen j))
    (div_le_div_of_nonneg_left hw.le (hlen j) (horder hij))

/-- The precise source stopping map may replace the abstract antitone
map in the already proved cubic-variation bridge. -/
theorem source_length_residual_variation {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (g : AngularGrid) (cutoff : ℝ) {w : ℝ} (hw : 0 < w)
    (length : Fin N → ℝ) (hlen : ∀ j, 0 < length j) (horder : Antitone length)
    (Q : Finset σ) (lengthIndex : σ → Fin N) (value : σ → E) (H : ℕ) :
    let stop := fun j => g.lastEligible cutoff (w/length j) (div_pos hw (hlen j))
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q
    let bands := fun j => ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q
    finiteCubicVariation (packetPrefix raw) H ≤ finiteCubicVariation (packetPartialSum bands) N := by
  exact stopping_prefix_cubic_variation Q lengthIndex _
    (g.source_length_stopping_antitone cutoff hw length hlen horder) value H

/-- A shorter stopping time means a strictly shorter physical packet
than any reference length still eligible at the block endpoint. -/
theorem residual_packet_length_and_cone (g : AngularGrid)
    {w B packetLength referenceLength C packetSlope assignedSlope referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B) (hp : 0 < packetLength) (hR : 0 < referenceLength)
    (hzero : g.eligible (g.rootWidth/B^2) (w/packetLength) 0)
    {upper : ℕ}
    (hstop : g.lastEligible (g.rootWidth/B^2) (w/packetLength) (div_pos hw hp) < upper)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper)
    (hcell : g.index upper assignedSlope = g.index upper referenceSlope)
    (hangle : |packetSlope-assignedSlope| ≤ C*(w/packetLength)) :
    packetLength < referenceLength ∧
      |packetSlope-referenceSlope| ≤ (C+B^2)*(w/packetLength) := by
  have hnot := g.not_eligible_above_lastEligible (g.rootWidth/B^2) (w/packetLength)
    (div_pos hw hp) hzero hstop
  have hpacket : (g.rootWidth/B^2)/(g.branching:ℝ)^upper < w/packetLength := by
    exact not_le.mp (fun h => hnot ((g.eligible_iff_precision_le _ _ _).mpr h))
  have href := (g.eligible_iff_precision_le _ _ _).mp hreference
  have hprec : w/referenceLength < w/packetLength := href.trans_lt hpacket
  have hlen : packetLength < referenceLength := by
    by_contra hn
    have hle := div_le_div_of_nonneg_left hw.le hR (not_lt.mp hn)
    exact (not_le.mpr hprec) hle
  have hwidth : g.width upper < B^2*(w/packetLength) := by
    have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^upper = g.width upper/B^2 := by
      unfold width
      ring
    rw [heq] at hpacket
    have h := (div_lt_iff₀ (sq_pos_of_pos hB)).mp hpacket
    simpa only [mul_comm] using h
  refine ⟨hlen,?_⟩
  calc
    |packetSlope-referenceSlope| ≤ |packetSlope-assignedSlope|+|assignedSlope-referenceSlope| :=
      abs_sub_le _ _ _
    _ ≤ C*(w/packetLength)+g.width upper := add_le_add hangle (g.same_cell_diameter upper hcell)
    _ ≤ C*(w/packetLength)+B^2*(w/packetLength) := add_le_add le_rfl hwidth.le
    _ = _ := by ring

/-- Membership in the actual fixed residual collection supplies the
child-cell condition and the strictly later eligible endpoint. -/
theorem fixedPathResidualPackets_geometry {ι σ : Type*} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (length angle : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength C : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (level : ℕ → ℕ) (count : ℕ) (pathTop : ι)
    (hprecision : precision pathTop = w/referenceLength)
    (hreference : ∀ j < count, g.eligible (g.rootWidth/B^2) (precision pathTop) (level (j+1)))
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (hangle : ∀ q ∈ packets, |angle q-slope (assigned q)| ≤ C*(w/length q))
    {q : σ}
    (hq : q ∈ g.fixedPathResidualPackets tops slope precision (g.rootWidth/B^2)
      packets assigned (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q)
        (div_pos hw (hlen q))) level count (slope pathTop)) :
    q ∈ packets ∧ length q < referenceLength ∧
      |angle q-slope pathTop| ≤ (C+B^2)*(w/length q) := by
  obtain ⟨hqp,j,hj,hstop,hchild⟩ := Finset.mem_filter.mp hq
  have hcell := ((g.mem_cellTops _ _ _ _ _ _ _).mp hchild).2.1
  have href := hreference j hj
  rw [hprecision] at href
  exact ⟨hqp,g.residual_packet_length_and_cone hw hB (hlen q) hR (hzero q hqp)
    hstop.2 href hcell (hangle q hqp)⟩

/-- The source uses all and only blocks preceding its first ineligible
endpoint. Thus the residual family is fixed before mass stopping or
evaluation of any spatial point. -/
theorem shifted_residual_collection_geometry {ι σ : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (length angle : σ → ℝ)
    (hlen : ∀ q, 0 < length q)
    {w B referenceLength C : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (hK : 0 < K) (shift : Fin K) (pathTop : ι)
    (hprecision : precision pathTop = w/referenceLength)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (hangle : ∀ q ∈ packets, |angle q-slope (assigned q)| ≤ C*(w/length q)) :
    let terminal := g.firstIneligibleShiftedBlock (g.rootWidth/B^2) (w/referenceLength)
      (div_pos hw hR) hK shift
    ∀ q ∈ g.fixedPathResidualPackets tops slope precision (g.rootWidth/B^2)
      packets assigned (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q)
        (div_pos hw (hlen q))) (ShiftedBlocks.endpoint shift) (terminal-1) (slope pathTop),
      q ∈ packets ∧ length q < referenceLength ∧
        |angle q-slope pathTop| ≤ (C+B^2)*(w/length q) := by
  dsimp only
  intro q hq
  apply g.fixedPathResidualPackets_geometry tops slope precision packets assigned length angle hlen
    hw hB hR (ShiftedBlocks.endpoint shift) _ pathTop hprecision ?_ hzero hangle hq
  intro j hj
  rw [hprecision]
  apply g.eligible_before_firstIneligibleShiftedBlock
  omega

end LipschitzHilbert.AngularGrid

end

end OAI
