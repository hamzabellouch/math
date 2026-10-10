import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualSquare
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualMask

namespace OAI

/-! Exact short/long splitting of the source residual. A packet at
least as long as the reference top cannot stop before an eligible
reference endpoint. The long part is therefore confined to the last
block and its square costs only its one terminal envelope. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem packetResidual_filter_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) (lower upper : ℕ) (cell : ℤ) :
    g.packetResidual packets slope stop base transition lower upper cell =
      g.packetResidual (packets.filter keep) slope stop base transition lower upper cell+
        g.packetResidual (packets.filter fun q => ¬keep q) slope stop base transition lower upper cell := by
  simp only [packetResidual,packetSet,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : keep q <;> simp [hq]

theorem residual_packet_length_lt (g : AngularGrid)
    {w B packetLength referenceLength : ℝ} (hw : 0 < w) (_hB : 0 < B)
    (hp : 0 < packetLength) (hR : 0 < referenceLength)
    (hzero : g.eligible (g.rootWidth/B^2) (w/packetLength) 0)
    {upper : ℕ}
    (hstop : g.lastEligible (g.rootWidth/B^2) (w/packetLength) (div_pos hw hp) < upper)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper) :
    packetLength < referenceLength := by
  have hnot := g.not_eligible_above_lastEligible (g.rootWidth/B^2) (w/packetLength)
    (div_pos hw hp) hzero hstop
  have hpacket : (g.rootWidth/B^2)/(g.branching:ℝ)^upper < w/packetLength :=
    not_le.mp (fun h => hnot ((g.eligible_iff_precision_le _ _ _).mpr h))
  have href := (g.eligible_iff_precision_le _ _ _).mp hreference
  have hprec : w/referenceLength < w/packetLength := href.trans_lt hpacket
  by_contra hn
  exact (not_le.mpr hprec) (div_le_div_of_nonneg_left hw.le hR (not_lt.mp hn))

/-- The physical long-packet residual vanishes at every block whose
upper endpoint is still eligible for the distinguished reference top. -/
theorem long_packet_residual_eq_zero (g : AngularGrid) (packets : Finset σ)
    (slope length : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper) :
    g.packetResidual (packets.filter fun q => ¬length q ≤ referenceLength) slope
      (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
      base transition lower upper cell = 0 := by
  unfold packetResidual
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hq,hstop⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq,_,_⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqp,hlong⟩ := Finset.mem_filter.mp hq
  exact (hlong (g.residual_packet_length_lt hw hB (hlen q) hR (hzero q hqp)
    hstop hreference).le).elim

theorem source_residual_short_long (g : AngularGrid) (packets : Finset σ)
    (slope length : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B : ℝ} (hw : 0 < w) (referenceLength : ℝ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    g.packetResidual packets slope
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
        base transition lower upper cell =
      g.packetResidual (packets.filter fun q => length q ≤ referenceLength) slope
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
        base transition lower upper cell+
      g.packetResidual (packets.filter fun q => ¬length q ≤ referenceLength) slope
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
        base transition lower upper cell :=
  g.packetResidual_filter_split packets slope _ base transition _ lower upper cell

theorem source_shifted_long_residual_support {K : ℕ} (g : AngularGrid)
    (packets : Finset σ) (slope length : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (hK : 0 < K) (shift : Fin K)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (pathSlope : ℝ) :
    let count := g.firstIneligibleShiftedBlock (g.rootWidth/B^2) (w/referenceLength)
      (div_pos hw hR) hK shift
    ∀ j : Fin count, j.val+1 < count →
      g.packetResidual (packets.filter fun q => ¬length q ≤ referenceLength) slope
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
        base transition (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (g.index (ShiftedBlocks.endpoint shift j.val) pathSlope) = 0 := by
  dsimp only
  intro j hj
  exact g.long_packet_residual_eq_zero packets slope length hlen hw hB hR hzero base transition
    _ _ _ (g.eligible_before_firstIneligibleShiftedBlock _ _ _ hK shift hj)

end AngularGrid

/-- Adding a term supported at the last block has no depth loss. -/
theorem terminal_perturbation_square_sum {E : Type*} [NormedAddCommGroup E]
    {count : ℕ} (hc : 0 < count) (full short long : Fin count → E)
    (hsplit : ∀ j, full j = short j+long j)
    (hsupport : ∀ j : Fin count, j.val+1 < count → long j = 0)
    {P R : ℝ} (hshort : (∑ j, ‖short j‖^2) ≤ P)
    (hR : 0 ≤ R) (hterminal : ‖long ⟨count-1,by omega⟩‖ ≤ R) :
    (∑ j, ‖full j‖^2) ≤ 2*P+2*R^2 := by
  have hlong : (∑ j, ‖long j‖^2) ≤ R^2 := by
    rw [Finset.sum_eq_single (⟨count-1,by omega⟩ : Fin count)]
    · nlinarith [norm_nonneg (long ⟨count-1,by omega⟩)]
    · intro j _ hj
      have hj' : j.val+1 < count := by
        have hneq : j.val ≠ count-1 := fun h => hj (Fin.ext h)
        omega
      rw [hsupport j hj',norm_zero,zero_pow (by decide : 2 ≠ 0)]
    · simp
  calc
    _ ≤ ∑ j, (2*‖short j‖^2+2*‖long j‖^2) := by
      apply Finset.sum_le_sum
      intro j _
      have ht : ‖full j‖ ≤ ‖short j‖+‖long j‖ := hsplit j ▸ norm_add_le _ _
      nlinarith [norm_nonneg (full j),norm_nonneg (short j),norm_nonneg (long j),
        sq_nonneg (‖short j‖-‖long j‖)]
    _ = 2*(∑ j, ‖short j‖^2)+2*(∑ j, ‖long j‖^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ _ := by linarith

end LipschitzHilbert

end

end OAI
