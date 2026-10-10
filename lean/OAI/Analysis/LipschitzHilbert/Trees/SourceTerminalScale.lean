import OAI.Analysis.LipschitzHilbert.Trees.SourceMassStopping
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseBlocks
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedScales
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableLength

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def firstIneligibleShiftedBlock {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) : ℕ :=
  Nat.find (g.exists_shifted_terminal cutoff precision hp hK σ)

theorem firstIneligibleShiftedBlock_spec {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ¬g.eligible cutoff precision
      (ShiftedBlocks.endpoint σ (g.firstIneligibleShiftedBlock cutoff precision hp hK σ)) :=
  Nat.find_spec (g.exists_shifted_terminal cutoff precision hp hK σ)

theorem eligible_before_firstIneligibleShiftedBlock {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) {j : ℕ} (hj : j < g.firstIneligibleShiftedBlock cutoff precision hp hK σ) :
    g.eligible cutoff precision (ShiftedBlocks.endpoint σ j) := by
  exact Classical.not_not.mp
    (Nat.find_min (g.exists_shifted_terminal cutoff precision hp hK σ) hj)

theorem eligible_iff_lt_firstIneligibleShiftedBlock {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) (j : ℕ) :
    g.eligible cutoff precision (ShiftedBlocks.endpoint σ j) ↔
      j < g.firstIneligibleShiftedBlock cutoff precision hp hK σ := by
  constructor
  · intro he
    by_contra hj
    have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_of_not_gt hj)
    exact g.firstIneligibleShiftedBlock_spec cutoff precision hp hK σ
      (g.eligible_of_le hp.le hlevel he)
  · exact g.eligible_before_firstIneligibleShiftedBlock cutoff precision hp hK σ

theorem firstIneligibleShiftedBlock_pos {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) (hzero : g.eligible cutoff precision 0) :
    0 < g.firstIneligibleShiftedBlock cutoff precision hp hK σ := by
  by_contra hn
  have hz : g.firstIneligibleShiftedBlock cutoff precision hp hK σ = 0 := by omega
  have hs := g.firstIneligibleShiftedBlock_spec cutoff precision hp hK σ
  apply hs
  simpa only [hz,ShiftedBlocks.endpoint_zero] using hzero

/-- Even the terminal block, whose upper endpoint need no longer be
eligible, has line window at most the original top length. Eligibility is
only used at the lower endpoint and the block width jump is at most B. -/
theorem source_block_line_scale_le_length (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    (j : ℕ) {w length : ℝ} (hw : 0 < w) (hlength : 0 < length)
    (he : g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/length)
      (ShiftedBlocks.endpoint σ j)) :
    sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) ≤ length := by
  let B := SourceParameters.branching L
  let R := SourceParameters.step L^(1/2:ℝ)
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hB : 1 ≤ B := one_le_pow₀ hG
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hR : 1 ≤ R := Real.one_le_rpow hG (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hwidth : g.width lower ≤ B*g.width upper :=
    (g.source_shifted_width_bounds L hbranch hK σ j).2
  have hden : g.width lower ≤ B^2*(g.width upper*R) := by
    have hb2 : B ≤ B^2 := by nlinarith
    calc
      _ ≤ B*g.width upper := hwidth
      _ ≤ B^2*g.width upper := mul_le_mul_of_nonneg_right hb2 (g.width_pos upper).le
      _ ≤ (B^2*g.width upper)*R :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg B) (g.width_pos upper).le) hR
      _ = _ := by ring
  have hlengthBound := g.source_eligible_length_lower hw hB0 hlength lower he
  calc
    sourceLineScale g L w upper = w/(g.width upper*R) := rfl
    _ ≤ B^2*w/g.width lower := by
      apply (div_le_div_iff₀ (mul_pos (g.width_pos upper) hR0) (g.width_pos lower)).mpr
      calc
        w*g.width lower ≤ w*(B^2*(g.width upper*R)) :=
          mul_le_mul_of_nonneg_left hden hw.le
        _ = (B^2*w)*(g.width upper*R) := by ring
    _ ≤ length := hlengthBound

/-- The concrete reverse grid ending at the first ineligible endpoint
satisfies the width hypothesis of the weighted path integral. -/
theorem source_first_terminal_grid_width (g : AngularGrid) (L origin : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    {w length : ℝ} (hw : 0 < w) (hlength : 0 < length)
    (hzero : g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/length) 0) :
    let count := g.firstIneligibleShiftedBlock (g.rootWidth/(SourceParameters.branching L)^2)
      (w/length) (div_pos hw hlength) hK σ
    (sourceReverseLineGrid g L origin hw σ count).width ≤ length := by
  dsimp only
  let count := g.firstIneligibleShiftedBlock (g.rootWidth/(SourceParameters.branching L)^2)
    (w/length) (div_pos hw hlength) hK σ
  have hc : 0 < count := g.firstIneligibleShiftedBlock_pos _ _ _ hK σ hzero
  have he := g.eligible_before_firstIneligibleShiftedBlock
    (g.rootWidth/(SourceParameters.branching L)^2) (w/length)
    (div_pos hw hlength) hK σ (show count-1 < count by omega)
  have hscale := g.source_block_line_scale_le_length L hbranch hK σ (count-1) hw hlength he
  have hcEq : count-1+1 = count := by omega
  change sourceLineScale g L w (ShiftedBlocks.endpoint σ count) ≤ length
  simpa only [hcEq] using hscale

end LipschitzHilbert.AngularGrid

end

end OAI
