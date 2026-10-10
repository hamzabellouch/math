import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedScales
import OAI.Analysis.LipschitzHilbert.Trees.ResidualBlocks

namespace OAI

/-! Actual residual blocks contain disjoint bands of packet lengths.
Their cardinality is bounded by the logarithm of the source block width
ratio, rather than by the total number of packet scales. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem dyadic_precision_band_card {N : ℕ} (I : Finset (Fin N))
    {c A : ℝ} (hc : 0 < c) (_hA : 0 < A) (R : ℕ)
    (hband : ∀ j ∈ I, A < c*(2:ℝ)^j.val ∧ c*(2:ℝ)^j.val ≤ (2:ℝ)^R*A) :
    I.card ≤ R := by
  by_cases hI : I.Nonempty
  · let i := I.min' hI
    have hi : i ∈ I := I.min'_mem hI
    have hspan (j : Fin N) (hj : j ∈ I) : j.val < i.val+R := by
      by_contra hn
      have hpow : (2:ℝ)^(i.val+R) ≤ (2:ℝ)^j.val :=
        pow_le_pow_right₀ (by norm_num) (not_lt.mp hn)
      have hlower := mul_lt_mul_of_pos_left (hband i hi).1 (by positivity : (0:ℝ)<2^R)
      have hupper := (mul_le_mul_of_nonneg_left hpow hc.le).trans (hband j hj).2
      rw [pow_add] at hupper
      nlinarith
    let idx := fun j : Fin N => j.val
    have hinj : Set.InjOn idx I := fun _ _ _ _ h => Fin.ext h
    have hsubset : I.image idx ⊆ Finset.Ico i.val (i.val+R) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Ico.mpr ⟨I.min'_le j hj,hspan j hj⟩
    calc
      I.card = (I.image idx).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico i.val (i.val+R)).card := Finset.card_le_card hsubset
      _ = R := by simp
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hI,Finset.card_empty]
    exact Nat.zero_le _

def residualLengthSet {N : ℕ} (stop : Fin N → ℕ) (lower upper : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => lower ≤ stop j ∧ stop j < upper)

theorem residualLengthSet_disjoint {N : ℕ} (stop : Fin N → ℕ)
    (level : ℕ → ℕ) (hlevel : StrictMono level) :
    Pairwise (fun i j => Disjoint (residualLengthSet stop (level i) (level (i+1)))
      (residualLengthSet stop (level j) (level (j+1)))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  have hi := (Finset.mem_filter.mp hki).2
  have hj := (Finset.mem_filter.mp hkj).2
  exact hij (AngularGrid.block_of_stop_unique level hlevel hi hj)

namespace AngularGrid

theorem source_residual_precision_window (g : AngularGrid) {w B length : ℝ}
    (hw : 0 < w) (_hB : 0 < B) (hlen : 0 < length)
    (hzero : g.eligible (g.rootWidth/B^2) (w/length) 0)
    {lower upper : ℕ}
    (hstop : lower ≤ g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) ∧
      g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) < upper) :
    g.width upper/B^2 < w/length ∧ w/length ≤ g.width lower/B^2 := by
  have hlow := (g.eligible_iff_le_lastEligible _ _ (div_pos hw hlen) hzero lower).mpr hstop.1
  have hhigh := g.not_eligible_above_lastEligible _ _ (div_pos hw hlen) hzero hstop.2
  have heq (k : ℕ) : (g.rootWidth/B^2)/(g.branching:ℝ)^k = g.width k/B^2 := by
    unfold width
    ring
  constructor
  · rw [← heq upper]
    exact not_le.mp (fun h => hhigh ((g.eligible_iff_precision_le _ _ _).mpr h))
  · rw [← heq lower]
    exact (g.eligible_iff_precision_le _ _ _).mp hlow

/-- The full residual only belongs to the parent cell. Its cone is wider
by one block ratio than the continuing residual's cone. -/
theorem source_parent_residual_cone (g : AngularGrid)
    {w B length C packetSlope assignedSlope referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B) (hlen : 0 < length)
    (hzero : g.eligible (g.rootWidth/B^2) (w/length) 0)
    {lower upper : ℕ}
    (hstop : lower ≤ g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) ∧
      g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) < upper)
    (hwidth : g.width lower ≤ B*g.width upper)
    (hcell : g.index lower assignedSlope = g.index lower referenceSlope)
    (hangle : |packetSlope-assignedSlope| ≤ C*(w/length)) :
    |packetSlope-referenceSlope| ≤ (C+B^3)*(w/length) := by
  have hp := (g.source_residual_precision_window hw hB hlen hzero hstop).1
  have hu : g.width upper < B^2*(w/length) := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hB)).mp hp
    simpa only [mul_comm] using h
  have hl : g.width lower ≤ B^3*(w/length) := by
    calc
      _ ≤ B*g.width upper := hwidth
      _ ≤ B*(B^2*(w/length)) := mul_le_mul_of_nonneg_left hu.le hB.le
      _ = _ := by ring
  calc
    _ ≤ |packetSlope-assignedSlope|+|assignedSlope-referenceSlope| := abs_sub_le _ _ _
    _ ≤ C*(w/length)+g.width lower := add_le_add hangle (g.same_cell_diameter lower hcell)
    _ ≤ C*(w/length)+B^3*(w/length) := add_le_add le_rfl hl
    _ = _ := by ring

/-- A residual block has at most log₂(block ratio) dyadic lengths. The
strict lower precision cutoff also handles a zero-width empty band. -/
theorem source_residual_length_card {N : ℕ} (g : AngularGrid)
    {w B baseLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hlen : 0 < baseLength)
    (lower upper R : ℕ) (hwidth : g.width lower ≤ (2:ℝ)^R*g.width upper)
    (hzero : ∀ j : Fin N, g.eligible (g.rootWidth/B^2) (w/(baseLength/(2:ℝ)^j.val)) 0) :
    let stop := fun j : Fin N => g.lastEligible (g.rootWidth/B^2)
      (w/(baseLength/(2:ℝ)^j.val)) (by positivity)
    (residualLengthSet stop lower upper).card ≤ R := by
  dsimp only
  apply dyadic_precision_band_card _ (div_pos hw hlen)
    (div_pos (g.width_pos upper) (sq_pos_of_pos hB)) R
  intro j hj
  have hjs := (Finset.mem_filter.mp hj).2
  have h := g.source_residual_precision_window hw hB
    (show 0 < baseLength/(2:ℝ)^j.val by positivity) (hzero j) hjs
  have heq : w/(baseLength/(2:ℝ)^j.val) = (w/baseLength)*(2:ℝ)^j.val := by
    field_simp
  rw [heq] at h
  refine ⟨h.1,h.2.trans ?_⟩
  calc
    _ ≤ ((2:ℝ)^R*g.width upper)/B^2 :=
      div_le_div_of_nonneg_right hwidth (sq_nonneg B)
    _ = _ := by ring

theorem source_shifted_residual_length_card {N : ℕ} (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L))
    {w baseLength : ℝ} (hw : 0 < w) (hlen : 0 < baseLength)
    (hzero : ∀ j : Fin N, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
      (w/(baseLength/(2:ℝ)^j.val)) 0) (block : ℕ) :
    let stop := fun j : Fin N => g.lastEligible (g.rootWidth/(SourceParameters.branching L)^2)
      (w/(baseLength/(2:ℝ)^j.val)) (by positivity)
    (residualLengthSet stop (ShiftedBlocks.endpoint shift block)
      (ShiftedBlocks.endpoint shift (block+1))).card ≤
        SourceParameters.stepExponent L*SourceParameters.blockCount L := by
  apply g.source_residual_length_card hw (SourceParameters.branching_pos L) hlen _ _ _ ?_ hzero
  have h := (g.source_shifted_width_bounds L hbranch hK shift block).2
  simpa only [SourceParameters.branching,SourceParameters.step,pow_mul] using h

end AngularGrid
end LipschitzHilbert

end

end OAI
