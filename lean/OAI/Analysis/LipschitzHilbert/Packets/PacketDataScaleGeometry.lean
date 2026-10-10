import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity
import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals
import OAI.Analysis.LipschitzHilbert.Geometry.SourceScalePacking

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem length_antitone (P : PacketLatticeData N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

theorem precision_monotone (P : PacketLatticeData N κ Label Item) (w : ℝ) (hw : 0 ≤ w) :
    Monotone (fun j => w / P.length j) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hw (P.length_pos j) (P.length_antitone hij)

theorem stopping_antitone (P : PacketLatticeData N κ Label Item) (grid : AngularGrid)
    (cutoff w : ℝ) (hw : 0 < w)
    (hstart : ∀ j, grid.eligible cutoff (w / P.length j) 0) :
    Antitone (fun j => grid.lastEligible cutoff (w / P.length j) (div_pos hw (P.length_pos j))) := by
  intro i j hij
  exact grid.lastEligible_antitone_precision cutoff (w / P.length i) (w / P.length j)
    (div_pos hw (P.length_pos i)) (div_pos hw (P.length_pos j))
    (P.precision_monotone w hw.le hij) (hstart i) (hstart j)


theorem length_scale_gap (i j : Fin N) (gap : ℕ) (hgap : i.val+gap≤j.val) :
    (2:ℝ)^gap*P.length j≤P.length i := by
  have he : (2:ℝ)^(i.val+gap)≤(2:ℝ)^j.val :=
    pow_le_pow_right₀ (by norm_num) hgap
  rw [pow_add] at he
  unfold length
  apply (le_div_iff₀ (pow_pos (by norm_num) _)).mpr
  calc
    _ = (P.topLength*((2:ℝ)^i.val*2^gap))/2^j.val := by ring
    _ ≤ P.topLength := (div_le_iff₀ (pow_pos (by norm_num) _)).mpr
      (mul_le_mul_of_nonneg_left he P.topLength_pos.le)

end LipschitzHilbert.PacketLatticeData

end

end OAI
