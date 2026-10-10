import OAI.Analysis.LipschitzHilbert.Trees.SourceMassStopping
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The phase power of every active stopped mass is bounded by the
same subexponential factor. This uses the mass at the initial node,
rather than a separate bound at every generation. -/

noncomputable section
namespace LipschitzHilbert

theorem mass_power_le_exp_sqrt {L n N α : ℝ}
    (hL : 1 ≤ L) (hn : 0 ≤ n) (hN : 0 < N) (hnN : n ≤ N)
    (hα : 1 ≤ α) (hα3 : α ≤ 3) (hlog : Real.log N ≤ 3*L) :
    n^((α-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs2 := Real.sq_sqrt hL0.le
  have he : 0 ≤ (α-1)/Real.sqrt L := div_nonneg (by linarith) hs.le
  apply (Real.rpow_le_rpow hn hnN he).trans
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N*((α-1)/Real.sqrt L) ≤ (3*L)*((α-1)/Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlog he
    _ ≤ (3*L)*(2/Real.sqrt L) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith) hs.le) (by positivity)
    _ = 6*Real.sqrt L := by
      field_simp
      nlinarith

theorem stopped_mass_power_le_exp_sqrt (n : ℕ → ℝ) (count : ℕ) (M L α : ℝ)
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hanti : Antitone n) (hlast : n count ≤ M)
    (hα : 1 ≤ α) (hα3 : α ≤ 3) (hlog : Real.log (n 0) ≤ 3*L)
    {j : ℕ} (hj : j < firstMassStop n count M) :
    n j^((α-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) := by
  have hactive := (firstMassStop_spec n count M hlast).2.2 j hj
  have hnj : 0 < n j := hM.trans_lt hactive
  have hnj0 : n j ≤ n 0 := hanti (Nat.zero_le j)
  exact mass_power_le_exp_sqrt hL hnj.le (hnj.trans_le hnj0) hnj0 hα hα3 hlog

end LipschitzHilbert

end

end OAI
