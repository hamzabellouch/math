import OAI.Probability.SwitchChain.SwitchTV
import OAI.Probability.SwitchChain.MixingTimeFromTV
import OAI.Probability.SwitchChain.InitialTVGraph
import OAI.Probability.SwitchChain.HavelConnectivity

namespace OAI

noncomputable section
namespace Problem315

theorem switch_chain_main_of_spectralGap (n : Nat) (d : Fin n → Nat)
    (hn : 4 ≤ n)
    (hgap : 1 < stateCount n d → hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    (∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧
      (stateCount n d = 1 →
        MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0) ∧
      (1 < stateCount n d → hasSpectralGapAtLeast n d
        ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) := by
  refine ⟨?_, singleton_mixing_conclusion n d, hgap⟩
  by_cases hlarge : 1 < stateCount n d
  · exact polynomial_mixing_of_tv_bound n d hn
      (switch_chain_tv_bound_of_spectralGap n d hn (hgap hlarge))
  · have hzero : MixedAt n d 0 :=
      (mixedAt_zero_iff_stateCount_le_one n d).mpr (by omega)
    obtain ⟨h, hh⟩ := exists_mixingTime_le_of_mixedAt n d 0 hzero
    exact ⟨h, hh.trans (Nat.zero_le _)⟩

end Problem315

end

end OAI
