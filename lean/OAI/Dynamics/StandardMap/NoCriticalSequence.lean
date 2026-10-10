import OAI.Dynamics.StandardMap.TerminalStrict

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy

theorem no_critical_scale_sequence (S:CriticalScaleSequence) : False := by
  obtain ⟨L⟩:=S.exists_limitLaws
  let α:ℝ:=1/(32*1200000004)
  have ha:0<α := by norm_num [α]
  have ha1:α≤1 := by norm_num [α]
  have haS:α*1200000004≤1/16 := by norm_num [α]
  obtain ⟨H,hH,hconv,hint,hbound⟩:=S.exists_terminal_cap_limit L ha ha1
  have hbalance:(∫d:NonAffineArray,capG α d.val ∂L.multi)=H :=
    tendsto_nhds_unique (S.capG_limit_balance L ha.le) (S.capG_prelimit_tendsto L ha.le ha1 hconv)
  have hstrict:=S.terminal_cap_strict L ha.le ha1 hH hbound
  have hrem:=S.remainder_cap_nonpos L ha.le ha1 haS
  rw [S.capG_integral_decomposition L] at hbalance
  linarith

theorem eventually_meanDeficit_small (η:ℝ) (hη:0<η) :
    ∃K:ℝ,0<K ∧ ∀k:ℝ,K≤k → ∀n:ℕ,0<n → meanDeficit k n<η := by
  have hex:∃K:ℝ,∀k:ℝ,K≤k → ∀n:ℕ,0<n → meanDeficit k n<η := by
    by_contra h
    obtain ⟨S⟩:=exists_critical_scale_sequence η hη (badGrowth_arbitrarily_large η h)
    exact no_critical_scale_sequence S
  obtain ⟨K,hK⟩:=hex
  exact ⟨max K 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),fun k hk=>hK k ((le_max_left _ _).trans hk)⟩
end StandardMapEntropy

end OAI
