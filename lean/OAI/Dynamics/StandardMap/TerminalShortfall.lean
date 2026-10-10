import OAI.Dynamics.StandardMap.RemainderLaws

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma shortfall_unit_mem (d : DistanceArray) (hu : UnitArray d) (s t : DyadicTime)
    (hst : (s:ℝ)<(t:ℝ)) : arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hl : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hb := hu s t
  rw [abs_of_pos hl] at hb
  have h0 := d.property.1 s t
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hl).mpr hb; linarith
  · have hh := div_nonneg h0 hl.le; linarith
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminal_shortfall_max_integral (i : ℕ) :
    (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂S.terminalLaw i)=1 := by
  rw [terminalLaw,integral_scaleLaw _ _ _ _ _ (S.epsilon_pos i) _
    ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const)]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.add_zero]
  let n := 2^(S.exponent i)
  have hn : 0<n := by dsimp [n]; positivity
  have hs : (n:ℝ)*(0:DyadicTime)=((0:ℤ):ℝ) := by simp
  have ht : (n:ℝ)*(dyadicInt 1:ℝ)=((0:ℤ):ℝ)+(n:ℝ) := by simp
  have he : (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂sampleLaw (S.parameter i) (S.positive i).le n hn)=
      ∫ d,arrayShortfall 0 (dyadicInt 1) d ∂sampleLaw (S.parameter i) (S.positive i).le n hn := by
    rw [integral_sampleLaw _ _ _ _ _ ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const),
      integral_sampleLaw _ _ _ _ _ (continuous_arrayShortfall 0 (dyadicInt 1))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [shortfall_sample_aligned _ _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
    exact max_eq_left (torusShortfall_mem _ (S.positive i).le z 0 n hn).1
  rw [he,integral_shortfall_sample _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
  exact div_self (S.epsilon_pos i).ne'
lemma terminal_shortfall_integrable_bound :
    Integrable (fun d : NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) L.terminal ∧
      (∫ d,arrayShortfall 0 (dyadicInt 1) d.val ∂L.terminal) ≤ 1 := by
  let F : DistanceArray → ℝ := fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0
  have hF : Continuous F := (continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const
  obtain ⟨hi,hb⟩ := vague_integrable_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (fun d => F d.val) (hF.comp continuous_subtype_val) (fun d => le_max_right _ _) 1 (by norm_num)
    (fun i => integrable_nonaffinePart _ F hF) (Eventually.of_forall (fun i => by
      exact (integral_nonaffinePart_le _ F hF (fun d => le_max_right _ _)).trans (S.terminal_shortfall_max_integral i).le))
  have he : (fun d : NonAffineArray => F d.val)=ᵐ[L.terminal] (fun d => arrayShortfall 0 (dyadicInt 1) d.val) := by
    filter_upwards [S.unit_aeterminal L] with d hd
    exact max_eq_left (shortfall_unit_mem d.val hd 0 (dyadicInt 1) (by norm_num)).1
  exact ⟨hi.congr he,by rw [←integral_congr_ae he]; exact hb⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
