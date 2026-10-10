import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model
import OAI.Combinatorics.KMedianRecovery.Recovery.Claim
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialRows

namespace OAI

namespace MetricKMedianRecovery

namespace RationalMetricInput

end RationalMetricInput

namespace BinaryRandomizedAlgorithm

end BinaryRandomizedAlgorithm

end MetricKMedianRecovery

namespace MetricKMedianRecovery

end MetricKMedianRecovery
namespace MetricKMedianRecovery
namespace ClippingTransfer
variable {D X : Type*} [PseudoMetricSpace X]

variable [Fintype D]

end ClippingTransfer
end MetricKMedianRecovery

namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

end MetricKMedianRecovery.PriceTransfer
namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

end MetricKMedianRecovery.PriceTransfer

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

namespace Entry
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {i : X}
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}
end Prefix

end PhaseSequence
end MetricKMedianRecovery

namespace MetricKMedianRecovery.LeafTransfer
variable {A X : Type*} [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.LeafTransfer

namespace MetricKMedianRecovery.PhaseParameterTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseParameterTransfer

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseHistoryTransfer

namespace MetricKMedianRecovery.CoincidentCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

variable [Fintype D]

end MetricKMedianRecovery.CoincidentCopy

namespace MetricKMedianRecovery.CoincidentHistory
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.CoincidentHistory

namespace MetricKMedianRecovery.HistoryIsometry
open PhaseHistoryTransfer
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [DecidableEq X] [DecidableEq Y]

end MetricKMedianRecovery.HistoryIsometry

namespace MetricKMedianRecovery.DisablingCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

variable [Fintype D]

end MetricKMedianRecovery.DisablingCopy

namespace MetricKMedianRecovery.DisablingHistory
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.DisablingHistory

namespace MetricKMedianRecovery.HistoryPhaseBound
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.HistoryPhaseBound

namespace MetricKMedianRecovery.UniformDisablingEndpoint
open PhaseHistoryTransfer HistoryPhaseBound
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.UniformDisablingEndpoint

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

end MetricKMedianRecovery.LeafMetric

namespace MetricKMedianRecovery.FreshCopyEndpoints
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.FreshCopyEndpoints

namespace MetricKMedianRecovery.FreshLeafTransfer
open PhaseHistoryTransfer FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.FreshLeafTransfer

namespace MetricKMedianRecovery.CommonPrefixTransfer
open PhaseHistoryTransfer FreshCopyEndpoints FreshLeafTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.CommonPrefixTransfer

namespace MetricKMedianRecovery.MaximalPrefixSelection
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.MaximalPrefixSelection

namespace MetricKMedianRecovery.PhaseMergeSurgery
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeSurgery

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergePath

namespace MetricKMedianRecovery.PhaseMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.PhaseMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseMergeSurgery PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeCompletion

namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergeRefinement PhaseMergeCompletion PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeCompletion

namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergePath PhaseMergeRefinement PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.PriceBisection

end MetricKMedianRecovery.PriceBisection

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  [PseudoMetricSpace Y] [DecidableEq Y]

end MetricKMedianRecovery.PhaseMergeCompletion

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseLengthInterpolation

namespace MetricKMedianRecovery.PriceBisection
open PhaseCountCrossing

end MetricKMedianRecovery.PriceBisection

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseMergeCompletion FreshCopyEndpoints PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseLengthInterpolation

namespace MetricKMedianRecovery.UniformRowDisabling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.UniformRowDisabling

namespace MetricKMedianRecovery.HistoryIsometry
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [DecidableEq X] [DecidableEq Y]

end MetricKMedianRecovery.HistoryIsometry

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseLengthInterpolation

namespace MetricKMedianRecovery.PhaseSensitiveCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement
  PhaseCountCrossing PhaseLengthInterpolation FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseSensitiveCrossing

namespace MetricKMedianRecovery.PhaseFreshAllocation
open PhaseSequence PhaseMergePath PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseFreshAllocation

namespace MetricKMedianRecovery.PhaseParameterAlignment
open PhaseSequence PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseParameterAlignment

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeInvariant

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseCoupledMerge

namespace MetricKMedianRecovery.PhaseLeafCoupling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
  PhaseMergeRefinement PhaseCoupledMerge PhaseLengthInterpolation FreshCopyEndpoints PhaseSensitiveCrossing
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseLeafCoupling

namespace MetricKMedianRecovery.PhaseMergeIteration
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
  PhaseMergeRefinement PhaseCoupledMerge PhaseLeafCoupling
universe uD uX

variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseMergeIteration

namespace MetricKMedianRecovery.PhaseUpperBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

end MetricKMedianRecovery.PhaseUpperBracket

namespace MetricKMedianRecovery.PhaseInitialBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing
  PhaseMergeInvariant PhaseCoupledMerge
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

noncomputable def initial_coupling {loc : D → X} {F : Finset X} {v eta lo hi l u : ℝ}
    {n k a b : ℕ} (hl : lo ≤ l) (hu : u ≤ hi) (hlu : l ≤ u) (hl0 : 0 ≤ l)
    (hwidth : u-l ≤ (Fintype.card D:ℝ)*eta)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j)) (hs : Sandwich k a b)
    (ha : Attains loc F ∅ ∅ v u 0 n a) (hb : Attains loc F ∅ ∅ v l 0 n b) :
    Coupled loc F v eta lo hi 0 n k where
  B := ∅
  P := []
  r := id
  lam := l
  lam' := u
  eps := 0
  a := a
  b := b
  disjoint := (Finset.disjoint_empty_right F)
  low := hl
  high := hu
  price := hlu
  eps_nonneg := le_rfl
  error := by simpa only [mul_zero,add_zero] using hwidth
  inj := Function.injective_id
  fixed := fun _ _ => rfl
  shrink := fun _ _ _ => le_rfl
  loss := fun _ _ _ => by simp only [id_eq,add_zero,le_refl]
  old_prefix := empty_prefix loc F ∅ v l eta hl0 hfar
  new_prefix := by
    simpa only [Finset.image_empty,List.map_nil] using
      empty_prefix loc F ∅ v u eta (hl0.trans hlu) hfar
  sandwich := hs
  new_tail := by simpa only [Finset.image_empty,List.map_nil,after] using ha
  old_tail := hb

theorem produce [Nonempty D] (loc : D → X) (F : Finset X) (v eta : ℝ)
    (lo M : ℚ) (k N total : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heta : 0 ≤ eta) (hprec : (1:ℝ)/2^N ≤ eta)
    (hlo : 0 < lo) (hM : 0 < M) (hN : 3 ≤ N) (hnN : Fintype.card D ≤ N)
    (hk : 2 ≤ k) (hlohi : lo ≤ 8*(Fintype.card D:ℚ)*M)
    (hF : F.Nonempty) (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ)) :
    (∃ c, c ≤ k ∧ Attains loc F ∅ ∅ v (lo:ℝ) 0 total c) ∨
      Solved loc F v eta (lo:ℝ) (8*(Fintype.card D:ℝ)*(M:ℝ)) total k := by
  classical
  let count (s : ℚ) : ℕ := Classical.choose
    (attains_exists loc F ∅ ∅ v (s:ℝ) 0 total (Finset.empty_subset _))
  have hc (s : ℚ) : Attains loc F ∅ ∅ v (s:ℝ) 0 total (count s) :=
    Classical.choose_spec (attains_exists loc F ∅ ∅ v (s:ℝ) 0 total (Finset.empty_subset _))
  by_cases hlow : count lo ≤ k
  · exact Or.inl ⟨count lo,hlow,hc lo⟩
  · right
    have hhigh : count (8*(Fintype.card D:ℚ)*M) ≤ k := by
      apply (PhaseUpperBracket.attains_high loc F v (M:ℝ) hv hvsmall (by exact_mod_cast hM) hdiam (n := total) (c := count (8*(Fintype.card D:ℚ)*M)) ?_).trans
        (by omega : 1 ≤ k)
      simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using hc (8*(Fintype.card D:ℚ)*M)
    obtain ⟨l,u,hl,hlu,hu,hw,hcl,hcu⟩ := PriceBisection.close_bracket count k N lo
      (8*(Fintype.card D:ℚ)*M) hlohi (by omega) hhigh
    have hloR : (0:ℝ) < (lo:ℝ) := by exact_mod_cast hlo
    have hlR : (lo:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    have hluR : (l:ℝ) ≤ (u:ℝ) := by exact_mod_cast hlu
    have huR : (u:ℝ) ≤ 8*(Fintype.card D:ℝ)*(M:ℝ) := by exact_mod_cast hu
    have hlp : (0:ℝ) < (l:ℝ) := hloR.trans_le hlR
    have hup : (0:ℝ) < (u:ℝ) := hlp.trans_le hluR
    by_cases hel : count l = k
    · have hp := empty_prefix loc F ∅ v (l:ℝ) eta hlp.le hfar
      have hs := hp.finish hv hvsmall hlp heta (Finset.disjoint_empty_right F) hlR
        (hluR.trans huR) (hel ▸ hc l)
      simpa only [Nat.zero_add] using hs
    by_cases heu : count u = k
    · have hp := empty_prefix loc F ∅ v (u:ℝ) eta hup.le hfar
      have hs := hp.finish hv hvsmall hup heta (Finset.disjoint_empty_right F) (hlR.trans hluR)
        huR (heu ▸ hc u)
      simpa only [Nat.zero_add] using hs
    have hwidth : (u:ℝ)-(l:ℝ) ≤ (Fintype.card D:ℝ)*eta := by
      have hwr : (u:ℝ)-(l:ℝ) ≤ (1:ℝ)/2^N := by
        have hh : ((u-l:ℚ):ℝ) ≤ ((1/(2:ℚ)^N:ℚ):ℝ) := Rat.cast_le.mpr hw
        push_cast at hh
        exact hh
      have hn : (1:ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
      exact (hwr.trans hprec).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn heta])
    let cou := initial_coupling hlR huR hluR hlp.le hwidth hfar
      (Or.inl ⟨by omega,by omega⟩ : Sandwich k (count u) (count l)) (hc u) (hc l)
    have hhalf : (1:ℝ)/2^(N+1) ≤ eta := by
      apply le_trans _ hprec
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hupper : 8*(Fintype.card D:ℝ)*(M:ℝ) ≤ 8*N*(M:ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (by norm_num)) (by exact_mod_cast hM.le)
    have hs := PhaseMergeIteration.solve v eta (lo:ℝ) (8*(Fintype.card D:ℝ)*(M:ℝ)) M k N
      hv hvsmall hloR heta hhalf hM hN hupper total X loc F 0 hF hdiam cou
    simpa only [Nat.zero_add] using hs

end MetricKMedianRecovery.PhaseInitialBracket

end OAI
