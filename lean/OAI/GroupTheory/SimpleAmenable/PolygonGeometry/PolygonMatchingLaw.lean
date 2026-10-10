import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.SuccessfulLawCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonMatchingLaw
open Classical MeasureTheory Filter Set
open scoped Topology

theorem matchingLaw_finite_weights {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {a m : ℕ} (μ : Measure X) [IsProbabilityMeasure μ] (T : Finset X)
    (hT : ∀ᵐx ∂μ,x∈T) (P : X → TrackPolygonPartition a m) :
    ∃(S : Finset (polygonFullGroup a m)) (p : polygonFullGroup a m → ℝ),
      (∀g,0 ≤ p g) ∧ (∀g∉S,p g=0) ∧ (∑g∈S,p g)=1 ∧
      ∀f : polygonFullGroup a m → ℝ,(∑g∈S,p g*f g)=∫x,matchingAverage (P x) f ∂μ := by
  have hmass : (∑x∈T,μ.real {x})=1 := by
    have hh := integral_of_finite_support μ T hT (fun _ => (1:ℝ))
    simpa using hh.symm
  obtain ⟨S,p,hp,hs,hm,ht⟩ := finite_uniform_mixture T (fun x => μ.real {x})
    (fun x => matchingSupport (P x)) (fun _ _ => measureReal_nonneg) hmass
    (fun x _ => matchingSupport_nonempty (P x))
  refine ⟨S,p,hp,hs,hm,?_⟩
  intro f
  rw [integral_of_finite_support μ T hT]
  exact ht f

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem matching_expectation_covariance {η κ : ℝ} {n : ℕ}
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) {δ : ℝ}
    (hc : ObservableClose (jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha)
      M.signals.eight (commonVertexDenominator_pos ha) η κ n)
      ((jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
        (commonVertexDenominator_pos ha) η κ n).map (barrierBitsTransport g)) δ)
    (f : polygonFullGroup a m → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
    let μ := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
      (commonVertexDenominator_pos ha) η κ n
    |(∫b,matchingAverage (M.signals.sampledPartition n b) f ∂μ)-
      (∫b,matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)) ∂μ)| ≤
      2*μ.real {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}+2*δ := by
  dsimp only
  obtain ⟨T,hT⟩ := jointBitFieldLaw_finite_support (a:=a) (m:=m) (barrierEightDirections ha)
    M.signals.eight M.signals.eight_q (commonVertexDenominator_pos ha) η κ n
  apply successful_law_covariance _ T hT (barrierBitsTransport g)
    (jointBitReindex_measurable _ _ g)
    {b | jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}
    (jointFieldSuccess_measurable _ _ n) hc
    (fun b => matchingAverage (M.signals.sampledPartition n b) f)
    (fun b => matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)))
    (fun b => matchingAverage_range _ hf)
    (fun b => matchingAverage_range _ (fun x => hf (g*x)))
  intro b hb hb'
  exact matchingAverage_transport (M.sampledPartition_arrow (sourceDyadicN_one_le n) hQ hB g hg b hb hb') f

end BarrierMenu

theorem polygonFullGroup_finiteTestReiter {a m : ℕ} (ha : 0 < a) :
    FiniteTestReiter (polygonFullGroup a m) := by
  intro F ε hε
  obtain ⟨M⟩ := exists_barrierMenu ha F
  obtain ⟨η,κ,hη,hη₁,hκ,ht⟩ := jointBitFieldLaw_transport (a:=a) (m:=m)
    (barrierEightDirections ha) M.signals.eight (commonVertexDenominator_pos ha) F
    (show 0 < ε/8 by linarith)
  let μ (n : ℕ) := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
    (commonVertexDenominator_pos ha) η κ n
  have hs : ∀ᶠn : ℕ in atTop,(μ n).real
      {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b} < ε/8 :=
    (jointBitFieldLaw_success (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
      (commonVertexDenominator_pos ha) hη hκ).eventually (gt_mem_nhds (by linarith))
  have hscale : ∀ᶠn : ℕ in atTop,M.Q < sourceDyadicN n ∧ M.B ≤ sourceDyadicN n := by
    filter_upwards [sourceDyadic_radius_eventually (max (M.Q+1) M.B)] with n hn
    have hnN : (2:ℝ)^n ≤ sourceDyadicN n := by
      unfold sourceDyadicN
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨lt_of_lt_of_le (by linarith [(le_max_left (M.Q+1) M.B).trans hn]) hnN,
      ((le_max_right (M.Q+1) M.B).trans hn).trans hnN⟩
  obtain ⟨n,hn,hsn,hN⟩ := (ht.and (hs.and hscale)).exists
  obtain ⟨T,hT⟩ := jointBitFieldLaw_finite_support (a:=a) (m:=m) (barrierEightDirections ha)
    M.signals.eight M.signals.eight_q (commonVertexDenominator_pos ha) η κ n
  obtain ⟨S,p,hp,hsupp,hm,havg⟩ := matchingLaw_finite_weights (μ n) T hT (M.signals.sampledPartition n)
  refine ⟨S,p,hp,hsupp,hm,?_⟩
  intro g hg f hf
  rw [havg,havg]
  have hh := M.matching_expectation_covariance hN.1 hN.2 g hg (hn g hg) f hf
  exact hh.trans (by change 2*(μ n).real _+2*(ε/8) ≤ ε; linarith)

end PolygonMatchingLaw

end SimpleAmenable
end
end

end OAI
