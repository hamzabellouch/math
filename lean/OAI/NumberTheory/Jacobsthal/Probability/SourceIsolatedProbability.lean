import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCrossingTail
import OAI.NumberTheory.Jacobsthal.Estimates.NonisolatedSelectedOccurrence
import OAI.NumberTheory.Jacobsthal.Partitions.CrossingMeshRate

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceIsolatedProbability
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart SourceSelectedCompactOccupation SourceCouplingRate
open NonisolatedSelectedOccurrence NonisolatedWordOccurrence GoodCrossingVisit CrossingPrimeBin
open CanonicalCrossingTail CrossingMeshRate ExponentialMesh LowStateHorizon SourceSuccessfulTail


theorem source_nonisolated_probability (D theta eps : ℝ) (hD : 0 < D)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (heps : 0 < eps) :
    ∃ κ alpha B₀ w₀ : ℝ,0 < κ ∧ 0 < alpha ∧ alpha ≤ theta ∧ 0 < B₀ ∧ 1 < w₀ ∧
    ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∀ ell : ℝ,∀ start : Node,
      ∀ hs : Valid start.side start.ratio,1 ≤ ell → Real.log B ≤ D*Real.log w →
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 → Consistent start → start.cutoff=B →
      w^start.cutoff=top → ∀ E : Set (List ℕ),
      (∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E → p.node.gap ≤ theta*B ∧
        noIsolatedWord hw htop hxi B alpha (4*theta) p.primes) →
      fullSourceLaw w ell ((Real.log B)^2) start hs (mesh κ w) (sourceHorizon ((Real.log B)^2) B)
        {h | CompactPrefixOccurrence.occurs E _ h} ≤ ENNReal.ofReal eps := by
  obtain ⟨κ,hκ,hCouple⟩ := source_coupling_rate
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ le_rfl D hD
  obtain ⟨T,hT,hTail⟩ := canonical_crossing_tail (eps/2) (by positivity)
  let alpha := isolatedAlpha theta (T+1)
  have ha : 0 < alpha ∧ alpha ≤ theta := isolated_alpha_bounds htheta (by linarith)
  have hEvents := (crossing_mesh_control (show 0 ≤ 5*D^3 by positivity) hκ).and
    (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
      (eventually_le_nhds (show 0 < eps/2 by positivity))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (D^2))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨κ,alpha,max (Real.exp 2) (1/alpha),max WC (max normalizationThreshold W),
    hκ,ha.1,ha.2,(Real.exp_pos _).trans_le (le_max_left _ _),hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hB₀ hw₀ hw top htop xi hxi hxi1 ell start hs hell hcomp hi h199 h23 hc hcut hcap E hE
  have hB : 0 < B := (Real.exp_pos _).trans_le ((le_max_left _ _).trans hB₀)
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr ((le_max_left _ _).trans hB₀)
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have he := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀)
  have hlogw : 1 ≤ Real.log w := (le_max_left _ _).trans he.2.2
  have hscale := UniformBudgetRate.source_scale_bound ((le_max_right _ _).trans he.2.2) hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hrnode := SourceNodeCoordinates.source_node_bounds hB start hi h199 h23 hc hcut
  let N := sourceHorizon ((Real.log B)^2) B
  have hwidth : xi/Real.log w ≤ alpha*B := by
    have hlen : 1/alpha ≤ B := (le_max_right _ _).trans hB₀
    have hmul : 1 ≤ alpha*B := by have hh := (div_le_iff₀ ha.1).mp hlen; nlinarith
    exact (div_le_self hxi.le hlogw).trans (hxi1.trans hmul)
  have hOcc := selected_nonisolated_probability hnorm hell hS0 hscale.1 hrnode.2.1 hs hsS
    hw htop hxi hB htheta htheta1 (by linarith : 1 ≤ T) h199 hc hcut hcap
    (mesh_pos κ w) (mesh_le_one hκ.le w) N (he.1 N hscale.2) hwidth E hE
  have hf := (hC w ((le_max_left _ _).trans hw₀) ell B start hs hell hB hlogB hcomp hrnode.2.1 h23 hc hrnode.2.2.2).1 N le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using he.2.1
  have hf' := hf.trans (ENNReal.ofReal_le_ofReal hfail)
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have htyped : typedState start.side start.ratio hs=Sum.inl s := congrArg Prod.fst hcost
  have ht := hTail (Real.log start.gap) (theta*B) s (by rwa [hsv]) (by rwa [hsv]) N
  rw [← htyped] at ht
  have hh := hOcc.trans (add_le_add hf' ht)
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)] at hh
  simpa only [add_halves] using hh
end NumberTheoryLean.SourceIsolatedProbability


end Erdos970

end OAI
