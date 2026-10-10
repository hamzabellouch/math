import OAI.NumberTheory.Jacobsthal.Paths.FullPathCompactSelection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSelectedCompactOccupation

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullPathCompactSelection
open PrimeCompactWeights PrimeCorrectionFactor PrimeBinMembership

noncomputable def fullSourceLaw (w ell S : ℝ) (start : Node)
    (hs : Valid start.side start.ratio) (mesh : ℝ) (N : ℕ) :
    Measure (Hist (FlagState (JointState w ell S start)) N) :=
  pathKernel (marked (CouplingData.joint w ell S start (Real.log start.gap) mesh)
    (ActualFlagInvariant.mismatch_measurable mesh)) N
    (fun _ => (FlaggedSourceStart.sourceJoint w ell S start hs,false))

theorem fullSourceLaw_eq {w ell S : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
    (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (mesh : ℝ) (N : ℕ) :
    fullSourceLaw w ell S start hs mesh N = sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N := rfl

theorem source_selected_compact (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (_hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      ∀ mesh : ℝ, ∀ N : ℕ, ∀ A : Set (Hist (FlagState (JointState w ell S start)) N),
        MeasurableSet A →
        (∫⁻ h, A.indicator (fullCompactReward R w B start N) h
          ∂fullSourceLaw w ell S start hs mesh N) ≤
            ENNReal.ofReal C * fullSourceLaw w ell S start hs mesh N A := by
  have hD := compactConstant_pos hR
  have hevent := ((correctionBudget_tendsto_zero d).eventually
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1))).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hevent
  refine ⟨compactConstant R*(R+1),max normalizationThreshold W,by positivity,
    normalizationThreshold_gt_one.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh N A hA
  have hnorm : normalizationThreshold ≤ w := (le_max_left _ _).trans hw
  have hwe := hW w ((le_max_right _ _).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hbound := scaled_compact_bound hR hB hell hellB hlogB hcomp hwe.1 hi h199 h23 hc hcut
  rw [fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS]
  exact selected_compact_history_bound hnorm hell hS0 hscale.1 hr hs hsS
    (by linarith) hD.le hbound mesh N hA

end NumberTheoryLean.SourceSelectedCompactOccupation

end

end Erdos970

end OAI
