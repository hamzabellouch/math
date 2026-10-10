import OAI.NumberTheory.Jacobsthal.Estimates.TwoSidedThresholdOccurrence
import OAI.NumberTheory.Jacobsthal.Estimates.TwoSidedThresholdStability

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReconstructedParentCoupling
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RepresentativeStopGeometry NearbyParentGeometry ActualFlagInvariant
open TwoSidedThresholdStability TwoSidedThresholdArrival TwoSidedThresholdGeometry
open ArrivalKernelGeometry RegeneratingInverseBands ErdosEvenThreshold

def primeNearThreshold (d : ℝ) (z : Node) : Prop :=
  z.side=.even ∧ 1 < z.cutoff ∧ 0 ≤ z.gap-sourceHeight z.cutoff ∧ z.gap-sourceHeight z.cutoff ≤ d

theorem node_parent_reconstruction (z : Node) (hc : Consistent z) (hs : 0 < z.ratio) :
    nextExponent (z.gap+z.cutoff) z.ratio=z.cutoff ∧ nextGap (z.gap+z.cutoff) z.ratio=z.gap := by
  have he : z.cutoff=z.gap/z.ratio := hc
  constructor
  · rw [he]
    unfold nextExponent
    field_simp [hs.ne',show z.ratio+1 ≠ 0 by positivity]
  · rw [he]
    unfold nextGap
    field_simp [hs.ne',show z.ratio+1 ≠ 0 by positivity]

theorem node_near_reconstruction {d : ℝ} (z : Node) (hc : Consistent z) (hs : 0 < z.ratio)
    (hn : primeNearThreshold d z) : z.ratio ∈ nearThreshold (z.gap+z.cutoff) d := by
  have hg := node_parent_reconstruction z hc hs
  change 1 < nextExponent (z.gap+z.cutoff) z.ratio ∧
    0 ≤ thresholdSlack (z.gap+z.cutoff) z.ratio ∧ thresholdSlack (z.gap+z.cutoff) z.ratio ≤ d
  rw [thresholdSlack,hg.1,hg.2]
  exact hn.2

theorem log_reconstructed_parent {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Real.log (r+r/t)=Real.log r+cost t := by
  have he : r+r/t=r*(1+1/t) := by ring
  rw [he,Real.log_mul hr.ne' (show 1+1/t ≠ 0 by positivity)]
  rfl

theorem reconstructed_log_stability {r q t u D h : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ht : (1/2:ℝ) ≤ t) (hu : (1/2:ℝ) ≤ u)
    (hgap : |Real.log r-Real.log q| ≤ D) (hratio : |t-u| ≤ h) :
    |Real.log (r+r/t)-Real.log (q+q/u)| ≤ D+4*h := by
  rw [log_reconstructed_parent hr (by linarith),log_reconstructed_parent hq (by linarith)]
  have he : (Real.log r+cost t)-(Real.log q+cost u)=
      (Real.log r-Real.log q)+(cost t-cost u) := by ring
  rw [he]
  have hc := cost_stability ht hu
  exact (abs_add_le _ _).trans (by linarith)

theorem good_prime_near_thick {w ell S v mesh d : ℝ} {start : Node}
    (hell : 0 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (n : ℕ) (h : History w ell S start) (y : CostState)
    (hgood : GoodAt v mesh n (some h,Sum.inl y))
    (hy2 : 2 ≤ stateRatio y.1) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hexp : Real.exp (4*((n:ℝ)+1)*mesh) ≤ 4/3) (hne : primeNearThreshold d h.node) :
    y ∈ thickArrival v d (3*mesh+3*(Real.exp (4*((n:ℝ)+1)*mesh)-1)) := by
  have hcons := history_consistent hell hr hs hc h
  have hvalid := terminal_valid hs h.admissible
  have hpos : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
  have hratio : 0 < h.node.ratio := valid_pos hvalid
  have hnear := node_near_reconstruction h.node hcons hratio hne
  have htwo : 2 ≤ h.node.ratio := ((thresholdStrip_eq_near _ _).symm ▸ hnear :
    h.node.ratio ∈ thresholdStrip (h.node.gap+h.node.cutoff) d).1
  have he : h.node.cutoff=h.node.gap/h.node.ratio := hcons
  have hg := reconstructed_log_stability (r := h.node.gap) (q := gapValue v y)
    (t := h.node.ratio) (u := stateRatio y.1) hpos (Real.exp_pos _) (by linarith) (by linarith)
    hgood.2.2.2 hgood.2.2.1
  have hpg : |Real.log (h.node.gap+h.node.cutoff)-Real.log (reconstructedParent v y)| ≤
      4*((n:ℝ)+1)*mesh := by
    rw [he]
    change |Real.log (h.node.gap+h.node.gap/h.node.ratio)-
      Real.log (gapValue v y+gapValue v y/stateRatio y.1)| ≤ _
    convert hg using 1
    ring
  have hQ : 0 < reconstructedParent v y := add_pos (Real.exp_pos _) (currentExponent_pos v y)
  have hh := coupled_near_to_thick hQ hy2 hd0 hd1 hnear hgood.2.2.1 hmesh hpg hexp
  have hi : stateSide y.1=.even := hgood.2.1.symm.trans hne.1
  refine ⟨hi,hh.1,?_⟩
  simpa only [add_assoc] using hh.2
end NumberTheoryLean.ReconstructedParentCoupling

end

section

namespace NumberTheoryLean.SourceThresholdCoupling
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport FiniteHistoryOccurrence ActualProcessCoupling ActualCoupledHistories
open ActualSuccessfulHistories ActualFlagInvariant PersistentFailureFlag
open ReconstructedParentCoupling CoupledEvenArrivalSupport CompletedArrivalOccurrence
open TwoSidedThresholdArrival TwoSidedThresholdKernel TwoSidedThresholdOccurrence
open CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

variable {w ell S : ℝ} {start : Node}

def nearPrimeNode (d : ℝ) : ChainState w ell S start → Prop
  | none => False
  | some h => primeNearThreshold d h.node

def primeThresholdOccurs (d : ℝ) (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) : Prop :=
  ∃ j : Fin N,nearPrimeNode d (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.1

theorem primeThresholdOccurs_measurable (d : ℝ) (N : ℕ) :
    MeasurableSet {h : Hist (FlagState (JointState w ell S start)) N | primeThresholdOccurs d N h} := by
  simp only [primeThresholdOccurs,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  have hm : Measurable (fun h : Hist (FlagState (JointState w ell S start)) N =>
      (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.1) := by fun_prop
  exact hm (show MeasurableSet {z : ChainState w ell S start | nearPrimeNode d z} from by trivial)

noncomputable def thresholdPerturbation (mesh : ℝ) (N : ℕ) : ℝ :=
  3*mesh+3*(Real.exp (4*((N:ℝ)+1)*mesh)-1)

theorem thresholdPerturbation_nonneg {mesh : ℝ} (hm : 0 ≤ mesh) (N : ℕ) :
    0 ≤ thresholdPerturbation mesh N := by
  have he : 1 ≤ Real.exp (4*((N:ℝ)+1)*mesh) := Real.one_le_exp_iff.mpr (by positivity)
  unfold thresholdPerturbation
  linarith

theorem thickArrival_mono {v d e f : ℝ} (hef : e ≤ f) : thickArrival v d e ⊆ thickArrival v d f := by
  intro y hy
  exact ⟨hy.1,hy.2.1,hy.2.2.1,hy.2.2.2.1,hy.2.2.2.2.trans (add_le_add le_rfl hef)⟩

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_threshold_transfer (hc : Consistent start)
    {mesh d : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (N : ℕ) (hexp : Real.exp (4*((N:ℝ)+1)*mesh) ≤ 4/3) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → primeThresholdOccurs d N h →
        completedOccurrence (thickArrival (Real.log start.gap) d (thresholdPerturbation mesh N)) N
          (mapHist (fun q => q.1.2) N h) := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N,
    sourceHistory_even_arrivals hw hell hS0 hS hr hs hsS mesh N] with h hgood hsupport
  intro hf hbad
  obtain ⟨j,hj⟩ := hbad
  let k : Finset.Iic N := ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩
  have hg := hgood hf k
  change GoodAt (Real.log start.gap) mesh (j.1+1) ((h k).1.1,(h k).1.2) at hg
  change nearPrimeNode d ((h k).1.1) at hj
  cases hp : (h k).1.1 with
  | none => rw [hp] at hj; exact False.elim hj
  | some p =>
    rw [hp] at hg hj
    cases hy : (h k).1.2 with
    | inr u => rw [hy] at hg; exact False.elim hg
    | inl y =>
      rw [hy] at hg
      have hi : stateSide y.1=.even := hg.2.1.symm.trans hj.1
      have hy2 := hsupport j y hy hi
      have hn : (j.1+1:ℕ) ≤ N := by have := j.isLt; omega
      have hnr : ((j.1+1:ℕ):ℝ) ≤ N := by exact_mod_cast hn
      have harg : 4*((((j.1+1:ℕ):ℝ))+1)*mesh ≤ 4*((N:ℝ)+1)*mesh := by nlinarith
      have hnear := good_prime_near_thick (by linarith : 0 ≤ ell) hr hs hc (j.1+1) p y hg hy2 hmesh hd0 hd1
        ((Real.exp_le_exp.mpr harg).trans hexp) hj
      have herr : 3*mesh+3*(Real.exp (4*((((j.1+1:ℕ):ℝ))+1)*mesh)-1) ≤ thresholdPerturbation mesh N := by
        unfold thresholdPerturbation
        linarith [Real.exp_le_exp.mpr harg]
      refine ⟨j,?_⟩
      change liveMember _ ((h k).1.2)
      rw [hy]
      exact thickArrival_mono herr hnear

theorem source_threshold_probability (hc : Consistent start)
    {mesh d : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (N : ℕ) (hexp : Real.exp (4*((N:ℝ)+1)*mesh) ≤ 4/3) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | primeThresholdOccurs d N h} ≤
      FlaggedSourceStart.sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
        ENNReal.ofReal (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*thresholdPerturbation mesh N)) := by
  let A : Set (Hist (CemeteryKernel.Space CostState) N) :=
    {h | completedOccurrence (thickArrival (Real.log start.gap) d (thresholdPerturbation mesh N)) N h}
  have hA : MeasurableSet A := completedOccurrence_measurable (thickArrival_measurable _ _ _) N
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      h ∈ {h | primeThresholdOccurs d N h} → h ∈ {h | (last N h).2=true} ∪
        (mapHist (fun q => q.1.2) N) ⁻¹' A := by
    filter_upwards [sourceHistory_threshold_transfer hw hell hS0 hS hr hs hsS hc hm hmesh hd0 hd1 N hexp] with h hh
    intro hp
    cases hf : (last N h).2 with
    | false => exact Or.inr (hh hf hp)
    | true => exact Or.inl hf
  have hraw := canonical_thick_occurrence_bound (Real.log start.gap) hd0 (thresholdPerturbation_nonneg hm.le N)
    (FlaggedSourceStart.typedState start.side start.ratio hs) N
  have hrawEN : finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N
      (thickOccurrence (Real.log start.gap) d (thresholdPerturbation mesh N) N) ≤
        ENNReal.ofReal (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*thresholdPerturbation mesh N)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hraw
  calc
    _ ≤ sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
        ({h | (last N h).2=true} ∪ (mapHist (fun q => q.1.2) N) ⁻¹' A) := measure_mono_ae hsub
    _ ≤ sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | (last N h).2=true}+
        sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N ((mapHist (fun q => q.1.2) N) ⁻¹' A) := measure_union_le _ _
    _ ≤ _ := by
      rw [sourceHistory_failure_probability hw hell hS0 hS hr hs hsS mesh N]
      exact add_le_add le_rfl ((source_completed_occurrence_le hw hell hS0 hS hr hs hsS mesh N
        (thickArrival_measurable _ _ _)).trans hrawEN)
end NumberTheoryLean.SourceThresholdCoupling

end

end Erdos970

end OAI
