import OAI.NumberTheory.Jacobsthal.Probability.RawMarkedVisitGeometry

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

lemma rawMarkedWord_cons_ae (a : ℕ) (b : Bool) (w : List Bool) (h : RawHistory a)
    {P : Set (RawCycleWordTrace a (b::w).length)} (hP : MeasurableSet P)
    (hA : ∀ᵐ r : RawReturnTrace a ∂rawBranchReturnKernel a b h,
      ∀ᵐ t ∂rawMarkedWordKernel (a+2*(r.1+1)) w r.2,
        (@Sigma.mk ℕ (fun n => RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) w.length)
          r.1 (r.2,t)) ∈ P) :
    ∀ᵐ t ∂rawMarkedWordKernel a (b::w) h, t ∈ P := by
  rw [rawMarkedWordKernel]
  apply Kernel.ae_comp_of_ae_ae hP
  filter_upwards [hA] with r hr
  rcases r with ⟨n,y⟩
  rw [sigmaFamilyKernel_apply]
  apply (ae_map_iff (measurableSigmaMk n).aemeasurable hP).mpr
  have he : ((Kernel.id : Kernel (RawHistory (a+2*(n+1))) (RawHistory (a+2*(n+1)))) ×ₖ
      rawMarkedWordKernel (a+2*(n+1)) w) y =
      (rawMarkedWordKernel (a+2*(n+1)) w y).map (Prod.mk y) := by
    ext S hS
    rw [Kernel.id_prod_apply' _ _ hS,Measure.map_apply measurable_prodMk_left hS]
  rw [he]
  exact (ae_map_iff measurable_prodMk_left.aemeasurable (hP.preimage (measurableSigmaMk n))).mpr hr

noncomputable def rawReturnAnchor (a : ℕ) (r : RawReturnTrace a) : CostState :=
  r.2 ⟨a,Finset.mem_Iic.mpr (by omega)⟩

lemma rawReturnAnchor_measurable (a : ℕ) : Measurable (rawReturnAnchor a) := by
  apply measurable_sigma_family
  intro n
  change Measurable (fun h : RawHistory (a+2*(n+1)) => h ⟨a,Finset.mem_Iic.mpr (by omega)⟩)
  exact measurable_pi_apply _

lemma rawBranchReturn_anchor_regenerates (a : ℕ) (b : Bool) (h : RawHistory a)
    (hr : rawLast a h ∈ regenerationSet) :
    ∀ᵐ r ∂rawBranchReturnKernel a b h, rawReturnAnchor a r ∈ regenerationSet := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  apply ae_restrict_of_ae
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable a n).aemeasurable
    (regenerationSet_measurable.preimage (rawReturnAnchor_measurable a))).mpr
  filter_upwards [firstReturnHistory_retains_past a n h] with y hy
  have he := congrFun hy (⟨a,by simp⟩ : Finset.Iic a)
  change y ⟨a,_⟩=rawLast a h at he
  change y ⟨a,_⟩ ∈ regenerationSet
  rw [he]
  exact hr

noncomputable def selectedCycleAnchor (r : Σ t : ℕ, RawReturnTrace t) : CostState :=
  rawReturnAnchor r.1 r.2

lemma selectedCycleAnchor_measurable : Measurable selectedCycleAnchor := by
  apply measurable_sigma_family
  intro t
  exact rawReturnAnchor_measurable t

lemma lastRawCycle_anchor_regenerates (w : List Bool) : ∀ a b h,
    rawLast a h ∈ regenerationSet →
    ∀ᵐ r ∂rawMarkedWordKernel a (w++[b]) h, selectedCycleAnchor (lastRawCycle a w b r) ∈ regenerationSet := by
  induction w with
  | nil =>
    intro a b h hr
    apply rawMarkedWord_cons_ae a b [] h
      (regenerationSet_measurable.preimage (selectedCycleAnchor_measurable.comp (lastRawCycle_measurable [] a b)))
    filter_upwards [rawBranchReturn_anchor_regenerates a b h hr] with r hR
    exact Eventually.of_forall (fun _ => hR)
  | cons c w ih =>
    intro a b h _hr
    apply rawMarkedWord_cons_ae a c (w++[b]) h
      (regenerationSet_measurable.preimage (selectedCycleAnchor_measurable.comp (lastRawCycle_measurable (c::w) a b)))
    filter_upwards [rawBranchReturn_ae_regeneration a c h] with r hR
    exact ih _ b r.2 hR

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

noncomputable def rawHitAnchor (a : ℕ) (r : RawMarkedHitTrace a) : CostState :=
  selectedCycleAnchor (lastRawCycle a (List.ofFn r.2.1) true r.2.2)

lemma rawHitAnchor_measurable (a : ℕ) : Measurable (rawHitAnchor a) := by
  apply measurable_sigma_family
  intro n
  apply measurable_sigma_family
  intro f
  exact selectedCycleAnchor_measurable.comp (lastRawCycle_measurable (List.ofFn f) a true)

lemma rawFirstHit_anchor_regenerates (a : ℕ) (v H : ℝ) (h : RawHistory a)
    (hr : rawLast a h ∈ regenerationSet) :
    ∀ᵐ r ∂rawMarkedFirstHitKernel a v H h, rawHitAnchor a r ∈ regenerationSet := by
  rw [rawMarkedFirstHitKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.sum_apply,Measure.ae_sum_iff]
  intro f
  rw [Kernel.map_apply _ (packRawMarkedHitTrace_measurable a n f)]
  apply (ae_map_iff (packRawMarkedHitTrace_measurable a n f).aemeasurable
    (regenerationSet_measurable.preimage (rawHitAnchor_measurable a))).mpr
  rw [rawHitWordKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (lastRawCycle_anchor_regenerates (List.ofFn f) a true h hr)

lemma rawRegFirstHit_anchor_regenerates (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawRegMarkedFirstHitKernel a v H h, rawHitAnchor a r ∈ regenerationSet := by
  rw [rawRegMarkedFirstHitKernel,stateFilter_input]
  by_cases hr : h ∈ lastRegeneration a
  · rw [ite_eq_left hr]
    exact rawFirstHit_anchor_regenerates a v H h hr
  · simp [hr]

noncomputable def rawEvenHitAnchor (a : ℕ) (r : RawEvenMarkedHitTrace a) : CostState :=
  selectedCycleAnchor (rawEvenFinalCycle a r)

lemma rawEvenHitAnchor_measurable (a : ℕ) : Measurable (rawEvenHitAnchor a) :=
  selectedCycleAnchor_measurable.comp (rawEvenFinalCycle_measurable a)

theorem rawEvenHit_anchor_regenerates (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawEvenMarkedHitKernel a v H h, rawEvenHitAnchor a r ∈ regenerationSet := by
  have hP : MeasurableSet {r | rawEvenHitAnchor a r ∈ regenerationSet} :=
    regenerationSet_measurable.preimage (rawEvenHitAnchor_measurable a)
  rw [rawEvenMarkedHitKernel]
  apply Kernel.ae_comp_of_ae_ae hP
  apply Eventually.of_forall
  rintro ⟨k,y⟩
  rw [rawEvenHitContinuation,sigmaFamilyKernel_apply]
  apply (ae_map_iff (measurableSigmaMk k).aemeasurable hP).mpr
  have he : ((Kernel.id : Kernel (RawHistory ((a+1)+2*k)) (RawHistory ((a+1)+2*k))) ×ₖ
      rawRegMarkedFirstHitKernel ((a+1)+2*k) v H) y =
      (rawRegMarkedFirstHitKernel ((a+1)+2*k) v H y).map (Prod.mk y) := by
    ext S hS
    rw [Kernel.id_prod_apply' _ _ hS,Measure.map_apply measurable_prodMk_left hS]
  rw [he]
  exact (ae_map_iff measurable_prodMk_left.aemeasurable (hP.preimage (measurableSigmaMk k))).mpr
    (rawRegFirstHit_anchor_regenerates _ v H y)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
