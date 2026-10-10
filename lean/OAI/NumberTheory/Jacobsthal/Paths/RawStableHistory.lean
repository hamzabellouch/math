import OAI.NumberTheory.Jacobsthal.Probability.GenuineMarkedVisit

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

variable (P : (n : ℕ) → Set (RawHistory n)) (hP : ∀ n, MeasurableSet (P n))
variable (hExt : ∀ b c, b ≤ c → ∀ h ∈ P b, ∀ᵐ y ∂rawExtension b c h, y ∈ P c)

noncomputable def returnHistoryProperty (b : ℕ) : Set (RawReturnTrace b) :=
  {r | r.2 ∈ P (b+2*(r.1+1))}

include hP in
lemma returnHistoryProperty_measurable (b : ℕ) : MeasurableSet (returnHistoryProperty P b) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact hP _

include hP hExt in
lemma rawReturn_historyProperty (b : ℕ) (h : RawHistory b) (hh : h ∈ P b) :
    ∀ᵐ r ∂rawReturnTraceKernel b h, r ∈ returnHistoryProperty P b := by
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable b n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable b n).aemeasurable (returnHistoryProperty_measurable P hP b)).mpr
  rw [firstReturnHistory,Kernel.restrict_apply]
  exact ae_restrict_of_ae (hExt _ _ (by omega) h hh)

noncomputable def selectedHistoryProperty : Set (Σ t : ℕ, RawReturnTrace t) :=
  {r | r.2 ∈ returnHistoryProperty P r.1}

include hP in
lemma selectedHistoryProperty_measurable : MeasurableSet (selectedHistoryProperty P) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro b
  exact returnHistoryProperty_measurable P hP b

include hP hExt in
lemma lastRawCycle_historyProperty (w : List Bool) : ∀ b c h, h ∈ P b →
    ∀ᵐ r ∂rawMarkedWordKernel b (w++[c]) h, lastRawCycle b w c r ∈ selectedHistoryProperty P := by
  have hBranch (b : ℕ) (c : Bool) (h : RawHistory b) (hh : h ∈ P b) :
      ∀ᵐ r ∂rawBranchReturnKernel b c h, r ∈ returnHistoryProperty P b := by
    rw [rawBranchReturnKernel,Kernel.restrict_apply]
    exact ae_restrict_of_ae (rawReturn_historyProperty P hP hExt b h hh)
  induction w with
  | nil =>
    intro b c h hh
    apply rawMarkedWord_cons_ae b c [] h
      ((selectedHistoryProperty_measurable P hP).preimage (lastRawCycle_measurable [] b c))
    filter_upwards [hBranch b c h hh] with r hr
    exact Eventually.of_forall (fun _ => hr)
  | cons d w ih =>
    intro b c h hh
    apply rawMarkedWord_cons_ae b d (w++[c]) h
      ((selectedHistoryProperty_measurable P hP).preimage (lastRawCycle_measurable (d::w) b c))
    filter_upwards [hBranch b d h hh] with r hr
    exact ih _ c r.2 hr

noncomputable def continuationHistoryProperty (b : ℕ) : Set (RawContinuationTrace b) :=
  {r | Sum.elim (fun h => h ∈ P b) (fun r => r ∈ returnHistoryProperty P b) r}

include hP in
lemma continuationHistoryProperty_measurable (b : ℕ) : MeasurableSet (continuationHistoryProperty P b) :=
  measurableSet_sum_iff.mpr ⟨hP b,returnHistoryProperty_measurable P hP b⟩

include hP hExt in
lemma rawContinuation_historyProperty (b : ℕ) (h : RawHistory b) (hh : h ∈ P b) :
    ∀ᵐ r ∂rawContinuationKernel b h, r ∈ continuationHistoryProperty P b := by
  rw [rawContinuationKernel,Kernel.piecewise_apply]
  split_ifs
  · rw [Kernel.map_apply _ measurable_inl]
    apply (ae_map_iff measurable_inl.aemeasurable (continuationHistoryProperty_measurable P hP b)).mpr
    change ∀ᵐ y ∂Measure.dirac h, y ∈ P b
    exact (ae_dirac_iff (hP b)).mpr hh
  · rw [Kernel.map_apply _ measurable_inr]
    exact (ae_map_iff measurable_inr.aemeasurable (continuationHistoryProperty_measurable P hP b)).mpr
      (rawReturn_historyProperty P hP hExt b h hh)

noncomputable def packedHistoryProperty (a : ℕ) : Set (RawInitialPackedTrace a) :=
  {r | r.2 ∈ P ((a+1)+2*r.1)}

include hP in
lemma packedHistoryProperty_measurable (a : ℕ) : MeasurableSet (packedHistoryProperty P a) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro k
  exact hP _

include hP hExt in
lemma packedInitial_historyProperty (a : ℕ) (h : RawHistory a) (hh : h ∈ P a) :
    ∀ᵐ r ∂packedInitialKernel a h, r ∈ packedHistoryProperty P a := by
  rw [packedInitialKernel,Kernel.map_apply _ (packRawInitialEven_measurable a)]
  apply (ae_map_iff (packRawInitialEven_measurable a).aemeasurable (packedHistoryProperty_measurable P hP a)).mpr
  have hs : ∀ᵐ r ∂rawInitialEvenKernel a h, r ∈ continuationHistoryProperty P (a+1) := by
    rw [rawInitialEvenKernel]
    apply Kernel.ae_comp_of_ae_ae (continuationHistoryProperty_measurable P hP (a+1))
    filter_upwards [hExt a (a+1) (by omega) h hh] with y hy
    exact rawContinuation_historyProperty P hP hExt (a+1) y hy
  filter_upwards [hs] with r hr
  cases r with
  | inl y => exact hr
  | inr y => exact hr

noncomputable def hitHistoryProperty (b : ℕ) : Set (RawMarkedHitTrace b) :=
  {r | lastRawCycle b (List.ofFn r.2.1) true r.2.2 ∈ selectedHistoryProperty P}

include hP in
lemma hitHistoryProperty_measurable (b : ℕ) : MeasurableSet (hitHistoryProperty P b) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro f
  exact (selectedHistoryProperty_measurable P hP).preimage (lastRawCycle_measurable (List.ofFn f) b true)

include hP hExt in
lemma rawRegFirstHit_historyProperty (b : ℕ) (v H : ℝ) (h : RawHistory b) (hh : h ∈ P b) :
    ∀ᵐ r ∂rawRegMarkedFirstHitKernel b v H h, r ∈ hitHistoryProperty P b := by
  rw [rawRegMarkedFirstHitKernel,stateFilter_input]
  split_ifs
  · rw [rawMarkedFirstHitKernel,Kernel.sum_apply,Measure.ae_sum_iff]
    intro n
    rw [Kernel.sum_apply,Measure.ae_sum_iff]
    intro f
    rw [Kernel.map_apply _ (packRawMarkedHitTrace_measurable b n f)]
    apply (ae_map_iff (packRawMarkedHitTrace_measurable b n f).aemeasurable (hitHistoryProperty_measurable P hP b)).mpr
    rw [rawHitWordKernel,Kernel.restrict_apply]
    exact ae_restrict_of_ae (lastRawCycle_historyProperty P hP hExt (List.ofFn f) b true h hh)
  · simp

include hP hExt in
theorem rawEvenHit_historyProperty (a : ℕ) (v H : ℝ) (h : RawHistory a) (hh : h ∈ P a) :
    ∀ᵐ r ∂rawEvenMarkedHitKernel a v H h, rawEvenFinalCycle a r ∈ selectedHistoryProperty P := by
  have hm : MeasurableSet {r | rawEvenFinalCycle a r ∈ selectedHistoryProperty P} :=
    (selectedHistoryProperty_measurable P hP).preimage (rawEvenFinalCycle_measurable a)
  rw [rawEvenMarkedHitKernel]
  apply Kernel.ae_comp_of_ae_ae hm
  filter_upwards [packedInitial_historyProperty P hP hExt a h hh] with r hr
  rcases r with ⟨k,y⟩
  rw [rawEvenHitContinuation,sigmaFamilyKernel_apply]
  apply (ae_map_iff (measurableSigmaMk k).aemeasurable hm).mpr
  have he : ((Kernel.id : Kernel (RawHistory ((a+1)+2*k)) (RawHistory ((a+1)+2*k))) ×ₖ
      rawRegMarkedFirstHitKernel ((a+1)+2*k) v H) y =
      (rawRegMarkedFirstHitKernel ((a+1)+2*k) v H y).map (Prod.mk y) := by
    ext S hS
    rw [Kernel.id_prod_apply' _ _ hS,Measure.map_apply measurable_prodMk_left hS]
  rw [he]
  exact (ae_map_iff measurable_prodMk_left.aemeasurable (hm.preimage (measurableSigmaMk k))).mpr
    (rawRegFirstHit_historyProperty P hP hExt _ v H y hr)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
