import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberMeasurability
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaOrder

namespace OAI

/-! # Entropy order from refinement of conull fibers

A finer future observation need only determine a kernel outside a null
set. Its conditional entropy is then at most the kernel-label entropy;
no support of that kernel on the finer future fibers is required.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma condExp_condExp_of_ae_measurable_sets
    {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {m n : MeasurableSpace Y} (hm : m ≤ mY) (hn : n ≤ mY)
    (hsub : ∀ s, MeasurableSet[m] s →
      ∃ t, MeasurableSet[n] t ∧ s =ᵐ[μ] t)
    (f : Y → ℝ) (hf : Integrable f μ) :
    μ[μ[f | n] | m] =ᵐ[μ] μ[f | m] := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm integrable_condExp
    (fun _ _ _ => integrable_condExp.integrableOn) _
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  obtain ⟨t,ht,hst⟩ := hsub s hs
  calc
    (∫ x in s, μ[f | m] x ∂μ) = ∫ x in s, f x ∂μ := setIntegral_condExp hm hf hs
    _ = ∫ x in t, f x ∂μ := setIntegral_congr_set hst
    _ = ∫ x in t, μ[f | n] x ∂μ := (setIntegral_condExp hn hf ht).symm
    _ = ∫ x in s, μ[f | n] x ∂μ := setIntegral_congr_set hst.symm

theorem conditionalSigmaEntropy_le_of_ae_measurable_sets
    {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    {m n : MeasurableSpace Y} (hm : m ≤ mY) (hn : n ≤ mY)
    (hsub : ∀ s, MeasurableSet[m] s →
      ∃ t, MeasurableSet[n] t ∧ s =ᵐ[μ] t) :
    conditionalSigmaEntropy (mY := mY) μ P n ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  let g (a : α) : Y → ℝ := {y | P y=a}.indicator (fun _ => 1)
  have hg a : Integrable (g a) μ := (integrable_const (1:ℝ)).indicator (hP a)
  have hi (s : MeasurableSpace Y) (hs : s ≤ mY) (a : α) :
      Integrable (fun y => Real.negMulLog ((μ[g a | s]) y)) μ :=
    integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono hs).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} s)
  unfold conditionalSigmaEntropy finiteShannon
  rw [integral_finsetSum _ (fun a _ => hi n hn a),
    integral_finsetSum _ (fun a _ => hi m hm a)]
  apply Finset.sum_le_sum
  intro a _
  have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := μ) (f := μ[g a | n]) hm
    (Real.continuous_negMulLog.upperSemicontinuous.upperSemicontinuousOn _)
    ((conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} n).mono fun _ h => h.1)
    isClosed_Ici integrable_condExp (hi n hn a)
  have htower := condExp_condExp_of_ae_measurable_sets (mY := mY) μ hm hn hsub (g a) (hg a)
  have hle : μ[(fun y => Real.negMulLog ((μ[g a | n]) y)) | m] ≤ᵐ[μ]
      fun y => Real.negMulLog ((μ[g a | m]) y) := by
    filter_upwards [hJ,htower] with y hy ht
    simpa only [Function.comp_def,ht] using hy
  calc
    _ = ∫ y, μ[(fun z => Real.negMulLog ((μ[g a | n]) z)) | m] y ∂μ :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp (hi m hm a) hle

/-- The finer observation can carry extra information: only determination
of the coarser label on a conull set is used. -/
theorem conditionalSigmaEntropy_le_of_conull_fibers
    {Y S T α : Type*} [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S] [MeasurableSpace T] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (G : Y → T) (hG : Measurable G)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E, F x=F y → G x=G y)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy (mY := mY) μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy (mY := mY) μ P (MeasurableSpace.comap G inferInstance) := by
  apply conditionalSigmaEntropy_le_of_ae_measurable_sets μ P hP hG.comap_le hF.comap_le
  intro s hs
  have hsm : MeasurableSet s := hG.comap_le s hs
  let q := μ[s.indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap F inferInstance]
  have hfix : q =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := by
    apply condExp_eq_of_conull_fiber_constant μ F hF _
      ((integrable_const (1:ℝ)).indicator hsm) E hE
    intro x hx y hy hxy
    have hg := hconst x hx y hy hxy
    have hmem : x ∈ s ↔ y ∈ s := by
      obtain ⟨A,_,rfl⟩ := hs
      change G x ∈ A ↔ G y ∈ A
      rw [hg]
    change s.indicator (fun _ => (1:ℝ)) x=s.indicator (fun _ => (1:ℝ)) y
    by_cases hxS : x ∈ s
    · simp only [indicator_of_mem hxS,indicator_of_mem (hmem.mp hxS)]
    · simp only [indicator_of_notMem hxS,indicator_of_notMem (fun hyS => hxS (hmem.mpr hyS))]
  have hqm : @Measurable Y ℝ (MeasurableSpace.comap F inferInstance) _ q :=
    stronglyMeasurable_condExp.measurable
  refine ⟨{x | (1/2:ℝ) < q x},measurableSet_lt measurable_const hqm,?_⟩
  filter_upwards [hfix] with x hx
  apply propext
  rw [hx]
  by_cases hsx : x ∈ s <;> norm_num [hsx]

end DukePrimeDegree

end

end OAI
