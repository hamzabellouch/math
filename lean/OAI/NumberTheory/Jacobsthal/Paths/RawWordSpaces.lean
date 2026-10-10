import OAI.NumberTheory.Jacobsthal.Probability.SigmaFamilyKernel

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.CostReturnLaw

noncomputable def firstArrivalMark (s : CostState) : Bool := Sum.elim sourceMark (fun _ => false) s.1

lemma firstArrivalMark_measurable : Measurable firstArrivalMark :=
  (sourceMark_measurable.sumElim measurable_const).comp measurable_fst

noncomputable def returnSignatureMark (s : ReturnSignature) : Bool := firstArrivalMark s.2.1

lemma returnSignatureMark_measurable : Measurable returnSignatureMark :=
  firstArrivalMark_measurable.comp (measurable_fst.comp measurable_snd)

noncomputable def rawReturnMark (a : ℕ) (r : RawReturnTrace a) : Bool := returnSignatureMark (rawReturnSignature a r)

lemma rawReturnMark_measurable (a : ℕ) : Measurable (rawReturnMark a) :=
  returnSignatureMark_measurable.comp (rawReturnSignature_measurable a)

lemma sourceReturnSignature_mark (z : OddCost) (w : SourceCycleWitness) :
    returnSignatureMark (sourceReturnSignature z w)=sourceMark w.1 := rfl

noncomputable def rawBranchReturnKernel (a : ℕ) (b : Bool) : Kernel (RawHistory a) (RawReturnTrace a) :=
  (rawReturnTraceKernel a).restrict ((rawReturnMark_measurable a) (measurableSet_singleton b))

instance rawBranchReturnKernel_isFiniteKernel (a : ℕ) (b : Bool) : IsFiniteKernel (rawBranchReturnKernel a b) := by
  unfold rawBranchReturnKernel
  infer_instance

noncomputable def sourceBranchWitnessKernel (b : Bool) : Kernel OddCost SourceCycleWitness :=
  sourceCycleWitnessKernel.restrict ((sourceMark_measurable.comp measurable_fst) (measurableSet_singleton b))

instance sourceBranchWitnessKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (sourceBranchWitnessKernel b) := by
  unfold sourceBranchWitnessKernel
  infer_instance

theorem rawBranchReturn_signature (a : ℕ) (b : Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawBranchReturnKernel a b h).map (rawReturnSignature a) =
      (sourceBranchWitnessKernel b z).map (sourceReturnSignature z) := by
  have hm : MeasurableSet {s : ReturnSignature | returnSignatureMark s=b} :=
    returnSignatureMark_measurable (measurableSet_singleton b)
  rw [rawBranchReturnKernel,sourceBranchWitnessKernel,Kernel.restrict_apply,Kernel.restrict_apply]
  change ((rawReturnTraceKernel a h).restrict ((rawReturnSignature a) ⁻¹' {s | returnSignatureMark s=b})).map
      (rawReturnSignature a) =
    ((sourceCycleWitnessKernel z).restrict ((sourceReturnSignature z) ⁻¹' {s | returnSignatureMark s=b})).map
      (sourceReturnSignature z)
  rw [← Measure.restrict_map (rawReturnSignature_measurable a) hm,
    ← Measure.restrict_map (sourceReturnSignature_measurable z) hm,rawReturnTrace_signature a h z hz]

lemma sourceBranchWitness_markCost (b : Bool) (z : OddCost) :
    (sourceBranchWitnessKernel b z).map sourceWitnessProjection =
      (completedMarkedKernel z).restrict {y | y.1=b} := by
  have hm : MeasurableSet {y : MarkedOddCost | y.1=b} := measurable_fst (measurableSet_singleton b)
  rw [sourceBranchWitnessKernel,Kernel.restrict_apply]
  change ((sourceCycleWitnessKernel z).restrict (sourceWitnessProjection ⁻¹' {y : MarkedOddCost | y.1=b})).map
    sourceWitnessProjection = _
  rw [← Measure.restrict_map sourceWitnessProjection_measurable hm,sourceCycleWitness_projection]

lemma sourceBranchWitness_endpoint (b : Bool) (z : OddCost) :
    (sourceBranchWitnessKernel b z).map (fun w => w.2.2) = cycleBranchKernel b z := by
  calc
    _ = ((sourceBranchWitnessKernel b z).map sourceWitnessProjection).map Prod.snd :=
      (Measure.map_map measurable_snd sourceWitnessProjection_measurable).symm
    _ = _ := by
      rw [sourceBranchWitness_markCost,cycleBranchKernel,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply]
      rfl

lemma rawBranchReturn_endpoint (a : ℕ) (b : Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawBranchReturnKernel a b h).map (fun r => (rawReturnSignature a r).2.2) =
      (cycleBranchKernel b z).map embedOdd := by
  have he := congrArg (fun μ : Measure ReturnSignature => μ.map (fun s => s.2.2))
    (rawBranchReturn_signature a b h z hz)
  rw [Measure.map_map (g := fun s : ReturnSignature => s.2.2)
      (measurable_snd.comp measurable_snd) (rawReturnSignature_measurable a),
    Measure.map_map (g := fun s : ReturnSignature => s.2.2)
      (measurable_snd.comp measurable_snd) (sourceReturnSignature_measurable z)] at he
  rw [← sourceBranchWitness_endpoint b z,
    Measure.map_map (g := embedOdd) (f := fun w : SourceCycleWitness => w.2.2)
      embedOdd_measurable (measurable_snd.comp measurable_snd)]
  exact he

lemma rawBranchReturn_mass_le_one (a : ℕ) (b : Bool) (h : RawHistory a) :
    rawBranchReturnKernel a b h univ ≤ 1 := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  exact (Measure.restrict_le_self univ).trans (rawReturnTrace_mass_le_one a h)

lemma rawReturnTrace_ae_regeneration (a : ℕ) (h : RawHistory a) :
    ∀ᵐ r ∂rawReturnTraceKernel a h, (rawReturnSignature a r).2.2 ∈ regenerationSet := by
  have hm : MeasurableSet {r : RawReturnTrace a | (rawReturnSignature a r).2.2 ∈ regenerationSet} :=
    regenerationSet_measurable.preimage ((measurable_snd.comp measurable_snd).comp (rawReturnSignature_measurable a))
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable a n).aemeasurable hm).mpr
  filter_upwards [firstReturnHistory_ae_cylinder a n h] with y hy
  exact hy.2

lemma rawBranchReturn_ae_regeneration (a : ℕ) (b : Bool) (h : RawHistory a) :
    ∀ᵐ r ∂rawBranchReturnKernel a b h, (rawReturnSignature a r).2.2 ∈ regenerationSet := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawReturnTrace_ae_regeneration a h)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

@[reducible] def RawCycleWordTrace : ℕ → ℕ → Type
  | a, 0 => RawHistory a
  | a, k+1 => Σ n : ℕ, RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) k

@[reducible] noncomputable def rawCycleWordMeasurable : (a k : ℕ) → MeasurableSpace (RawCycleWordTrace a k)
  | a, 0 => inferInstanceAs (MeasurableSpace (RawHistory a))
  | a, k+1 => by
    letI : ∀ n : ℕ, MeasurableSpace (RawCycleWordTrace (a+2*(n+1)) k) :=
      fun n => rawCycleWordMeasurable (a+2*(n+1)) k
    exact inferInstanceAs (MeasurableSpace (Σ n : ℕ, RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) k))

noncomputable instance (a k : ℕ) : MeasurableSpace (RawCycleWordTrace a k) := rawCycleWordMeasurable a k

abbrev CycleInputSignature := ℝ × ReturnSignature

@[reducible] def CycleWordSignature : ℕ → Type
  | 0 => CostState
  | k+1 => CycleInputSignature × CycleWordSignature k

@[reducible] noncomputable def cycleWordSignatureMeasurable : (k : ℕ) → MeasurableSpace (CycleWordSignature k)
  | 0 => inferInstanceAs (MeasurableSpace CostState)
  | k+1 => by
    letI : MeasurableSpace (CycleWordSignature k) := cycleWordSignatureMeasurable k
    exact inferInstanceAs (MeasurableSpace (CycleInputSignature × CycleWordSignature k))

noncomputable instance (k : ℕ) : MeasurableSpace (CycleWordSignature k) := cycleWordSignatureMeasurable k

noncomputable def rawReturnInputCost (a : ℕ) (r : RawReturnTrace a) : ℝ :=
  (r.2 ⟨a,Finset.mem_Iic.mpr (by omega)⟩).2

lemma rawReturnInputCost_measurable (a : ℕ) : Measurable (rawReturnInputCost a) := by
  apply measurable_sigma_family
  intro n
  change Measurable (fun h : RawHistory (a+2*(n+1)) => (h ⟨a,Finset.mem_Iic.mpr (by omega)⟩).2)
  exact measurable_snd.comp (measurable_pi_apply (⟨a,Finset.mem_Iic.mpr (by omega)⟩ : Finset.Iic (a+2*(n+1))))

noncomputable def rawReturnInputSignature (a : ℕ) (r : RawReturnTrace a) : CycleInputSignature :=
  (rawReturnInputCost a r,rawReturnSignature a r)

lemma rawReturnInputSignature_measurable (a : ℕ) : Measurable (rawReturnInputSignature a) :=
  (rawReturnInputCost_measurable a).prodMk (rawReturnSignature_measurable a)

noncomputable def rawCycleWordSignature : (a k : ℕ) → RawCycleWordTrace a k → CycleWordSignature k
  | a, 0, h => rawLast a h
  | a, k+1, r => (rawReturnInputSignature a (packRawReturnTrace a r.1 r.2.1),
      rawCycleWordSignature (a+2*(r.1+1)) k r.2.2)

lemma rawCycleWordSignature_measurable (k : ℕ) : ∀ a, Measurable (rawCycleWordSignature a k) := by
  induction k with
  | zero => intro a; exact rawLast_measurable a
  | succ k ih =>
    intro a
    apply measurable_sigma_family
    intro n
    exact ((rawReturnInputSignature_measurable a).comp
      ((rawReturnTrace_mk_measurable a n).comp measurable_fst)).prodMk
        ((ih (a+2*(n+1))).comp measurable_snd)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
