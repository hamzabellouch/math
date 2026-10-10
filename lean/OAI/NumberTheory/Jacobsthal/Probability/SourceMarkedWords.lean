import OAI.NumberTheory.Jacobsthal.Paths.RawWordSpaces

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry

noncomputable def sourceCycleInputSignature (z : OddCost) (w : SourceCycleWitness) : CycleInputSignature :=
  (z.2,sourceReturnSignature z w)

lemma sourceCycleInputSignature_measurable :
    Measurable (fun p : OddCost × SourceCycleWitness => sourceCycleInputSignature p.1 p.2) := by
  have hEven : Measurable (fun p : OddCost × SourceCycleWitness => p.2.1) := measurable_fst.comp measurable_snd
  have hOld : Measurable (fun p : OddCost × SourceCycleWitness => p.1.2) := measurable_snd.comp measurable_fst
  have hDur : Measurable (fun p : OddCost × SourceCycleWitness => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hRet : Measurable (fun p : OddCost × SourceCycleWitness => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact hOld.prodMk (hDur.prodMk (((measurable_inl.comp hEven).prodMk
    (hOld.add (cost_measurable.comp (measurable_subtype_coe.comp hEven)))).prodMk
      (embedOdd_measurable.comp hRet)))

noncomputable def sourceWordUpdate (k : ℕ) (p : OddCost × (SourceCycleWitness × CycleWordSignature k)) :
    CycleWordSignature (k+1) := (sourceCycleInputSignature p.1 p.2.1,p.2.2)

lemma sourceWordUpdate_measurable (k : ℕ) : Measurable (sourceWordUpdate k) :=
  (sourceCycleInputSignature_measurable.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)

def sourceContinuationInput (p : OddCost × SourceCycleWitness) : OddCost := p.2.2.2

lemma sourceContinuationInput_measurable : Measurable sourceContinuationInput :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

noncomputable def sourceMarkedWordKernel : (w : List Bool) → Kernel OddCost (CycleWordSignature w.length)
  | [] => Kernel.deterministic embedOdd embedOdd_measurable
  | b::w =>
    (Kernel.id ×ₖ (sourceBranchWitnessKernel b ⊗ₖ
      (sourceMarkedWordKernel w).comap sourceContinuationInput sourceContinuationInput_measurable)).map
        (sourceWordUpdate w.length)

instance sourceMarkedWordKernel_isFiniteKernel (w : List Bool) : IsFiniteKernel (sourceMarkedWordKernel w) := by
  induction w with
  | nil => change IsFiniteKernel (Kernel.deterministic embedOdd embedOdd_measurable); infer_instance
  | cons b w ih => rw [sourceMarkedWordKernel]; infer_instance

lemma sourceMarkedWord_cons_lintegral (b : Bool) (w : List Bool) (z : OddCost)
    {F : CycleWordSignature (b::w).length → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s, F s ∂sourceMarkedWordKernel (b::w) z) =
      ∫⁻ y : SourceCycleWitness, ∫⁻ s,
        F (sourceCycleInputSignature z y,s) ∂sourceMarkedWordKernel w y.2.2 ∂sourceBranchWitnessKernel b z := by
  rw [sourceMarkedWordKernel,Kernel.map_apply _ (sourceWordUpdate_measurable _),
    lintegral_map hF (sourceWordUpdate_measurable _),Kernel.lintegral_id_prod (f := fun p : OddCost × (SourceCycleWitness × CycleWordSignature w.length) => F (sourceWordUpdate w.length p)) (hF.comp (sourceWordUpdate_measurable _)),
    Kernel.lintegral_compProd _ _ _
      (f := fun p : SourceCycleWitness × CycleWordSignature w.length => F (sourceWordUpdate w.length (z,p)))
      ((hF.comp (sourceWordUpdate_measurable _)).comp measurable_prodMk_left)]
  rfl

lemma sourceBranchWitness_mass_le_one (b : Bool) (z : OddCost) : sourceBranchWitnessKernel b z univ ≤ 1 := by
  rw [sourceBranchWitnessKernel,Kernel.restrict_apply]
  exact (Measure.restrict_le_self univ).trans_eq measure_univ

lemma sourceMarkedWord_mass_le_one (w : List Bool) : ∀ z, sourceMarkedWordKernel w z univ ≤ 1 := by
  induction w with
  | nil => intro z; change (Measure.dirac (embedOdd z)) univ ≤ 1; simp
  | cons b w ih =>
    intro z
    have he := sourceMarkedWord_cons_lintegral b w z (F := fun _ => (1:ℝ≥0∞)) measurable_const
    simp only [lintegral_const,one_mul] at he
    rw [he]
    calc
      _ ≤ ∫⁻ _y, (1:ℝ≥0∞) ∂sourceBranchWitnessKernel b z := lintegral_mono (fun y => ih y.2.2)
      _ = sourceBranchWitnessKernel b z univ := by simp
      _ ≤ 1 := sourceBranchWitness_mass_le_one b z

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
