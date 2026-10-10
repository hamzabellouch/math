import OAI.NumberTheory.Jacobsthal.Probability.JointMarkedWord

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

noncomputable def wordSignatureEnd : (k : ℕ) → CycleWordSignature k → CostState
  | 0, s => s
  | k+1, s => wordSignatureEnd k s.2

lemma wordSignatureEnd_measurable (k : ℕ) : Measurable (wordSignatureEnd k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact ih.comp measurable_snd

noncomputable def branchWordKernel : List Bool → Kernel OddCost OddCost
  | [] => Kernel.id
  | b::w => branchWordKernel w ∘ₖ cycleBranchKernel b

instance branchWordKernel_isFiniteKernel (w : List Bool) : IsFiniteKernel (branchWordKernel w) := by
  induction w with
  | nil => change IsFiniteKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | cons b w ih => rw [branchWordKernel]; infer_instance

lemma branchWordKernel_replicate (b : Bool) (n : ℕ) :
    branchWordKernel (List.replicate n b)=cycleBranchKernel b ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,branchWordKernel,ih,pow_succ]; rfl

lemma branchWordKernel_first_replicate (b c : Bool) (n : ℕ) :
    branchWordKernel (b::List.replicate n c)=(cycleBranchKernel c ^ n) ∘ₖ cycleBranchKernel b := by
  rw [branchWordKernel,branchWordKernel_replicate]

lemma sourceMarkedWord_endpoint (w : List Bool) : ∀ z,
    (sourceMarkedWordKernel w z).map (wordSignatureEnd w.length) = (branchWordKernel w z).map embedOdd := by
  induction w with
  | nil =>
    intro z
    change (Measure.dirac (embedOdd z)).map id=(Measure.dirac z).map embedOdd
    rw [Measure.map_id,Measure.map_dirac' embedOdd_measurable]
  | cons b w ih =>
    intro z
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (wordSignatureEnd_measurable _),lintegral_map hF embedOdd_measurable,
      sourceMarkedWord_cons_lintegral b w z
        (F := fun s => F (wordSignatureEnd (b::w).length s)) (hF.comp (wordSignatureEnd_measurable _))]
    have hi (y : SourceCycleWitness) : (∫⁻ s,
        F (wordSignatureEnd w.length s) ∂sourceMarkedWordKernel w y.2.2) =
      ∫⁻ u, F (embedOdd u) ∂branchWordKernel w y.2.2 := by
      rw [← lintegral_map (g := wordSignatureEnd w.length) hF (wordSignatureEnd_measurable _),ih,
        lintegral_map hF embedOdd_measurable]
    change (∫⁻ y : SourceCycleWitness, ∫⁻ s,
      F (wordSignatureEnd w.length s) ∂sourceMarkedWordKernel w y.2.2 ∂sourceBranchWitnessKernel b z) = _
    simp_rw [hi]
    have hJ : Measurable (fun y : OddCost => ∫⁻ u, F (embedOdd u) ∂branchWordKernel w y) :=
      (hF.comp embedOdd_measurable).lintegral_kernel
    rw [← lintegral_map (g := fun y : SourceCycleWitness => y.2.2) hJ (measurable_snd.comp measurable_snd),
      sourceBranchWitness_endpoint,branchWordKernel,Kernel.lintegral_comp _ _ _ (g := fun u : OddCost => F (embedOdd u)) (hF.comp embedOdd_measurable)]

noncomputable def rawWordReturnedOdd (a : ℕ) (w : List Bool) (t : RawCycleWordTrace a w.length) : OddCost :=
  decodeReturnedOdd (wordSignatureEnd w.length (rawCycleWordSignature a w.length t))

lemma rawWordReturnedOdd_measurable (a : ℕ) (w : List Bool) : Measurable (rawWordReturnedOdd a w) :=
  decodeReturnedOdd_measurable.comp ((wordSignatureEnd_measurable _).comp (rawCycleWordSignature_measurable _ _))

theorem rawMarkedWord_endpoint (a : ℕ) (w : List Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawMarkedWordKernel a w h).map (rawWordReturnedOdd a w)=branchWordKernel w z := by
  calc
    _ = (((rawMarkedWordKernel a w h).map (rawCycleWordSignature a w.length)).map
        (wordSignatureEnd w.length)).map decodeReturnedOdd := by
      rw [Measure.map_map decodeReturnedOdd_measurable (wordSignatureEnd_measurable _),
        Measure.map_map (decodeReturnedOdd_measurable.comp (wordSignatureEnd_measurable _))
          (rawCycleWordSignature_measurable _ _)]
      rfl
    _ = ((branchWordKernel w z).map embedOdd).map decodeReturnedOdd := by
      rw [rawMarkedWord_signature w a h z hz,sourceMarkedWord_endpoint]
    _ = _ := by
      rw [Measure.map_map decodeReturnedOdd_measurable embedOdd_measurable]
      have he : decodeReturnedOdd ∘ embedOdd=id := rfl
      rw [he,Measure.map_id]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
