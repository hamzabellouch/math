import OAI.NumberTheory.Jacobsthal.Paths.RawWordBridgeInputs

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

noncomputable def sourceWordReward (w : List Bool)
    (F : CycleInputSignature × CycleWordSignature w.length → ℝ≥0∞) (c : CycleInputSignature) : ℝ≥0∞ :=
  ∫⁻ s, F (c,s) ∂sourceMarkedWordKernel w (decodeReturnedOdd c.2.2.2)

lemma sourceWordReward_measurable (w : List Bool)
    {F : CycleInputSignature × CycleWordSignature w.length → ℝ≥0∞} (hF : Measurable F) :
    Measurable (sourceWordReward w F) := by
  let K : Kernel CycleInputSignature (CycleWordSignature w.length) :=
    (sourceMarkedWordKernel w).comap (fun c : CycleInputSignature => decodeReturnedOdd c.2.2.2)
      (decodeReturnedOdd_measurable.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  change Measurable (fun c : CycleInputSignature => ∫⁻ s, F (c,s) ∂K c)
  exact hF.lintegral_kernel_prod_right'

theorem rawMarkedWord_signature (w : List Bool) : ∀ (a : ℕ) (h : RawHistory a) (z : OddCost),
    rawLast a h=embedOdd z →
    (rawMarkedWordKernel a w h).map (rawCycleWordSignature a w.length) = sourceMarkedWordKernel w z := by
  induction w with
  | nil =>
    intro a h z hz
    change (Measure.dirac h).map (rawLast a) = Measure.dirac (embedOdd z)
    rw [Measure.map_dirac' (rawLast_measurable a),hz]
  | cons b w ih =>
    intro a h z hz
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (rawCycleWordSignature_measurable _ a),
      rawMarkedWord_cons_lintegral a b w h
        (F := fun t => F (rawCycleWordSignature a (b::w).length t))
        (hF.comp (rawCycleWordSignature_measurable _ a)),sourceMarkedWord_cons_lintegral b w z hF]
    have hInner : (fun r : RawReturnTrace a => ∫⁻ t,
        F (rawReturnInputSignature a r,rawCycleWordSignature (a+2*(r.1+1)) w.length t)
          ∂rawMarkedWordKernel (a+2*(r.1+1)) w r.2) =ᵐ[rawBranchReturnKernel a b h]
        fun r => sourceWordReward w F (rawReturnInputSignature a r) := by
      filter_upwards [rawBranchReturn_endpoint_supported a b h] with r hr
      rcases r with ⟨n,y⟩
      change (∫⁻ t, F (rawReturnInputSignature a ⟨n,y⟩,rawCycleWordSignature (a+2*(n+1)) w.length t)
        ∂rawMarkedWordKernel (a+2*(n+1)) w y) = _
      have hi := ih (a+2*(n+1)) y (decodeReturnedOdd (rawReturnSignature a ⟨n,y⟩).2.2) hr
      have hG : Measurable (fun s : CycleWordSignature w.length => F (rawReturnInputSignature a ⟨n,y⟩,s)) :=
        hF.comp measurable_prodMk_left
      rw [← lintegral_map (g := rawCycleWordSignature (a+2*(n+1)) w.length)
        (f := fun s : CycleWordSignature w.length => F (rawReturnInputSignature a ⟨n,y⟩,s))
        hG (rawCycleWordSignature_measurable _ _),hi]
      rfl
    change (∫⁻ r : RawReturnTrace a, ∫⁻ t,
        F (rawReturnInputSignature a r,rawCycleWordSignature (a+2*(r.1+1)) w.length t)
          ∂rawMarkedWordKernel (a+2*(r.1+1)) w r.2 ∂rawBranchReturnKernel a b h) = _
    rw [lintegral_congr_ae hInner,
      ← lintegral_map (g := rawReturnInputSignature a) (sourceWordReward_measurable w hF)
        (rawReturnInputSignature_measurable a),rawBranchReturn_input_signature a b h z hz,
      lintegral_map (g := sourceCycleInputSignature z) (sourceWordReward_measurable w hF)
        (sourceCycleInputSignature_measurable.comp measurable_prodMk_left)]
    rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
