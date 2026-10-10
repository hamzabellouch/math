import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixReorder
import OAI.NumberTheory.DukePrimeDegree.Entropy.PrefixRootConditionals

namespace OAI

/-! # The root-order exchange as an actual extended-prefix time chart -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T)
    {D : Finset (Fin (d+1))}
    (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def nextTimeCoordinates : positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ c.Time :=
  q.nextGroupCast.trans (c.remainingWordHomeomorph q.next_initial hfinal).symm

def prefixTimeExchange :
    ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) ≃ₜ
    ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  (((Homeomorph.refl (UpperRootTransverse (d+1) × T)).prodCongr
      (q.rootOrderCoordinates d)).trans
    (Homeomorph.prodAssoc (UpperRootTransverse (d+1) × T) ℝ
      (positiveRootGeneratedGroup (q.remaining.erase q.root))).symm).trans
    ((Homeomorph.prodAssoc (UpperRootTransverse (d+1)) T ℝ).prodCongr
      (nextTimeCoordinates q c hfinal))

lemma prefixTimeExchange_apply
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    prefixTimeExchange (T := T) q c hfinal z =
      ((z.1.1,(z.1.2,z.2.2)),
        nextTimeCoordinates q c hfinal (q.nextConjugation d z.2.2 z.2.1)) := rfl

lemma prefixTimeExchange_param (g : G (d+1))
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    (C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g
      (prefixTimeExchange (T := T) q c hfinal z) = C.extendedRootParam q g z := by
  change (C.extend q.initial q.root q.mem_remaining q.least).quotientParam g
      (z.1.1,((z.1.2,z.2.2),(c.remainingWordHomeomorph q.next_initial hfinal)
        ((c.remainingWordHomeomorph q.next_initial hfinal).symm
          (q.nextGroupCast (q.nextConjugation d z.2.2 z.2.1))))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

variable [MeasurableSpace T] [BorelSpace T]

theorem prefixTimeExchange_conditional
    (ρ : Measure ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ))) [IsFiniteMeasure ρ] :
    ∀ᵐ b ∂(ρ.map (q.prefixRootExchange d)).fst,
      (ρ.map (prefixTimeExchange (T := T) q c hfinal)).condKernel
          (Homeomorph.prodAssoc (UpperRootTransverse (d+1)) T ℝ b) =
        ((ρ.map (q.prefixRootExchange d)).condKernel b).map (nextTimeCoordinates q c hfinal) := by
  let σ := ρ.map (q.prefixRootExchange d)
  let E := (Homeomorph.prodAssoc (UpperRootTransverse (d+1)) T ℝ).toMeasurableEquiv
  let F := fun z : ((UpperRootTransverse (d+1) × T) × ℝ) ×
      positiveRootGeneratedGroup (q.remaining.erase q.root) => nextTimeCoordinates q c hfinal z.2
  have hF : Measurable F := (nextTimeCoordinates q c hfinal).measurable.comp measurable_snd
  have H := conditional_map_fibers σ E F hF
  have hm : σ.map (fun z => (E z.1,F z)) = ρ.map (prefixTimeExchange (T := T) q c hfinal) := by
    dsimp only [σ]
    have hg : Measurable (fun z => (E z.1,F z)) :=
      (E.measurable.comp measurable_fst).prodMk hF
    rw [Measure.map_map hg (q.measurable_prefixRootExchange d)]
    rfl
  change ∀ᵐ b ∂σ.fst,
    (ρ.map (prefixTimeExchange (T := T) q c hfinal)).condKernel (E b) =
      (σ.condKernel b).map (fun w => F (b,w))
  simpa only [hm] using H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
