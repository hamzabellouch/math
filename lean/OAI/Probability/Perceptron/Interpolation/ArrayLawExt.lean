import Mathlib
import OAI.Probability.Perceptron.Variational.CovarianceMatrix

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

lemma array_law_eq_of_blocks {K : Type*} [MeasurableSpace K]
    (μ ν : Measure (CompactArray K)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (compactBlock (n+1)) = ν.map (compactBlock (n+1))) : μ = ν := by
  let e : CompactArray K ≃ᵐ (ℕ × ℕ → K) := (MeasurableEquiv.curry ℕ ℕ K).symm
  apply e.map_measurableEquiv_injective
  let P (I : Finset (ℕ × ℕ)) := (ν.map e).map I.restrict
  have hp : IsProjectiveLimit (ν.map e) P := fun _ => rfl
  apply IsProjectiveLimit.unique (P := P) ?_ hp
  intro I
  let n := I.sup (fun a => max a.1 a.2)
  have hb (a : I) : a.val.1 < n+1 ∧ a.val.2 < n+1 := by
    have he : max a.val.1 a.val.2 ≤ n := Finset.le_sup (f := fun a : ℕ × ℕ => max a.1 a.2) a.property
    exact ⟨by omega,by omega⟩
  let G : CompactBlock K (n+1) → (I → K) :=
    fun B a => B ⟨a.val.1,(hb a).1⟩ ⟨a.val.2,(hb a).2⟩
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro a
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hm : Measurable (compactBlock (K:=K) (n+1)) := by
    unfold compactBlock
    exact Measurable.of_eval fun _ => Measurable.of_eval fun _ => by fun_prop
  change (μ.map e).map I.restrict = (ν.map e).map I.restrict
  have he : I.restrict ∘ e = G ∘ compactBlock (n+1) := by
    funext Q a
    rfl
  rw [Measure.map_map I.measurable_restrict e.measurable,
    Measure.map_map I.measurable_restrict e.measurable,he,
    ← Measure.map_map hG hm,← Measure.map_map hG hm,h n]

end SphericalPerceptronFreeEnergy

end

end OAI
