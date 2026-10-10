import OAI.Probability.PosteriorReplicas.Information.ParametricKernel

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {T Y Z : Type*} [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [StandardBorelSpace Z] [Nonempty Y] [Nonempty Z]
  {n : ℕ}

omit [StandardBorelSpace Y] [Nonempty Y] [Nonempty Z] in
lemma measurable_projected_totalCorrelation (ν : Measure (Fin n → Y)) [IsProbabilityMeasure ν]
    {g : T × Y → Z} (hg : Measurable g) :
    Measurable (fun b => totalCorrelation (ν.map (fun u i => g (b,u i)))) := by
  let h : T × (Fin n → Y) → (Fin n → Z) := fun z i => g (z.1,z.2 i)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel ν h
  have : IsMarkovKernel κ := parametricMapKernel_markov ν h hh
  have hc := measurable_kernel_klDiv κ (piKernel (coordKernel κ))
  simp only [piKernel_apply, coordKernel_apply] at hc
  change Measurable (fun b => totalCorrelation (κ b)) at hc
  simpa only [κ, parametricMapKernel_apply ν hh, h] using hc
end

section
variable {T W Y Z : Type*} [MeasurableSpace T] [MeasurableSpace W]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace W] [Nonempty W] [Fintype W] [MeasurableSingletonClass W]
  [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
  {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
  (μ : Measure W) [IsProbabilityMeasure μ]
  (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]
  {g : T × Y → Z} (hg : Measurable g)
include hg

lemma random_replica_information_le_entropy :
    (∑ i, cmi (randomSideLaw β g (coordinateJoint μ κ i))) +
      (∫⁻ b, totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  have hi (i : Fin n) := measurable_cmi_attachSide hg (coordinateJoint μ κ i)
  have ht := measurable_projected_totalCorrelation (μ ⊗ₘ κ).snd hg
  have h := lintegral_mono (μ := β) (fun b =>
    replica_information_le_entropy μ κ (g := fun y => g (b,y)) (by fun_prop))
  rw [lintegral_add_aux (Finset.measurable_sum _ (fun i _ => hi i)) ht,
    lintegral_finsetSum _ (fun i _ => hi i)] at h
  simp only [lintegral_const, measure_univ, mul_one] at h
  simpa only [cmi_randomSideLaw β hg] using h

lemma random_replica_information_identical (q : Measure (Y × W)) [IsProbabilityMeasure q]
    (hq : ∀ i, coordinateJoint μ κ i = q) :
    (n : ℝ≥0∞) * cmi (randomSideLaw β g q) +
      (∫⁻ b, totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  have h := random_replica_information_le_entropy β μ κ hg
  have hs : (∑ i, cmi (randomSideLaw β g (coordinateJoint μ κ i))) =
      (n : ℝ≥0∞) * cmi (randomSideLaw β g q) := by
    calc
      _ = ∑ _i : Fin n, cmi (randomSideLaw β g q) := by
        apply Finset.sum_congr rfl
        intro i _
        cases hq i
        rfl
      _ = _ := by simp
  rw [hs] at h
  exact h
end

lemma conditionalInformation_eq_cmi {d ℓ N : ℕ} [NeZero N]
    (q : Measure (Data d ℓ × (Vec d × Fin N))) [IsFiniteMeasure q] :
    conditionalInformation q = cmi q := rfl

lemma sideLaw_eq_randomSideLaw {d ℓ N : ℕ} (q : Measure (Vec d × Fin N)) :
    sideLaw ℓ q = randomSideLaw (gaussianRows d ℓ) (fun z => labels z.1 z.2) q := rfl

lemma messageEntropy_eq_finiteEntropy {d N : ℕ} (q : Measure (Vec d × Fin N)) :
    messageEntropy q = finiteEntropy q.snd := rfl

end PosteriorReplicas
end

end OAI
