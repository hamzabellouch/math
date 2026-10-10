import OAI.Probability.PosteriorReplicas.Information.ConditionalKL
import OAI.Probability.PosteriorReplicas.Information.PiKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section ConditionalPi
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : Kernel X (Fin n → Y)) [IsMarkovKernel κ]

def coordKernel (i : Fin n) : Kernel X Y := κ.map (fun u => u i)
instance coordKernel_markov (i : Fin n) : IsMarkovKernel (coordKernel κ i) :=
  Kernel.IsMarkovKernel.map _ (measurable_pi_apply i)

omit [StandardBorelSpace Y] [Nonempty Y] [IsMarkovKernel κ] in
lemma coordKernel_apply (i : Fin n) (x : X) : coordKernel κ i x = coordinateMarginal (κ x) i :=
  Kernel.map_apply _ (measurable_pi_apply i) _

def conditionalTotalCorrelation : ℝ≥0∞ :=
  klDiv (μ ⊗ₘ κ) (μ ⊗ₘ piKernel (coordKernel κ))

omit [Nonempty Y] in
lemma conditionalTotalCorrelation_integral :
    conditionalTotalCorrelation μ κ = ∫⁻ x, klDiv (κ x) (marginalProduct (κ x)) ∂μ := by
  rw [conditionalTotalCorrelation, klDiv_compProd_kernel]
  apply lintegral_congr
  intro x
  rw [piKernel_apply]
  simp_rw [coordKernel_apply, marginalProduct]

lemma klDiv_conditional_pi_decomposition (ρ : Fin n → Measure Y) [∀ i, IsProbabilityMeasure (ρ i)] :
    klDiv (μ ⊗ₘ κ) (μ.prod (Measure.pi ρ)) = conditionalTotalCorrelation μ κ +
      ∑ i, klDiv (μ ⊗ₘ coordKernel κ i) (μ.prod (ρ i)) := by
  simp_rw [← Measure.compProd_const, klDiv_compProd_kernel]
  rw [conditionalTotalCorrelation_integral]
  calc
    _ = ∫⁻ x, klDiv (κ x) (marginalProduct (κ x)) +
        ∑ i, klDiv (coordinateMarginal (κ x) i) (ρ i) ∂μ := by
      exact lintegral_congr fun x => klDiv_pi_decomposition (κ x) ρ
    _ = _ := by
      have hc : Measurable (fun x => klDiv (κ x) (marginalProduct (κ x))) := by
        simpa only [piKernel_apply, coordKernel_apply, marginalProduct] using
          (measurable_kernel_klDiv κ (piKernel (coordKernel κ)))
      have hi : ∀ i, Measurable (fun x => klDiv (coordinateMarginal (κ x) i) (ρ i)) := by
        intro i
        simpa only [coordKernel_apply, Kernel.const_apply] using
          (measurable_kernel_klDiv (coordKernel κ i) (Kernel.const X (ρ i)))
      rw [lintegral_add_aux hc (Finset.measurable_sum _ (fun i _ => hi i)),
        lintegral_finsetSum _ (fun i _ => hi i)]
      simp_rw [coordKernel_apply, Kernel.const_apply]

lemma conditionalTotalCorrelation_identity [StandardBorelSpace X] [Nonempty X] :
    conditionalTotalCorrelation μ κ +
      ∑ i, klDiv (μ ⊗ₘ coordKernel κ i)
        (μ.prod (coordinateMarginal (μ ⊗ₘ κ).snd i)) =
      klDiv (μ ⊗ₘ κ).snd (marginalProduct (μ ⊗ₘ κ).snd) +
      klDiv (μ ⊗ₘ κ) (μ.prod (μ ⊗ₘ κ).snd) := by
  rw [← klDiv_conditional_pi_decomposition]
  rw [klDiv_prod_decomposition, Measure.fst_compProd, klDiv_self, zero_add]
  rfl

end ConditionalPi

section Projection
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
  {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : Kernel X (Fin n → Y)) [IsMarkovKernel κ]
  {g : Y → Z} (hg : Measurable g)
include hg

omit [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z] in
lemma marginalProduct_map (ν : Measure (Fin n → Y)) [IsProbabilityMeasure ν] :
    marginalProduct (ν.map (fun u i => g (u i))) =
      (marginalProduct ν).map (fun u i => g (u i)) := by
  unfold marginalProduct coordinateMarginal
  have he : (fun i : Fin n => (ν.map (fun u j => g (u j))).map (fun u => u i)) =
      fun i => (ν.map (fun u => u i)).map g := by
    funext i
    rw [Measure.map_map (measurable_pi_apply i) (by fun_prop),
      Measure.map_map hg (measurable_pi_apply i)]
    rfl
  rw [he]
  exact (Measure.pi_map_pi (fun _ : Fin n => hg.aemeasurable)).symm

omit [Nonempty Y] [Nonempty Z] in
lemma conditionalTotalCorrelation_map_le :
    conditionalTotalCorrelation μ (κ.map (fun u i => g (u i))) ≤ conditionalTotalCorrelation μ κ := by
  let : IsMarkovKernel (κ.map (fun u i => g (u i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  rw [conditionalTotalCorrelation_integral, conditionalTotalCorrelation_integral]
  apply lintegral_mono
  intro x
  dsimp only
  rw [Kernel.map_apply _ (show Measurable (fun u : Fin n → Y => fun i => g (u i)) by fun_prop), marginalProduct_map hg]
  exact klDiv_map_le _ _ (by fun_prop)

end Projection
end PosteriorReplicas
end

end OAI
