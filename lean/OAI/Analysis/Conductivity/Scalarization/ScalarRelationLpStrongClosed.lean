import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ScalarRelationStrongClosed

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

theorem scalar_relation_Lp_strong_closed
    {X V : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b)
    {E F : Lp V 2 μ} {En Fn : ℕ → Lp V 2 μ} {sn : ℕ → X → ℝ}
    (hs : ∀ n, ∀ᵐ x ∂μ, sn n x ∈ Set.Icc a b)
    (hE : Tendsto En atTop (𝓝 E)) (hF : Tendsto Fn atTop (𝓝 F))
    (hres : TendstoInMeasure μ (fun n x => Fn n x - sn n x • En n x)
      atTop (fun _ => 0)) :
    ∃ s : X → ℝ, Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Set.Icc a b ∧ F x = s x • E x) := by
  obtain ⟨φ, hφ, hElim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hE).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hFlim⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp hF).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ξ, hξ, hrlim⟩ :=
    ((hres.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop).exists_seq_tendsto_ae
  apply scalar_relation_ae_strong_closed hab (Lp.stronglyMeasurable E).measurable
    (Lp.stronglyMeasurable F).measurable (En := fun n => En (φ (ψ (ξ n))))
    (Fn := fun n => Fn (φ (ψ (ξ n)))) (sn := fun n => sn (φ (ψ (ξ n))))
  · exact fun n => hs _
  · filter_upwards [hElim] with x hx
    exact (hx.comp hψ.tendsto_atTop).comp hξ.tendsto_atTop
  · filter_upwards [hFlim] with x hx
    exact hx.comp hξ.tendsto_atTop
  · exact hrlim

end ScalarConductivity

end
end

end OAI
