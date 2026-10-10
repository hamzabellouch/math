import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalProduct

namespace OAI

/-!
# Compatibility of nested real conditional measures

Conditioning first on a transverse coordinate and then on all but one
leaf coordinate gives the same real conditional as conditioning on both
coordinates at once. This is the finite-chart form of
Einsiedler--Katok (2003), Lemma 8.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace DukePrimeDegree

variable {T : Type*} [MeasurableSpace T]
variable {B : Type*} [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

theorem ae_nested_real_conditionals
    (μ : Measure (T × (B × ℝ))) [IsFiniteMeasure μ] :
    ∀ᵐ a ∂μ.fst, ∀ᵐ b ∂(μ.condKernel a).fst,
      (μ.map MeasurableEquiv.prodAssoc.symm).condKernel (a, b) =
        (μ.condKernel a).condKernel b := by
  let κ := μ.condKernel
  let ρ := μ.map MeasurableEquiv.prodAssoc.symm
  have hρ : ρ = (μ.fst ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    calc
      ρ = (μ.fst ⊗ₘ (κ.fst ⊗ₖ κ.condKernel)).map MeasurableEquiv.prodAssoc.symm := by
        rw [Kernel.disintegrate, Measure.disintegrate]
      _ = _ := Measure.compProd_assoc
  have hfst : ρ.fst = μ.fst ⊗ₘ κ.fst := by
    rw [hρ, Measure.fst_compProd]
  have heq : κ.condKernel =ᵐ[ρ.fst] ρ.condKernel :=
    eq_condKernel_of_measure_eq_compProd κ.condKernel (by rw [hfst]; exact hρ)
  rw [hfst] at heq
  have h := Measure.ae_ae_of_ae_compProd heq
  filter_upwards [h] with a ha
  have hinner := Kernel.condKernel_apply_eq_condKernel κ a
  filter_upwards [ha, hinner] with b hb hbc
  exact hb.symm.trans hbc

/-- Constant projective real conditionals in a full chart force each
larger conditional leaf measure to split as a product. -/
theorem ae_nested_eq_prod_of_projective_conditionals
    (μ : Measure (T × (B × ℝ))) [IsFiniteMeasure μ]
    (ν : T → Measure ℝ) (hνfinite : ∀ a, IsFiniteMeasure (ν a))
    (hν : ∀ a, ν a Set.univ ≠ 0)
    (h : ∀ᵐ a ∂μ.fst, ∀ᵐ b ∂(μ.condKernel a).fst, ∃ c : ℝ≥0∞,
      (μ.map MeasurableEquiv.prodAssoc.symm).condKernel (a, b) = c • ν a) :
    ∀ᵐ a ∂μ.fst,
      μ.condKernel a = (μ.condKernel a).fst.prod
        (PrimeDegreePackets.anchorNormalize (ν a) Set.univ) := by
  filter_upwards [h, ae_nested_real_conditionals μ] with a ha hc
  let := hνfinite a
  apply eq_prod_of_projective_real_conditionals (μ.condKernel a) (ν a) (hν a)
  filter_upwards [ha, hc] with b hb hbc
  rwa [hbc] at hb

end DukePrimeDegree

end

end OAI
