import OAI.NumberTheory.PrimePackets.ErgodicDecomposition

namespace OAI

/-!
# Conditional component invariance from almost invariant base sets

Pointwise invariance of every set in the conditioning sigma algebra is
stronger than needed. Almost invariance with respect to the ambient
probability already makes the conditional component measures invariant.
This permits Mautner's L² argument to act on the full-subgroup components
without asserting that the new map normalizes the subgroup.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExpKernel_invariant_of_ae_invariant_sets
    {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (hm : m ≤ mY)
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (hfix : ∀ A : Set Y, MeasurableSet[m] A → T ⁻¹' A =ᵐ[μ] A) :
    ∀ᵐ z ∂μ.trim hm, (condExpKernel μ m z).map T = condExpKernel μ m z := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdiag : τ ⊗ₘ κ = @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κ := by
    rw [Measure.compProd_map hT.measurable, hdiag]
    apply Measure.ext_prod
    intro A B hA hB
    have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
      (measurable_id'' hm).prodMk measurable_id
    rw [Measure.map_apply (measurable_id.prodMap hT.measurable) (hA.prod hB),
      Measure.map_apply hδ ((measurable_id.prodMap hT.measurable) (hA.prod hB)),
      Measure.map_apply hδ (hA.prod hB)]
    change μ (A ∩ T ⁻¹' B) = μ (A ∩ B)
    have he : A ∩ T ⁻¹' B =ᵐ[μ] T ⁻¹' (A ∩ B) := by
      filter_upwards [(hfix A hA).mem_iff] with x hx
      apply propext
      change (x ∈ A ∧ T x ∈ B) ↔ (T x ∈ A ∧ T x ∈ B)
      change (T x ∈ A ↔ x ∈ A) at hx
      rw [hx]
    exact (measure_congr he).trans
      (hT.measure_preimage ((hm A hA).inter hB).nullMeasurableSet)
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ hT.measurable
  have h₁ := condKernel_compProd τ (κ.map T)
  have h₂ := condKernel_compProd τ κ
  have h₁' : (τ ⊗ₘ κ).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using h₁
  filter_upwards [h₁'.symm.trans h₂] with z hz
  change (κ.map T) z = κ z at hz
  simpa only [Kernel.map_apply _ hT.measurable, κ] using hz

end DukePrimeDegree

end

end OAI
