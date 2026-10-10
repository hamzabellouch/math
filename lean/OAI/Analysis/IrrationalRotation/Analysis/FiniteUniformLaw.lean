import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace Invariant233.FiniteUniformLaw

theorem map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).toMeasure.map e = (PMF.uniformOfFintype β).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem pi_uniform {ι : Type*} [Fintype ι] (α : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] :
    Measure.pi (fun i => (PMF.uniformOfFintype (α i)).toMeasure) =
      (PMF.uniformOfFintype ((i : ι) → α i)).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

theorem infinitePi_restrict_uniform {ι : Type*} (α : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (s : Finset ι) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map s.restrict =
      (PMF.uniformOfFintype ((i : s) → α i)).toMeasure := by
  rw [Measure.infinitePi_map_restrict]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

end Invariant233.FiniteUniformLaw

end

end OAI
