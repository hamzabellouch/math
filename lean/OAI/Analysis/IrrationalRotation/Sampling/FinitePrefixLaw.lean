import OAI.Analysis.IrrationalRotation.Analysis.FiniteUniformLaw

namespace OAI

noncomputable section
open MeasureTheory
open scoped Classical

namespace Invariant233.FiniteUniformLaw

theorem infinitePi_fin_uniform (α : ℕ → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (N : ℕ) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map
        (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → α i)).toMeasure := by
  classical
  let e : (Finset.range N) ≃ Fin N :=
    { toFun := fun i => ⟨i.1, Finset.mem_range.mp i.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_range.mpr i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : ((i : Finset.range N) → α i) ≃ ((i : Fin N) → α i) :=
    Equiv.piCongrLeft (fun i : Fin N => α i) e
  have hcomp : (fun d (i : Fin N) => d i) =
      E ∘ (Finset.range N).restrict := by rfl
  rw [hcomp, ← Measure.map_map (measurable_of_finite E) (Finset.measurable_restrict _),
    infinitePi_restrict_uniform]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_finite E) (measurableSet_singleton a)]
  have he : E ⁻¹' {a} = {E.symm a} := by
    ext b
    exact E.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply]
  congr 2
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr E

alias infinitePi_fin_prefix_uniform := infinitePi_fin_uniform

end Invariant233.FiniteUniformLaw

end

end OAI
