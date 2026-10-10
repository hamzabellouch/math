import OAI.MeasureTheory.Falconer.Graphs.GraphChartIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphCartesianEquiv : GraphLiftSpace ≃ᵐ Plane × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    ((MeasurableEquiv.prodComm : ℝ × (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) × ℝ).trans
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).prodCongr (MeasurableEquiv.refl ℝ)))

theorem graphCartesianEquiv_apply (x : GraphLiftSpace) :
    graphCartesianEquiv x = (graphCartesianFrequency x, x 2) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem graphCartesianEquiv_volume_preserving : MeasurePreserving graphCartesianEquiv := by
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h₂ : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h₃ := (PiLp.volume_preserving_toLp (Fin 2)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact h₃.comp (h₂.comp h₁)

theorem graphCartesianEquiv_symm_weight (y : Plane × ℝ) :
    graphJacobianWeight (graphCartesianEquiv.symm y) =
      (‖y.1‖*Real.sqrt (1+y.2^2))⁻¹ := by
  have he := graphCartesianEquiv_apply (graphCartesianEquiv.symm y)
  rw [MeasurableEquiv.apply_symm_apply] at he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change y.1 = graphCartesianFrequency (graphCartesianEquiv.symm y) at h₁
  change y.2 = (graphCartesianEquiv.symm y) 2 at h₂
  simp only [graphJacobianWeight, ← h₁, ← h₂]

theorem graph_chart_plane_product_integral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℂ) :
    (∫ q in graphLiftMap '' S, f q) =
      ∫ y in graphCartesianEquiv '' (graphPolarMap '' S),
        (‖y.1‖*Real.sqrt (1+y.2^2))⁻¹ •
          f (graphLiftMap (graphPolarInverse (graphCartesianEquiv.symm y))) := by
  rw [graph_chart_cartesian_integral S hS hdom f,
    graphCartesianEquiv_volume_preserving.setIntegral_image_emb
      graphCartesianEquiv.measurableEmbedding]
  apply setIntegral_congr_fun
    (measurable_image_of_fderivWithin hS
      (fun p (_ : p ∈ S) => (graphPolarMap_hasFDerivAt p).hasFDerivWithinAt)
      (graphPolarMap_injOn.mono hdom))
  intro x hx
  dsimp only
  rw [MeasurableEquiv.symm_apply_apply, graphCartesianEquiv_apply]
  rfl

end PlanarFalconer

end OAI
