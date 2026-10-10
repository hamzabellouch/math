import OAI.MeasureTheory.Falconer.Fourier.PositiveDistanceSpatialKernel
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

def fourSpatialPairEquiv : (Fin 4 → Plane) ≃ᵐ ((Plane × Plane) × (Plane × Plane)) where
  toFun x := ((x 0,x 1),(x 2,x 3))
  invFun z := ![z.1.1,z.1.2,z.2.1,z.2.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by rcases z with ⟨⟨x,y⟩,⟨u,v⟩⟩; rfl
  measurable_toFun := by
    change Measurable (fun x : Fin 4 → Plane => ((x 0,x 1),(x 2,x 3)))
    fun_prop
  measurable_invFun := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun z : (Plane × Plane) × (Plane × Plane) =>
      (![z.1.1,z.1.2,z.2.1,z.2.2] : Fin 4 → Plane) i)
    fin_cases i <;> fun_prop

theorem measurePreserving_fourSpatialPair (μ : Fin 4 → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] :
    MeasurePreserving fourSpatialPairEquiv (Measure.pi μ)
      ((μ 0).prod (μ 1) |>.prod ((μ 2).prod (μ 3))) := by
  apply MeasurePreserving.symm fourSpatialPairEquiv.symm
  refine ⟨fourSpatialPairEquiv.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply fourSpatialPairEquiv.symm.measurable (MeasurableSet.univ_pi hs)]
  have he : fourSpatialPairEquiv.symm ⁻¹' Set.pi univ s =
      (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
    ext z
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
    · intro h i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2.1
      · exact h.2.2
  rw [he,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,Fin.prod_univ_four]
  ring

theorem lintegral_fourSpatialPair (μ : Fin 4 → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] (F : ((Plane × Plane) × (Plane × Plane)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F ((x 0,x 1),(x 2,x 3)) ∂Measure.pi μ) =
      ∫⁻ z, F z ∂((μ 0).prod (μ 1) |>.prod ((μ 2).prod (μ 3))) :=
  (measurePreserving_fourSpatialPair μ).lintegral_comp hF

theorem setLIntegral_fourSpatialPair (μ : Fin 4 → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] (F : ((Plane × Plane) × (Plane × Plane)) → ℝ≥0∞)
    (hF : Measurable F) (S : Set ((Plane × Plane) × (Plane × Plane)))
    (hS : MeasurableSet S) :
    (∫⁻ x in fourSpatialPairEquiv ⁻¹' S, F ((x 0,x 1),(x 2,x 3)) ∂Measure.pi μ) =
      ∫⁻ z in S, F z ∂((μ 0).prod (μ 1) |>.prod ((μ 2).prod (μ 3))) :=
  (measurePreserving_fourSpatialPair μ).setLIntegral_comp_preimage hS hF

end PlanarFalconer

end OAI
