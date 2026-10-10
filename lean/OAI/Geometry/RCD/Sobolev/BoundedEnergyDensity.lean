import OAI.Geometry.RCD.Metric.BoundedFiniteDensity

namespace OAI

/-! # A bounded measurable representative of the limiting energy density -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem bounded_finite_density_pointwise (μ : Measure X) [IsFiniteMeasure μ]
    (ν : FiniteMeasure X) {M : ℝ} (hM : 0≤M)
    (hν : (ν : Measure X)≤ENNReal.ofReal M • μ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧
      (∀ x, 0≤f x ∧ f x≤M) ∧
      ∀ A : Set X, MeasurableSet A → (ν : Measure X).real A=∫ x in A, f x ∂μ := by
  obtain ⟨g,hgm,hgi,hgb,hrep⟩ := bounded_finite_density μ ν hM hν
  let f := fun x => min M (max 0 (g x))
  have hfg : f=ᵐ[μ] g := hgb.mono fun x hx => by simp [f,max_eq_right hx.1,min_eq_right hx.2]
  have hfm : Measurable f := measurable_const.min (measurable_const.max hgm)
  have hfi : Integrable f μ := hgi.congr hfg.symm
  have hfb (x : X) : 0≤f x ∧ f x≤M :=
    ⟨le_min hM (le_max_left _ _),min_le_left _ _⟩
  refine ⟨f,hfm,hfi,hfb,?_⟩
  intro A hA
  have he : (ν : Measure X)=(finiteDensityMeasure μ hfi : Measure X) := by
    change (ν : Measure X)=μ.withDensity (fun x => ENNReal.ofReal (f x))
    rw [hrep]
    exact withDensity_congr_ae (hfg.symm.mono fun _ hx => congrArg ENNReal.ofReal hx)
  rw [he]
  exact finiteDensityMeasure_apply μ hfi (Eventually.of_forall fun x => (hfb x).1) hA

end RegularPointCoordinates

end

end OAI
