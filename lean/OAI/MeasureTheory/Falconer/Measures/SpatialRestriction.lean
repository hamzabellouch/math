import OAI.MeasureTheory.Falconer.Fourier.JetStateSpatialShell

namespace OAI

/-! # Measurable product restrictions stay in the original endpoint jet class -/

namespace Falconer
open Set MeasureTheory

 theorem endpointTransform_restrict_indicator {d : ℕ} (μ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (S : Set (Space d)) (hS : MeasurableSet S)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict S) M b r w =
      endpointTransform μ M (fun x u => S.indicator (fun _ => (1:ℂ)) x*b x u) r w := by
  unfold endpointTransform
  rw [← integral_indicator hS]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S <;> simp [hx]

namespace DescriptorJetSymbol

noncomputable def restrictSpatial {n K L : ℕ} {F : Finset PlanarFalconer.PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D) (S : Set (Space (n+2))) (hS : MeasurableSet S) :
    DescriptorJetSymbol n K L F D :=
  f.spatialMultiplier (S.indicator (fun _ => (1:ℂ))) (measurable_const.indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx])

 theorem restrictSpatial_endpoint {n K L : ℕ} {F : Finset PlanarFalconer.PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D) (S : Set (Space (n+2))) (hS : MeasurableSet S)
    (Q : DyadicCube (n+2)) (ρ μ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (masks : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
    (A M r : ℝ) (w : Sphere (n+2)) :
    endpointTransform μ M ((f.restrictSpatial S hS).value Q ρ profile N σ J i masks A) r w =
      endpointTransform (μ.restrict S) M (f.value Q ρ profile N σ J i masks A) r w := by
  rw [endpointTransform_restrict_indicator μ M _ S hS]
  congr 1
  funext x u
  exact f.spatialMultiplier_value _ _ _ Q ρ profile N σ J i masks A x u

end DescriptorJetSymbol
end Falconer

end OAI
