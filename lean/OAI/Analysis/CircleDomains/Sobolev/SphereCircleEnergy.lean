import OAI.Analysis.CircleDomains.Sobolev.SphereRealDifferential
import OAI.Analysis.CircleDomains.Sobolev.CircleEnergyChange
import OAI.Analysis.CircleDomains.Sobolev.CircleEnergy

namespace OAI

/-!
# Energy transport through a metric-conformal sphere map

On the finite charts, the actual sphere map and actual intrinsic circle
coordinate satisfy the Dirichlet change-of-variables formula. The source
set may be any measurable part of a mask or of a localized tail.
-/

open Set Filter Matrix MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem integral_circleEnergy_metric_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient (u ∘ sphereRealMap f)) g x := by
  classical
  have hdata (x : ℝ × ℝ) (hx : x ∈ s) :=
    metric_conformal_real_chart (hf _ (hsU x hx)) (hg x hx) (hfinite x hx)
  let c (x : ℝ × ℝ) : ℝ := if hx : x ∈ s then (hdata x hx).2.2.choose else 1
  apply integral_circleEnergy_change_variables hs hW (sphereRealMap f)
    (fun x => fderiv ℝ (sphereRealMap f) x)
    (fun x hx => (hdata x hx).1.hasFDerivAt)
    (sphereRealMap_injOn hinj hsU hfinite)
    (fun x hx => (hdata x hx).2.1.ne') hmap u hu g c
  · intro x hx
    simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.1
  · intro x hx
    simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.2

/-- The same formula for a source coordinate identified locally with the
pullback. This is the equality used for the filled coordinates. -/
theorem integral_filled_circleEnergy_metric_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x := by
  refine (integral_circleEnergy_metric_sphere_map hs hW hinj hsU hf hg hfinite hmap u hu).trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [fieldEnergy, circleGradient_congr_of_eventuallyEq (hcoordinate x hx)]

end CircleDomainRigidity

end

end OAI
