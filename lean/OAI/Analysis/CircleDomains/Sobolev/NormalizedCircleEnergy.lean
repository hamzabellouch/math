import OAI.Analysis.CircleDomains.Modulus.NormalizedMetricUniformization
import OAI.Analysis.CircleDomains.Sobolev.SphereCircleEnergy

namespace OAI

/-!
# Energy transport for circle models fixing infinity

Fixing infinity eliminates the exceptional target point from the finite
chart. Thus the change-of-variables formula applies on every measurable
source set in the finite chart, including the whole localized tail.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem integral_filled_circleEnergy_normalized_sphere_map
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    (∫ y in sphereRealMap f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x :=
  integral_filled_circleEnergy_metric_sphere_map hs hW hinj hsU hf hg
    (fun x hx => finite_image_of_fixes_infty hinj hU hfix (hsU x hx)) hmap u F hu hcoordinate

end CircleDomainRigidity

end

end OAI
