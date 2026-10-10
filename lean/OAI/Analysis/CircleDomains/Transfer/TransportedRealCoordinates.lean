import OAI.Analysis.CircleDomains.Topology.TransportedCircleCoordinates

namespace OAI

/-!
# Real barrier coordinates on normalized circle models

Real coordinates are transported by the actual smooth inverse. The
ordinary real gradient has the same energy as its intrinsic circle
differential, so the proved change-of-variables formula applies without
discarding the real lift or its values.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O) :
    IsOpen (sphereRealMap f '' O) ∧
      ContDiffOn ℝ ∞ (F ∘ sphereRealMap fi) (sphereRealMap f '' O) ∧
      ∀ x ∈ O, ((F ∘ sphereRealMap fi) ∘ sphereRealMap f) =ᶠ[𝓝 x] F := by
  refine ⟨heq.isOpen_real_image hUinf hfix hV hO hOU, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    have hix : sphereRealMap fi (sphereRealMap f x) ∈ O := by
      rwa [heq.real_left_inv hUinf hfix (hOU hx)]
    exact ((hF.contDiffAt (hO.mem_nhds hix)).comp _
      (heq.real_smooth_inv hUinf hfix ((heq.real_bijOn hUinf hfix).mapsTo (hOU hx)))).contDiffWithinAt
  · intro x hx
    filter_upwards [hO.mem_nhds hx] with y hy
    change F (sphereRealMap fi (sphereRealMap f y)) = F y
    rw [heq.real_left_inv hUinf hfix (hOU hy)]

theorem circleGradient_coe_eq_planarGradient
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) {F : (ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) {x : ℝ × ℝ} (hx : x ∈ O) :
    circleGradient (fun y => (F y : UnitAddCircle)) x = planarGradient F x := by
  exact (circleGradient_eventuallyEq_lift hO
    ((AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn hF.continuousOn) hF
    (fun _ _ => rfl) hx).self_of_nhds

theorem integral_transported_real_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    (∫ y in sphereRealMap f '' s, gradientEnergy (F ∘ sphereRealMap fi) (fun _ => 1) y) =
      ∫ x in s, gradientEnergy F g x := by
  obtain ⟨hW, hv, _⟩ := transported_real_coordinate heq hV hUinf hfix hO hOU F hF
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hOU (hsO hx))).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono (hsO.trans hOU))
  have henergy := integral_transported_circle_coordinate heq hV hUinf hfix hO hOU
    (fun x => (F x : UnitAddCircle)) (smoothCircleOn_coe hO hF) hs hsO hf hg
  calc
    _ = ∫ y in sphereRealMap f '' s,
        fieldEnergy (circleGradient ((fun x => (F x : UnitAddCircle)) ∘ sphereRealMap fi))
          (fun _ => 1) y := by
      apply setIntegral_congr_fun himage
      intro y hy
      have hyW : y ∈ sphereRealMap f '' O := image_mono hsO hy
      have hd := circleGradient_coe_eq_planarGradient hW hv hyW
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [show circleGradient ((fun x => (F x : UnitAddCircle)) ∘ sphereRealMap fi) y =
        planarGradient (F ∘ sphereRealMap fi) y from hd]
    _ = ∫ x in s, fieldEnergy (circleGradient (fun y => (F y : UnitAddCircle))) g x := henergy
    _ = _ := by
      apply setIntegral_congr_fun hs
      intro x hx
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hO hF (hsO hx)]

end CircleDomainRigidity

end

end OAI
