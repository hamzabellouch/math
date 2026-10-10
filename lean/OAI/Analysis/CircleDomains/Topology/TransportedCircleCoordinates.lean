import OAI.Analysis.CircleDomains.Sobolev.SmoothRealSphereMaps

namespace OAI

/-!
# Actual pushed-forward circle coordinates

A smooth coordinate on an open part of the source is composed with the
actual inverse of a normalized smooth sphere equivalence. Its target
domain is the actual image of that source region. It is smooth there,
its pullback is locally the original coordinate, and the full
Dirichlet change-of-variables formula follows.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem smoothCircleOn_comp
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u : H → UnitAddCircle} {U : Set H} (hu : SmoothCircleOn u U)
    {f : E → H} {V : Set E} (hf : ∀ x ∈ V, ContDiffAt ℝ ∞ f x)
    (hmap : MapsTo f V U) : SmoothCircleOn (u ∘ f) V := by
  intro x hx a hcut
  exact (hu (f x) (hmap hx) a hcut).comp x (hf x hx)

theorem transported_circle_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hequiv : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → UnitAddCircle) (hF : SmoothCircleOn F O) :
    let W := sphereRealMap f '' O
    let v := F ∘ sphereRealMap fi
    IsOpen W ∧ SmoothCircleOn v W ∧
      (∀ x ∈ O, (v ∘ sphereRealMap f) =ᶠ[𝓝 x] F) := by
  dsimp only
  refine ⟨hequiv.isOpen_real_image hUinf hfix hV hO hOU, ?_, ?_⟩
  · apply smoothCircleOn_comp hF
    · rintro y ⟨x, hx, rfl⟩
      exact hequiv.real_smooth_inv hUinf hfix ((hequiv.real_bijOn hUinf hfix).mapsTo (hOU hx))
    · rintro y ⟨x, hx, rfl⟩
      rwa [hequiv.real_left_inv hUinf hfix (hOU hx)]
  · intro x hx
    filter_upwards [hO.mem_nhds hx] with y hy
    change F (sphereRealMap fi (sphereRealMap f y)) = F y
    rw [hequiv.real_left_inv hUinf hfix (hOU hy)]

theorem integral_transported_circle_coordinate
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hequiv : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → UnitAddCircle) (hF : SmoothCircleOn F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    (∫ y in sphereRealMap f '' s,
      fieldEnergy (circleGradient (F ∘ sphereRealMap fi)) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient F) g x := by
  obtain ⟨hW, hv, hpull⟩ := transported_circle_coordinate hequiv hV hUinf hfix hO hOU F hF
  exact integral_filled_circleEnergy_normalized_sphere_map hs hW hequiv.bijOn.injOn
    hUinf hfix (fun x hx => hOU (hsO hx)) hf hg
    (fun x hx => mem_image_of_mem _ (hsO hx)) (F ∘ sphereRealMap fi) F hv
    (fun x hx => hpull x (hsO hx))

end CircleDomainRigidity

end

end OAI
