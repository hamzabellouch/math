import OAI.Analysis.CircleDomains.Transfer.TransportedRealCoordinates

namespace OAI

/-!
# Integrability in the metric energy change of variables

The Jacobian theorem gives integrability equivalence as well as equality
of integrals. This supplies the target finite-energy hypotheses required
by parallel-line payment from the actual source energy estimates.
-/

open Set Function Filter Matrix MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace FiniteTransfer

theorem integrable_covectorEnergy_change_variables_iff
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (A x) s x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0)
    (v : (ℝ × ℝ) → Fin 2 → ℝ) (g : (ℝ × ℝ) → PlanarMetric)
    (hPD : ∀ x ∈ s, (g (f x)).PosDef)
    (c : (ℝ × ℝ) → ℝ) (hc : ∀ x ∈ s, 0 < c x) :
    IntegrableOn (fun y => covectorEnergy (v y) (g y)) (f '' s) ↔
      IntegrableOn (fun x => covectorEnergy ((planeDerivativeMatrix (A x))ᵀ *ᵥ v (f x))
        (c x • ((planeDerivativeMatrix (A x))ᵀ * g (f x) * planeDerivativeMatrix (A x)))) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  simp only [smul_eq_mul]
  have hB : (planeDerivativeMatrix (A x)).det ≠ 0 := by
    simpa only [det_planeDerivativeMatrix] using hdet x hx
  simpa only [det_planeDerivativeMatrix] using
    (covectorEnergy_conformal_pullback (v (f x)) (hPD x hx) hB (hc x hx)).symm

theorem integrable_circleEnergy_change_variables_iff
    {s U : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hU : IsOpen U)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivAt f (A x) x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0) (hmap : MapsTo f s U)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u U)
    (g : (ℝ × ℝ) → PlanarMetric) (c : (ℝ × ℝ) → ℝ)
    (hc : ∀ x ∈ s, 0 < c x)
    (hg : ∀ x ∈ s, g x = c x • ((planeDerivativeMatrix (A x))ᵀ * planeDerivativeMatrix (A x))) :
    IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) (f '' s) ↔
      IntegrableOn (fieldEnergy (circleGradient (u ∘ f)) g) s := by
  have heq := integrable_covectorEnergy_change_variables_iff hs f A
    (fun x hx => (hf x hx).hasFDerivWithinAt) hinj hdet
    (fun y => ![(circleGradient u y).1, (circleGradient u y).2]) (fun _ => 1)
    (fun _ _ => Matrix.PosDef.one) c hc
  refine heq.trans (integrableOn_congr_fun ?_ hs)
  intro x hx
  have hvec := circleGradient_comp_vector hU hu (hf x hx).differentiableAt (hmap hx)
  rw [(hf x hx).fderiv] at hvec
  simp only [mul_one]
  rw [← hg x hx, ← hvec]
  rfl

end FiniteTransfer

theorem integrable_filled_circleEnergy_metric_sphere_map_iff
    {s W : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hW : IsOpen W)
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hsU : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty)
    (hmap : MapsTo (sphereRealMap f) s W)
    (u F : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u W)
    (hcoordinate : ∀ x ∈ s, (u ∘ sphereRealMap f) =ᶠ[𝓝 x] F) :
    IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) (sphereRealMap f '' s) ↔
      IntegrableOn (fieldEnergy (circleGradient F) g) s := by
  classical
  have hdata (x : ℝ × ℝ) (hx : x ∈ s) :=
    metric_conformal_real_chart (hf _ (hsU x hx)) (hg x hx) (hfinite x hx)
  let c (x : ℝ × ℝ) : ℝ := if hx : x ∈ s then (hdata x hx).2.2.choose else 1
  have heq := integrable_circleEnergy_change_variables_iff hs hW (sphereRealMap f)
    (fun x => fderiv ℝ (sphereRealMap f) x)
    (fun x hx => (hdata x hx).1.hasFDerivAt)
    (sphereRealMap_injOn hinj hsU hfinite)
    (fun x hx => (hdata x hx).2.1.ne') hmap u hu g c
    (fun x hx => by simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.1)
    (fun x hx => by simpa only [c, dite_eq_left hx] using (hdata x hx).2.2.choose_spec.2)
  refine heq.trans (integrableOn_congr_fun ?_ hs)
  intro x hx
  simp only [fieldEnergy, circleGradient_congr_of_eventuallyEq (hcoordinate x hx)]

theorem integrable_transported_real_coordinate_iff
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOU : O ⊆ realChartDomain U)
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F O)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsO : s ⊆ O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p) (hg : ∀ x ∈ s, (g x).PosDef) :
    IntegrableOn (gradientEnergy (F ∘ sphereRealMap fi) (fun _ => 1))
      (sphereRealMap f '' s) ↔ IntegrableOn (gradientEnergy F g) s := by
  obtain ⟨hW, hv, hpull⟩ := transported_real_coordinate heq hV hUinf hfix hO hOU F hF
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hOU (hsO hx))).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono (hsO.trans hOU))
  have henergy := integrable_filled_circleEnergy_metric_sphere_map_iff hs hW
    heq.bijOn.injOn (fun x hx => hOU (hsO hx)) hf hg
    (fun x hx => finite_image_of_fixes_infty heq.bijOn.injOn hUinf hfix (hOU (hsO hx)))
    (fun x hx => mem_image_of_mem _ (hsO hx))
    (fun x => ((F ∘ sphereRealMap fi) x : UnitAddCircle))
    (fun x => (F x : UnitAddCircle)) (smoothCircleOn_coe hW hv)
    (fun x hx => (hpull x (hsO hx)).fun_comp (fun t : ℝ => (t : UnitAddCircle)))
  calc
    _ ↔ IntegrableOn (fieldEnergy
        (circleGradient (fun x => ((F ∘ sphereRealMap fi) x : UnitAddCircle)))
        (fun _ => 1)) (sphereRealMap f '' s) := by
      apply integrableOn_congr_fun _ himage
      intro y hy
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hW hv (image_mono hsO hy)]
    _ ↔ IntegrableOn (fieldEnergy (circleGradient (fun x => (F x : UnitAddCircle))) g) s :=
      henergy
    _ ↔ _ := by
      apply integrableOn_congr_fun _ hs
      intro x hx
      change covectorEnergy _ _ = covectorEnergy _ _
      rw [circleGradient_coe_eq_planarGradient hO hF (hsO hx)]

end CircleDomainRigidity

end

end OAI
