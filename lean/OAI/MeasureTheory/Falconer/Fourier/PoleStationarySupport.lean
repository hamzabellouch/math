import OAI.MeasureTheory.Falconer.Fourier.PoleCutoffs
import OAI.MeasureTheory.Falconer.Fourier.ChartJetOperators
import OAI.MeasureTheory.Falconer.Angular.CapCoordinates

namespace OAI

/-! # Actual support conditions for the pole expansion

Geometric support in a radius-1/4 cap implies all support conditions in
the quadratic stationary theorem. The ambient pole bump is invisible to
the actual coefficient jets at its center.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem gnomonic_small_cap_coordinates {n : ℕ} (x : Space n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hcap : ‖(gnomonicChart x : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ δ) :
    ‖x‖ ≤ 2*δ := by
  let p := coordinateJoin (0 : Space n) 1
  let h := coordinateJoin x 0
  have hp : ‖p‖ = 1 := by
    change ‖coordinateJoin (0 : Space n) 1‖ = 1
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have horth : inner ℝ p h = 0 := by simp [p,h,coordinateJoin_inner]
  have hh : ‖h‖ = ‖x‖ := by
    change ‖coordinateJoin x 0‖ = ‖x‖
    have he := coordinateJoin_norm_sq x 0
    simp only [zero_pow (by decide : 2 ≠ 0),zero_add] at he
    nlinarith [norm_nonneg (coordinateJoin x 0),norm_nonneg x]
  have hsplit : northLift x = p+h := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [p,h,northLift,coordinateJoin_eq]
  have hc : ‖‖p+h‖⁻¹ • (p+h)-p‖ ≤ δ := by
    simpa only [gnomonicChart,hsplit] using hcap
  rw [← hh]
  exact small_cap_chart_displacement hp horth hδ hδsmall hc

private theorem fixed_cap_mem_north {n : ℕ} (w : Sphere (n+1))
    (hw : ‖(w : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ 1/4) :
    w ∈ northHemisphere n := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have hi : inner ℝ (w : Space (n+1)) (coordinateJoin (0 : Space n) 1) =
      (w : Space (n+1)) 0 := by
    rw [PiLp.inner_apply,Fin.sum_univ_succ]
    simp [coordinateJoin_eq]
  have he := norm_sub_sq_real (w : Space (n+1)) (coordinateJoin (0 : Space n) 1)
  rw [sphere_norm,hp,hi] at he
  change 0 < (w : Space (n+1)) 0
  nlinarith [norm_nonneg ((w : Space (n+1))-coordinateJoin (0 : Space n) 1)]

theorem rotated_cap_quadratic_support (m : ℕ) (e : Sphere (m+3))
    (b : Sphere (m+3) → ℂ)
    (hcap : ∀ w, b w ≠ 0 → ‖(w : Space (m+3))-(e : Space (m+3))‖ ≤ 1/4) :
    let T := stationaryPoleRotation e
    (∀ w, w ∉ northHemisphere (m+2) → b (sphereMap T w) = 0) ∧
    (∀ x : Space (m+2), x ∉ quadraticToGnomonic '' ball (0 : Space (m+2)) 1 →
      b (sphereMap T (gnomonicChart x)) = 0) ∧
    (∀ u : Space (m+2), 1/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (sphereMap T (gnomonicChart (quadraticToGnomonic u))) = 0) := by
  let T := stationaryPoleRotation e
  have htransport (w : Sphere (m+3)) (hw : b (sphereMap T w) ≠ 0) :
      ‖(w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1‖ ≤ 1/4 := by
    have he : T (coordinateJoin (0 : Space (m+2)) 1) = (e : Space (m+3)) := by
      rw [← gnomonicChart_zero_pole]
      exact stationaryPoleRotation_pole e
    calc
      _ = ‖T ((w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1)‖ := (T.norm_map _).symm
      _ = ‖(sphereMap T w : Space (m+3))-(e : Space (m+3))‖ := by rw [T.map_sub,he]; rfl
      _ ≤ _ := hcap _ hw
  refine ⟨?_,?_,?_⟩
  · intro w hw
    by_contra hb
    exact hw (fixed_cap_mem_north w (htransport w hb))
  · intro x hx
    by_contra hb
    have hc := gnomonic_small_cap_coordinates x (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1/2) (htransport _ hb)
    exact hx (quadraticToGnomonic_image_smallBall x (by linarith))
  · intro u hu hu1
    by_contra hb
    have hc := htransport _ hb
    rw [gnomonicChart_quadraticToGnomonic hu1,
      quadraticSpherePoint_dist_pole (hu1.le.trans (by norm_num))] at hc
    linarith

noncomputable def poleLocalizedAmbient {d : ℕ} (e : Sphere d)
    (B : Space d → ℂ) (x : Space d) : ℂ := (poleCutoff e x : ℂ)*B x

theorem poleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (poleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).mul hB

theorem poleLocalizedAmbient_cap {d : ℕ} (e : Sphere d) (B : Space d → ℂ)
    (w : Sphere d) (hw : poleLocalizedAmbient e B w ≠ 0) :
    ‖(w : Space d)-(e : Space d)‖ ≤ 1/4 := by
  apply (poleCutoff_support e w _).le
  intro hz
  exact hw (by simp only [poleLocalizedAmbient,hz,Complex.ofReal_zero,zero_mul])

theorem poleLocalizedAmbient_coefficient (m j : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    actualStationaryCoefficient m j (poleLocalizedAmbient e B) e =
      actualStationaryCoefficient m j B e := by
  apply actualStationaryCoefficient_local m j e
  have he := (capBump (1/4) (by norm_num) e).eventuallyEq_one
  filter_upwards [he] with x hx
  change capBump (1/4) (by norm_num) e x = (1 : ℝ) at hx
  simp only [poleLocalizedAmbient,poleCutoff,hx,Complex.ofReal_one,one_mul]

theorem poleCutoff_opposite_neg {d : ℕ} (e : Sphere d) (x : Space d) :
    poleCutoff (oppositePole e) (-x) = poleCutoff e x := by
  simp only [poleCutoff,ContDiffBump.apply,capBump,oppositePole_coe]
  have he : ((1/4 : ℝ)/2)⁻¹ • (-x-(-(e : Space d))) =
      -(((1/4 : ℝ)/2)⁻¹ • (x-(e : Space d))) := by module
  rw [he,ContDiffBumpBase.symmetric]

/-- The incoming pole uses the same smooth direction patch as the outgoing
pole, applied to the conjugated antipodal amplitude. -/
theorem poleLocalized_opposite_oscillation {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (B : Space d → ℂ) :
    sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w) =
      star (sphereOscillation Λ e
        (fun w => poleLocalizedAmbient e (fun x => star (B (-x))) w)) := by
  have heq : sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w) =
      sphereOscillation (-Λ) e (fun w => poleLocalizedAmbient e (fun x => B (-x)) w) := by
    rw [sphereOscillation,← sphere_integral_rotation (LinearIsometryEquiv.neg ℝ)]
    unfold sphereOscillation
    apply integral_congr_ae
    filter_upwards with w
    change Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (-(w : Space d)) (e : Space d) : ℂ)) *
      ((poleCutoff (oppositePole e) (-(w : Space d)) : ℂ)*B (-(w : Space d))) = _
    rw [poleCutoff_opposite_neg,inner_neg_left]
    have hp : Complex.I*(Λ : ℂ)*((-inner ℝ (w : Space d) (e : Space d) : ℝ) : ℂ) =
        Complex.I*((-Λ : ℝ) : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ) := by
      push_cast
      ring
    rw [hp]
    rfl
  rw [heq,sphereOscillation_neg]
  congr 1
  congr 1
  funext w
  simp [poleLocalizedAmbient]

theorem poleLocalized_quadratic_contDiff (m : ℕ) (e : Sphere (m+3))
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticAmplitude_contDiff
  · let T := stationaryPoleRotation e
    have h : ContDiffOn ℝ ∞
        (fun u => poleLocalizedAmbient e B (T (quadraticSpherePoint u)))
        (ball (0 : Space (m+2)) 1) := by
      intro u hu
      have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
      exact ((poleLocalizedAmbient_contDiff e hB).comp
        T.toContinuousLinearMap.contDiff).contDiffAt.comp u
          (quadraticSpherePoint_contDiffAt (hu1.trans (by norm_num))) |>.contDiffWithinAt
    apply h.congr
    intro u hu
    have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
    change poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic u))) = _
    rw [gnomonicChart_quadraticToGnomonic hu1]
  · exact (rotated_cap_quadratic_support m e (fun w => poleLocalizedAmbient e B w)
      (poleLocalizedAmbient_cap e B)).2.2

/-- The local expansion has the original-amplitude coefficients.
All support and smoothness requirements are discharged by the fixed bump.
The remaining derivative bound is the explicit Euclidean jet budget. -/
theorem poleLocalized_stationary_remainder
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ E : ℝ, 0 ≤ E →
      (∀ k ≤ 2*J+(m+2)+1, ∀ u,
        ‖iteratedFDeriv ℝ k (quadraticAmplitude m
          (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) u‖ ≤ E) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(Complex.I*(Λ : ℂ))) *
          sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w) -
        ∑ j ∈ Finset.range J, ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
          actualStationaryCoefficient m j B e‖ ≤ C*Λ^(-(J : ℝ))*E := by
  obtain ⟨C,hC,hrem⟩ := quadraticSphereOscillation_remainder hgnomonic hquadratic m J hJ
  refine ⟨C,hC,?_⟩
  intro e B hB E hE hder Λ hΛ
  let b : Sphere (m+3) → ℂ := fun w => poleLocalizedAmbient e B w
  have hb : Measurable b :=
    (poleLocalizedAmbient_contDiff e hB).continuous.measurable.comp
      continuous_subtype_val.measurable
  obtain ⟨hs,hchart,_⟩ := rotated_cap_quadratic_support m e b (poleLocalizedAmbient_cap e B)
  have hr := hrem (fun w => b (sphereMap (stationaryPoleRotation e) w))
    (hb.comp (continuous_sphereMap _).measurable) hs hchart
    (poleLocalized_quadratic_contDiff m e hB) E hE hder Λ hΛ
  have hj (j : ℕ) : quadraticJetCoefficient j (quadraticAmplitude m
      (fun w => b (sphereMap (stationaryPoleRotation e) w))) =
      actualStationaryCoefficient m j B e := by
    rw [← actualStationaryCoefficient_eq m j (poleLocalizedAmbient e B) e,
      poleLocalizedAmbient_coefficient]
  simpa only [sphereOscillation_rotate,hj] using hr

end Falconer

end OAI
