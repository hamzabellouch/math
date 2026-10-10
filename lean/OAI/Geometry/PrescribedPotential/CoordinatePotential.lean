import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.CoordinateBalls

namespace OAI

/-! Coordinate Potential. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory Matrix
open scoped ContDiff InnerProductSpace ComplexOrder Matrix.Norms.Elementwise
namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance coordinatePotentialRealIP (d : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))
local notation "e" => EuclideanSpace.equiv (Fin d) ℂ

lemma hessian_coord_comp_at {f : (Fin d → ℂ) → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (e x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x v w =
      fderiv ℝ (fderiv ℝ f) (e x) (e v) (e w) := by
  let er := (EuclideanSpace.equiv (Fin d) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have her : ContDiff ℝ ∞ e := er.contDiff
  have hd : fderiv ℝ e = fun _ => (er : E →L[ℝ] (Fin d → ℂ)) := by
    funext y
    exact er.hasFDerivAt.fderiv
  rw [PotentialKaehler.second_derivative_comp her.contDiffAt hf v w, hd]
  simp
  rfl

lemma levi_coord_pair_at {f : (Fin d → ℂ) → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (e x)) (v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x v v +
      fderiv ℝ (fderiv ℝ (f ∘ e)) x (Complex.I • v) (Complex.I • v) =
        4 * inner ℝ ((PotentialKaehler.potentialMatrix f (e x)).toEuclideanLin v) v := by
  rw [hessian_coord_comp_at hf, hessian_coord_comp_at hf]
  rw [real_inner_comm, real_inner_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  change _ = 4 * (star (e v) ⬝ᵥ ((PotentialKaehler.potentialMatrix f (e x)) *ᵥ (e v))).re
  rw [PotentialKaehler.potentialMatrix, PotentialKaehler.hermitianPartMatrix_pair]
  simp only [map_smul, PotentialKaehler.hermitianPart]
  ring

lemma matrix_quadratic_le (H : Matrix (Fin d) (Fin d) ℂ) (v : E) :
    inner ℝ (H.toEuclideanLin v) v ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) H‖ * ‖v‖^2 := by
  apply (real_inner_le_norm _ _).trans
  have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) H).le_opNorm v
  change ‖H.toEuclideanLin v‖ ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) H‖ * ‖v‖ at h
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg v)]

lemma matrix_quadratic_nonneg {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.PosSemidef) (v : E) :
    0 ≤ inner ℝ (H.toEuclideanLin v) v := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ)]
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr hH).re_inner_nonneg_left v
end PotentialABP

namespace Anticanonical.SourceSmooth
open EllipticKernel PotentialABP
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local instance sourceCoordinateRealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
namespace CoordinateBall
variable (p : CoordinateBall A)

def bump : ContDiffBump p.center where
  rIn := 7*p.radius/2
  rOut := 4*p.radius
  rIn_pos := by linarith [p.radius_pos]
  rIn_lt_rOut := by linarith [p.radius_pos]

def extension (φ : SmoothRealFunction A) : EC d → ℝ :=
  fun z => p.bump z * φ.value ((A.euclideanChart p.index).symm z)

lemma extension_smooth (φ : SmoothRealFunction A) : ContDiff ℝ ∞ (p.extension φ) := by
  apply MetricLocalization.smooth_bump_smul p.bump
  intro z hz
  have hz' : z ∈ (A.euclideanChart p.index).target := p.closure_sub
    (by simpa only [bump, ContDiffBump.tsupport_eq] using hz)
  exact (φ.euclidean_smooth p.index).contDiffAt
    (by simpa only [ComplexAtlas.euclideanChart_target] using
      (A.euclideanChart p.index).open_target.mem_nhds hz')

lemma extension_eventuallyEq (φ : SmoothRealFunction A) {z : EC d}
    (hz : z ∈ closedBall p.center (3*p.radius)) :
    p.extension φ =ᶠ[𝓝 z] (φ.value ∘ (A.euclideanChart p.index).symm) := by
  have hz' : z ∈ ball p.center (7*p.radius/2) := by
    have hd : dist z p.center ≤ 3*p.radius := hz
    change dist z p.center < 7*p.radius/2
    linarith [p.radius_pos]
  filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
  have hone : p.bump y = 1 := p.bump.one_of_mem_closedBall
    (show dist y p.center ≤ 7*p.radius/2 from (show dist y p.center < 7*p.radius/2 from hy).le)
  simp [extension, hone]

lemma extension_eq (φ : SmoothRealFunction A) {z : EC d}
    (hz : z ∈ closedBall p.center (3*p.radius)) :
    p.extension φ z = φ.value ((A.euclideanChart p.index).symm z) :=
  (p.extension_eventuallyEq φ hz).eq_of_nhds

lemma metric_bound (g : KaehlerMetric A) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z ∈ closedBall p.center (3*p.radius), ∀ v : EC d,
      inner ℝ ((g.matrix p.index (coordinateEquiv d z)).toEuclideanLin v) v ≤ C*‖v‖^2 := by
  have hc : ContinuousOn (fun z : EC d =>
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) (g.matrix p.index (coordinateEquiv d z)))
      (closedBall p.center (3*p.radius)) := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp_continuousOn
    have hs : ContinuousOn (fun z : EC d => g.matrix p.index (coordinateEquiv d z))
        (A.euclideanChart p.index).target := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      have hij := (contDiffOn_pi.mp (contDiffOn_pi.mp (g.smooth p.index) i) j).continuousOn
      rw [ComplexAtlas.euclideanChart_target]
      convert hij.comp (coordinateEquiv d).continuous.continuousOn
        (show Set.MapsTo (coordinateEquiv d)
          ((coordinateEquiv d) ⁻¹' (A.chart p.index).target) (A.chart p.index).target from
            fun _ hz => hz) using 1; rfl
    exact hs.mono (fun z hz => p.closure_sub
      (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz))
  obtain ⟨C, hC⟩ := (isCompact_closedBall p.center (3*p.radius)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun z hz v => ?_⟩
  exact (matrix_quadratic_le _ v).trans
    (mul_le_mul_of_nonneg_right ((hC z hz).trans (le_max_left _ _)) (sq_nonneg _))

lemma extension_levi_lower (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hφ : g.PositivePotential φ) {C : ℝ}
    (hC : ∀ z ∈ closedBall p.center (3*p.radius), ∀ v : EC d,
      inner ℝ ((g.matrix p.index (coordinateEquiv d z)).toEuclideanLin v) v ≤ C*‖v‖^2)
    {z : EC d} (hz : z ∈ closedBall p.center (3*p.radius)) (v : EC d) :
    -(4*C*‖v‖^2) ≤ fderiv ℝ (fderiv ℝ (p.extension φ)) z v v +
      fderiv ℝ (fderiv ℝ (p.extension φ)) z (Complex.I • v) (Complex.I • v) := by
  have hzt : z ∈ (A.euclideanChart p.index).target :=
    p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz)
  have hzt' : coordinateEquiv d z ∈ (A.chart p.index).target := by simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using hzt
  have he := ((p.extension_eventuallyEq φ hz).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [he]
  have hl := levi_coord_pair_at ((φ.smooth p.index).contDiffAt
    ((A.chart p.index).open_target.mem_nhds hzt')) v
  have hn := matrix_quadratic_nonneg (hφ p.index _ hzt').posSemidef v
  rw [map_add, LinearMap.add_apply, inner_add_left] at hn
  change fderiv ℝ (fderiv ℝ (φ.value ∘ (A.euclideanChart p.index).symm)) z v v +
      fderiv ℝ (fderiv ℝ (φ.value ∘ (A.euclideanChart p.index).symm)) z (Complex.I • v) (Complex.I • v) =
      4*inner ℝ ((φ.hessian p.index (coordinateEquiv d z)).toEuclideanLin v) v at hl
  rw [hl]
  linarith [hC z hz v]
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
