import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCurveTangencies
import OAI.Geometry.SurfaceImmersion.Atlas.ConvexQuadraticPhase

namespace OAI

/-! The generic-parameter statement for the actual quadratic phases used
by the primitive construction, retaining finite tangencies on compact arcs. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry

lemma quadraticPhaseAlongCurve_hasDerivAt {u : ℝ → CurvePlane} {v ell : CurvePlane}
    {L t : ℝ} (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => convexQuadraticPhase ell L (u s))
      ((ell.1+L*(u t).1)*v.1+(ell.2+L*(u t).2)*v.2) t := by
  have hd := (convexQuadraticPhase_hasFDerivAt ell L (u t)).comp_hasDerivAt t hu
  convert hd using 1
  · rfl
  · simp only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

lemma quadraticPhaseAlongCurve_deriv (u : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u)
    (ell : CurvePlane) (L : ℝ) :
    deriv (fun s => convexQuadraticPhase ell L (u s)) =
      fun t => curvePhaseVelocity u (deriv u) L t ell := by
  funext t
  exact (quadraticPhaseAlongCurve_hasDerivAt (ell := ell) (L := L)
    ((hu.differentiable (by simp) t).hasDerivAt)).deriv

theorem exists_finite_critical_quadratic_phases {α : Type*} [Countable α]
    (u : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a))
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0) (L : α → ℝ)
    (U : Set CurvePlane) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U, ∀ a,
      (K a ∩ {t | deriv (fun s => convexQuadraticPhase ell (L a) (u a s)) t = 0}).Finite ∧
      ∀ t ∈ K a, deriv (fun s => convexQuadraticPhase ell (L a) (u a s)) t = 0 →
        deriv (deriv (fun s => convexQuadraticPhase ell (L a) (u a s))) t ≠ 0 := by
  let v := fun a => deriv (u a)
  let w := fun a => deriv (v a)
  have hv : ∀ a, ContDiff ℝ ∞ (v a) := fun a => (contDiff_infty_iff_deriv.mp (hu a)).2
  have hdu : ∀ a t, HasDerivAt (u a) (v a t) t := fun a t =>
    ((hu a).differentiable (by simp) t).hasDerivAt
  have hdv : ∀ a t, HasDerivAt (v a) (w a t) t := fun a t =>
    ((hv a).differentiable (by simp) t).hasDerivAt
  obtain ⟨ell,hell,hn⟩ := exists_nondegenerate_curve_phases u v w hu hv hdu hdv L U hU hne
  refine ⟨ell,hell,fun a => ?_⟩
  have hfirst := quadraticPhaseAlongCurve_deriv (u a) (hu a) ell (L a)
  have hsecond : deriv (deriv (fun s => convexQuadraticPhase ell (L a) (u a s))) =
      fun t => curvePhaseAcceleration (u a) (v a) (w a) (L a) t ell := by
    rw [hfirst]
    funext t
    exact (curvePhaseVelocity_hasDerivAt (L := L a) (ell := ell) (hdu a t) (hdv a t)).deriv
  constructor
  · simpa only [hfirst] using finite_nondegenerate_curve_tangencies (u a) (v a) (w a)
      (hu a) (hv a) (hdu a) (hdv a) (L a) ell (hK a) (hregular a) (hn a)
  · intro t ht hc
    rw [hsecond]
    apply hn a t (hregular a t ht)
    simpa only [hfirst] using hc

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
