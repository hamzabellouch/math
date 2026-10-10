import OAI.Geometry.SurfaceImmersion.Atlas.IndependentPhaseProjections
import OAI.Geometry.SurfaceImmersion.Atlas.CompactCurvePhaseParameters
import OAI.Geometry.SurfaceImmersion.Atlas.FiniteCriticalQuadraticPhases

namespace OAI

/-! One finite phase family simultaneously has nondegenerate boundary
critical points and the required independent crossing covectors. All
parameters can be chosen in an arbitrarily prescribed open neighborhood. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

theorem exists_generic_independent_phases
    (index : α → ι) (u : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a))
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0) (L : α → ℝ)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (offset₁ offset₂ : κ → CurvePlane)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ a, (K a ∩ {t | deriv (fun s =>
        convexQuadraticPhase (ell (index a)) (L a) (u a s)) t = 0}).Finite) ∧
      (∀ a t, t ∈ K a → deriv (fun s =>
        convexQuadraticPhase (ell (index a)) (L a) (u a s)) t = 0 →
          deriv (deriv (fun s =>
            convexQuadraticPhase (ell (index a)) (L a) (u a s))) t ≠ 0) ∧
      (∀ k, covectorDet (ell (first k)+offset₁ k) (ell (second k)+offset₂ k) ≠ 0) := by
  let v := fun a => deriv (u a)
  let w := fun a => deriv (v a)
  have hv : ∀ a, ContDiff ℝ ∞ (v a) := fun a => (contDiff_infty_iff_deriv.mp (hu a)).2
  have hw : ∀ a, ContDiff ℝ ∞ (w a) := fun a => (contDiff_infty_iff_deriv.mp (hv a)).2
  have hdu : ∀ a t, HasDerivAt (u a) (v a t) t := fun a t =>
    ((hu a).differentiable (by simp) t).hasDerivAt
  have hdv : ∀ a t, HasDerivAt (v a) (w a t) t := fun a t =>
    ((hv a).differentiable (by simp) t).hasDerivAt
  let O : Sum α κ → Set (ι → CurvePlane)
    | .inl a => (fun ell => ell (index a)) ⁻¹'
        goodCompactCurvePhases (u a) (v a) (w a) (L a) (K a)
    | .inr k => {ell | covectorDet (ell (first k)+offset₁ k) (ell (second k)+offset₂ k) ≠ 0}
  have ho : ∀ s, IsOpen (O s) := by
    intro s
    cases s with
    | inl a =>
        exact (goodCompactCurvePhases_open (u a) (v a) (w a) (L a)
        (hu a).continuous (hv a).continuous (hw a).continuous (hK a)).preimage
          (show Continuous (fun ell : ι → CurvePlane => ell (index a)) from continuous_apply (index a))
    | inr k =>
        exact (independent_covectorDet_open_dense (hdistinct k) (offset₁ k) (offset₂ k)).1
  have hd : ∀ s, Dense (O s) := by
    intro s
    cases s with
    | inl a =>
        exact (goodCompactCurvePhases_dense (u a) (v a) (w a) (L a)
        (hu a) (hv a) (hdu a) (hdv a) (K a) (hregular a)).preimage
          ((ContinuousLinearMap.proj (index a) : (ι → CurvePlane) →L[ℝ] CurvePlane).isOpenMap
            (phaseProjection_surjective (index a)))
    | inr k =>
        exact (independent_covectorDet_open_dense (hdistinct k) (offset₁ k) (offset₂ k)).2
  obtain ⟨ell,hell,he⟩ := (dense_iInter_of_isOpen ho hd).inter_open_nonempty U hU hne
  have hn (a : α) : ∀ t ∈ K a, curvePhaseVelocity (u a) (v a) (L a) t (ell (index a)) = 0 →
      curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)) ≠ 0 :=
    mem_iInter.mp he (Sum.inl a)
  have hfirst (a : α) := quadraticPhaseAlongCurve_deriv (u a) (hu a) (ell (index a)) (L a)
  have hsecond (a : α) : deriv (deriv (fun s =>
      convexQuadraticPhase (ell (index a)) (L a) (u a s))) =
      fun t => curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)) := by
    rw [hfirst]
    funext t
    exact (curvePhaseVelocity_hasDerivAt (L := L a) (ell := ell (index a))
      (hdu a t) (hdv a t)).deriv
  refine ⟨ell,hell,?_,?_,?_⟩
  · intro a
    rw [hfirst]
    exact finite_compact_simple_zeros
      (df := fun t => curvePhaseAcceleration (u a) (v a) (w a) (L a) t (ell (index a)))
      (by
        have huc := (hu a).continuous
        have hvc : Continuous (deriv (u a)) := (hv a).continuous
        dsimp [curvePhaseVelocity]
        fun_prop) (hK a)
      (fun t _ => curvePhaseVelocity_hasDerivAt (hdu a t) (hdv a t)) (hn a)
  · intro a t ht hc
    rw [hsecond]
    apply hn a t ht
    simpa only [hfirst] using hc
  · intro k
    exact mem_iInter.mp he (Sum.inr k)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
