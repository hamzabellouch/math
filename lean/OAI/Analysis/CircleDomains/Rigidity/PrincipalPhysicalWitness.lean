import OAI.Analysis.CircleDomains.Sobolev.PrincipalWeakDirections
import OAI.Analysis.CircleDomains.Sobolev.ComplexLocalSobolevTransport

namespace OAI

/-! Convert the actual principal weak directional fields to the exact
physical Sobolev witness, retaining the real conjugate Beltrami equation. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def principalWeakDirections (g : PlaneL2) (i : Fin 2) (z : ℂ) : ℂ :=
  complexPlaneCoordinates (EuclideanSpace.single i 1) +
    principalDirectionalCorrection g (complexPlaneCoordinates (EuclideanSpace.single i 1)) z

lemma principalWeakDirections_locallyIntegrable (g : PlaneL2) (i : Fin 2) :
    LocallyIntegrable (principalWeakDirections g i) volume :=
  (locallyIntegrable_const _).add ((Lp.memLp (principalDirectionalCorrection g
    (complexPlaneCoordinates (EuclideanSpace.single i 1)))).locallyIntegrable (by norm_num))

lemma principalWeakDirections_memLp (g : PlaneL2) (R : ℝ) (i : Fin 2) :
    MemLp (principalWeakDirections g i) 2 (volume.restrict (Metric.ball 0 R)) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact (memLp_const (complexPlaneCoordinates (EuclideanSpace.single i 1))).add
    ((Lp.memLp (principalDirectionalCorrection g
      (complexPlaneCoordinates (EuclideanSpace.single i 1)))).restrict _)

 def principalPhysicalWitness (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z)) :
    PlaneLocalWeakComplex (fun x => H (complexPlaneCoordinates x)) :=
  localWeakComplexOfDirectionalFields H (principalWeakDirections g)
    H.continuous.locallyIntegrable (principalWeakDirections_locallyIntegrable g)
    (fun i φ hφ => by
      have h := hw (complexPlaneCoordinates (EuclideanSpace.single i 1)) φ hφ
      simp only [principalWeakDirections, mul_comm] at h ⊢
      linear_combination h)
    (principalWeakDirections_memLp g)

lemma principalPhysicalWitness_equation (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z))
    (q : EuclideanPlane → ℝ)
    (hq : ∀ᵐ z ∂volume, g z=(q (complexPlaneCoordinates.symm z) : ℂ)*
      star (1+beurling g z)) :
    let D := principalPhysicalWitness H g hw
    ∀ᵐ x ∂volume,
      planarDbar (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1) =
      q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving
  filter_upwards [hmp.ae hq, hmp.ae (principalDirectionalCorrection_ae g 1),
    hmp.ae (principalDirectionalCorrection_ae g Complex.I)] with x hqx h0 h1
  change planarDbar (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).im =
      q x • star (planarDz (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).im)
  rw [planarDbar_of_complex_directions, planarDz_of_complex_directions]
  simp only [principalWeakDirections, complexPlaneCoordinates_zero,
    complexPlaneCoordinates_one, h0, h1, star_one, Complex.star_def, Complex.conj_I,
    one_mul, neg_mul] at hqx ⊢
  have hb : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))+
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  have hz : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))-
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = 1+beurling g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  simp only [sub_eq_add_neg] at hb hz ⊢
  rw [hb, hz]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Complex.real_smul] using hqx

end CircleDomainRigidity

end

end OAI
