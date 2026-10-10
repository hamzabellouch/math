import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevHeightModulus
import OAI.Analysis.CircleDomains.Rigidity.ConductivityEnergyBounds
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! A common energy-error budget yields local equicontinuity of actual
homeomorphic height coordinates, with no common distortion constant. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_log_bound_from_error (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    {r R T B : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hT : ‖c‖+R < T)
    (hI : Integrable (fun p => D.imagGradient p 0^2+(D.imagGradient p 1-1)^2))
    (hB : (∫ p, D.imagGradient p 0^2+(D.imagGradient p 1-1)^2) ≤ B)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal) := by
  let A := complexPlaneCoordinates ⁻¹' {z : ℂ | r < dist z c ∧ dist z c < R}
  have hAB : A ⊆ ball (0 : EuclideanPlane) T := by
    intro p hp
    have htri : ‖complexPlaneCoordinates p‖ ≤ dist (complexPlaneCoordinates p) c+‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (complexPlaneCoordinates p-c) c
    rw [complexPlaneCoordinates_norm] at htri
    exact mem_ball.mpr (by rw [dist_zero_right]; linarith [hp.2])
  have hi : IntegrableOn (fun p => D.imagGradient p 0^2+D.imagGradient p 1^2) (ball 0 T) :=
    (D.imag_memLp T 0).integrable_sq.add (D.imag_memLp T 1).integrable_sq
  have hm := setIntegral_mono_set hi
    (Eventually.of_forall (fun p => add_nonneg (sq_nonneg (D.imagGradient p 0))
      (sq_nonneg (D.imagGradient p 1)))) (Eventually.of_forall (fun p hp => hAB hp))
  have he := D.imag_local_energy_le_error T hI
  have hb : (∫ p in A, D.imagGradient p 0^2+D.imagGradient p 1^2) ≤
      2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal := by
    exact hm.trans (he.trans (by linarith))
  exact (local_sobolev_height_log_bound φ c D hr hrR hx hy).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))

 theorem homeomorphic_heights_equicontinuous {ι : Type*}
    (φ : ι → ℂ ≃ₜ ℂ)
    (D : ∀ i, PlaneLocalWeakComplex (fun x => φ i (complexPlaneCoordinates x)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hI : ∀ i, Integrable (fun p => (D i).imagGradient p 0^2+((D i).imagGradient p 1-1)^2))
    (hB : ∀ i, (∫ p, (D i).imagGradient p 0^2+((D i).imagGradient p 1-1)^2) ≤ B) :
    Equicontinuous (fun i z => (φ i z).im) := by
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let T := ‖c‖+2
  let C := 16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let L := (C+1)/ε^2
  have hL : 0 < L := div_pos (by linarith) (sq_pos_of_pos hε)
  let δ := Real.exp (-L)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL.le))
  have hlog : Real.log (1/δ) = L := by
    dsimp only [δ]
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hEL : ε^2*L = C+1 := by
    dsimp only [L]
    field_simp
  refine ⟨δ, hδ, ?_⟩
  intro z hz i
  have hh := height_log_bound_from_error (φ i) c (D i) hδ hδ1
    (T := T) (by dsimp only [T]; linarith) (hI i) (hB i)
    (x := c) (y := z) (mem_closedBall_self hδ.le) (mem_closedBall.mpr hz.le)
  rw [hlog] at hh
  change |(φ i c).im-(φ i z).im|^2*L ≤ C at hh
  rw [Real.dist_eq]
  by_contra hn
  have hp := pow_le_pow_left₀ hε.le (le_of_not_gt hn) 2
  have hm := mul_le_mul_of_nonneg_right hp hL.le
  nlinarith

end CircleDomainRigidity

end

end OAI
