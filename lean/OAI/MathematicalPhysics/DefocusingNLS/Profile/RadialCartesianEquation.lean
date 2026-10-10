import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffTransport
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

namespace OAI

/-! The stationary radial equation gives the genuine Cartesian similarity equation. -/

open scoped ContDiff Laplacian
open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialCartesian_derivatives (f : ℝ → ℂ) (x : E) (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    Δ (fun y : E => f ‖y‖) x = deriv (deriv f) ‖x‖ +
        ((11 / ‖x‖ : ℝ) : ℂ) * deriv f ‖x‖ ∧
      fderiv ℝ (fun y : E => f ‖y‖) x ((1/2 : ℝ) • x) =
        ((‖x‖/2 : ℝ) : ℂ) * deriv f ‖x‖ := by
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let q : ℝ → ℂ := fun s => f (Real.sqrt s)
  have hq : ContDiffAt ℝ 2 q (r^2) := by
    have hs : ContDiffAt ℝ 2 Real.sqrt (r^2) :=
      contDiffAt_id.sqrt (ne_of_gt (sq_pos_of_pos hr))
    have hf' : ContDiffAt ℝ 2 f (Real.sqrt (r^2)) := by
      simpa only [Real.sqrt_sq hr.le] using hf
    exact hf'.comp (r^2) hs

  have hF : (fun y : E => q (‖y‖^2)) = fun y => f ‖y‖ := by
    funext y
    simp only [q,Real.sqrt_sq (norm_nonneg y)]
  have he : (fun s : ℝ => q (s^2)) =ᶠ[nhds r] f := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simp only [q,Real.sqrt_sq hs.le]
  have hd : deriv f r = ((2*r : ℝ) : ℂ) * deriv q (r^2) := by
    rw [← he.deriv_eq]
    have h := hq.differentiableAt (by norm_num) |>.hasDerivAt
    simpa [Function.comp_def,Complex.real_smul] using (h.scomp (h := fun s : ℝ => s^2) r ((hasDerivAt_id r).pow 2)).deriv
  have hdd : deriv (deriv f) r =
      ((4*r^2 : ℝ) : ℂ) * deriv (deriv q) (r^2) + 2 * deriv q (r^2) := by
    have h := iteratedDeriv_scomp_two (g := q) (f := fun s : ℝ => s^2) (x := r) hq (contDiffAt_id.pow 2)
    have hfirst : deriv (fun s : ℝ => s^2) = fun s => 2*s := by
      funext s
      simp
    have hsecond : deriv (deriv (fun s : ℝ => s^2)) r = 2 := by
      rw [hfirst]
      simpa only [mul_one,id_eq] using ((hasDerivAt_id r).const_mul 2).deriv
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def] at h
    rw [hsecond,hfirst] at h
    rw [← he.deriv.deriv_eq]
    rw [h]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hl := radialSquareLift_laplacian q x hq
  have ht := radialSquareLift_fderiv q x ((1/2 : ℝ) • x)
    (hq.differentiableAt (by norm_num))
  rw [hF] at hl ht
  have hir : inner ℝ x ((1/2 : ℝ) • x) = r^2/2 := by
    simp [inner_smul_right,r]
    ring
  rw [hir] at ht
  constructor
  · rw [hl,hd,hdd]
    change _ = _ + ((11/r : ℝ) : ℂ)*_
    push_cast
    field_simp [hrC]
    ring
  · rw [ht,hd]
    push_cast
    ring

theorem stationarySimilarityDefect_continuous (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) : Continuous (stationarySimilarityDefect a b m Q) := by
  have hd : Continuous (fderiv ℝ Q) :=
    (hQ.fderiv_right (m := 0) (by simp)).continuous
  have hdd : Continuous (iteratedFDeriv ℝ 2 Q) :=
    (hQ.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).continuous_iteratedFDeriv'
  have hl : Continuous (Δ Q) := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin 12) ℝ)]
    apply continuous_finsetSum
    intro j _
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℂ
      ![EuclideanSpace.basisFun (Fin 12) ℝ j, EuclideanSpace.basisFun (Fin 12) ℝ j]).continuous.comp hdd
  have ht : Continuous (fun y : E => fderiv ℝ Q y ((1/2 : ℝ) • y)) :=
    hd.clm_apply (continuous_id.const_smul (1/2 : ℝ))
  have haQ : Continuous (fun y : E => (a : ℂ)*Q y) := continuous_const.mul hQ.continuous
  have hbQ : Continuous (fun y : E => (b : ℂ)*Q y) := continuous_const.mul hQ.continuous
  have hI : Continuous (fun y : E => Complex.I*(fderiv ℝ Q y ((1/2 : ℝ) • y)+(a : ℂ)*Q y)) :=
    continuous_const.mul (ht.add haQ)
  have hN : Continuous (fun y : E => oddPowerNonlinearity m (Q y)) :=
    (contDiff_oddPowerNonlinearity m).continuous.comp hQ.continuous
  exact ((hl.add hI).add hbQ).sub hN

theorem radialMatchedCartesian_stationary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ∀ y : E, stationarySimilarityDefect (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedCartesian n z) y=0 := by
  let D := stationarySimilarityDefect (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
    (radialMatchedCartesian n z)
  have hc : Continuous D := stationarySimilarityDefect_continuous _ _ _ _
    (radialMatchedCartesian_contDiff n z hX hz)
  have he : ∀ y : E, y ≠ 0 → D y=0 := by
    intro y hy
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hf : ContDiffAt ℝ 2 (radialMatchedProfile n z) ‖y‖ :=
      ((radialMatchedProfile_contDiffOn n z hX hz) ‖y‖ hr).contDiffAt
        (Ioi_mem_nhds hr) |>.of_le (by simp)
    obtain ⟨hl,ht⟩ := radialCartesian_derivatives (radialMatchedProfile n z) y hy hf
    change Δ (radialMatchedCartesian n z) y = _ at hl
    change fderiv ℝ (radialMatchedCartesian n z) y ((1/2 : ℝ) • y) = _ at ht
    have h := radialMatchedProfile_stationary n z hX hz ‖y‖ hr
    dsimp only [D,stationarySimilarityDefect,radialMatchedCartesian]
    rw [hl,ht]
    exact sub_eq_zero.mpr h
  have hD : D = fun _ => 0 := Continuous.ext_on (dense_compl_singleton (0 : E))
    hc continuous_const (fun y hy => he y (by simpa using hy))
  intro y
  exact congrFun hD y

theorem exists_smooth_stationary_radialMatchedProfile :
    ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧
      ContDiff ℝ ∞ (radialMatchedCartesian n z) ∧
      (∀ y, stationarySimilarityDefect (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
        (radialMatchedCartesian n z) y=0) ∧
      (∀ y : E, radialMatchedCartesian n z y ≠ 0) ∧
      0 < (radialMatchedCartesian n z 0).re ∧ (radialMatchedCartesian n z 0).im=0 := by
  filter_upwards [exists_smooth_radialMatchedProfile] with n hn
  obtain ⟨z,hX,hz,hQ,hne,hre,him⟩ := hn
  exact ⟨z,hX,hz,hQ,radialMatchedCartesian_stationary n z hX hz,hne,hre,him⟩

end DefocusingNLS

end OAI
