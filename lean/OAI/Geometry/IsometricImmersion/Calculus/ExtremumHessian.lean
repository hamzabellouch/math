import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Algebra.QuadraticDiscriminant

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace ExtremumCalculus

theorem second_deriv_nonneg_of_localMin {f : ℝ → ℝ} {a : ℝ}
    (hm : IsLocalMin f a) (hc : ContinuousAt f a) :
    0 ≤ deriv (deriv f) a := by
  by_contra hn
  have hn' : deriv (deriv f) a < 0 := lt_of_not_ge hn
  have hM := isLocalMax_of_deriv_deriv_neg hn' hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hM] with x hx hy
    exact le_antisymm hy hx
  have hz : deriv (deriv f) a = 0 := by
    simpa using heq.deriv.deriv_eq
  exact (ne_of_lt hn') hz

theorem second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {a : ℝ}
    (hM : IsLocalMax f a) (hc : ContinuousAt f a) :
    deriv (deriv f) a ≤ 0 := by
  by_contra hn
  have hn' : 0 < deriv (deriv f) a := lt_of_not_ge hn
  have hm := isLocalMin_of_deriv_deriv_pos hn' hM.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hM] with x hx hy
    exact le_antisymm hy hx
  have hz : deriv (deriv f) a = 0 := by
    simpa using heq.deriv.deriv_eq
  exact (ne_of_gt hn') hz

end ExtremumCalculus

def ordinaryHessian (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordPartial i (coordPartial j z) p

variable {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem second_deriv_along_line (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (v : Coord) :
    deriv (deriv (fun t : ℝ => z (p + t • v))) 0 =
      fderiv ℝ (fderiv ℝ z) p v v := by
  have hL (t : ℝ) : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hLp : Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc := (hL 0).continuousAt
    change Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 (p + (0 : ℝ) • v)) at hc
    simpa only [zero_smul, add_zero] using hc
  have heq : deriv (fun t : ℝ => z (p + t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ z (p + t • v) v) := by
    filter_upwards [hLp.eventually (hU.mem_nhds hp)] with t ht
    have hd := (((hz (p + t • v) ht).contDiffAt
      (hU.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt
    simpa [Function.comp_def] using (hd.comp_hasDerivAt t (hL t)).deriv
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by simp)
  have hd : HasFDerivAt (fderiv ℝ z) (fderiv ℝ (fderiv ℝ z) p) p :=
    (((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ z (p + t • v))
      (fderiv ℝ (fderiv ℝ z) p v) 0 := by
    simpa [Function.comp_def] using
      (hd.comp_hasDerivAt_of_eq 0 (hL 0) (by simp))
  rw [heq.deriv_eq]
  simpa using (hcomp.clm_apply (hasDerivAt_const 0 v)).deriv

theorem secondFDeriv_nonneg_of_localMin (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hm : IsLocalMin z p) (v : Coord) :
    0 ≤ fderiv ℝ (fderiv ℝ z) p v v := by
  have hL : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
  have hm' : IsLocalMin (fun t : ℝ => z (p + t • v)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMin z (p + (0 : ℝ) • v) by simpa using hm).comp_continuous
        (g := fun t : ℝ => p + t • v) hL
  have hc : ContinuousAt (fun t : ℝ => z (p + t • v)) 0 := by
    exact (((hz p hp).contDiffAt (hU.mem_nhds hp)).continuousAt).comp_of_eq hL (by simp)
  rw [← second_deriv_along_line hz hU hp v]
  exact ExtremumCalculus.second_deriv_nonneg_of_localMin hm' hc

theorem secondFDeriv_nonpos_of_localMax (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hM : IsLocalMax z p) (v : Coord) :
    fderiv ℝ (fderiv ℝ z) p v v ≤ 0 := by
  have hL : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
  have hM' : IsLocalMax (fun t : ℝ => z (p + t • v)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMax z (p + (0 : ℝ) • v) by simpa using hM).comp_continuous
        (g := fun t : ℝ => p + t • v) hL
  have hc : ContinuousAt (fun t : ℝ => z (p + t • v)) 0 := by
    exact (((hz p hp).contDiffAt (hU.mem_nhds hp)).continuousAt).comp_of_eq hL (by simp)
  rw [← second_deriv_along_line hz hU hp v]
  exact ExtremumCalculus.second_deriv_nonpos_of_localMax hM' hc

theorem secondFDeriv_basis_quadratic (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (t : ℝ) :
    fderiv ℝ (fderiv ℝ z) p
        (t • Pi.single 0 1 + Pi.single 1 1)
        (t • Pi.single 0 1 + Pi.single 1 1) =
      ordinaryHessian z p 0 0 * (t * t) +
        (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 := by
  have hsym : fderiv ℝ (fderiv ℝ z) p (Pi.single 1 1) (Pi.single 0 1) =
      fderiv ℝ (fderiv ℝ z) p (Pi.single 0 1) (Pi.single 1 1) := by
    rw [← second_coordPartial_eq_fderiv hz hU hp,
      ← second_coordPartial_eq_fderiv hz hU hp]
    exact coordPartial_comm hz hU hp 1 0
  simp only [ordinaryHessian, second_coordPartial_eq_fderiv hz hU hp,
    map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, hsym]
  ring

theorem ordinaryHessian_det_nonneg_of_localMin (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (hm : IsLocalMin z p) :
    0 ≤ (ordinaryHessian z p).det := by
  have hq : ∀ t : ℝ, 0 ≤ ordinaryHessian z p 0 0 * (t * t) +
      (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 := by
    intro t
    rw [← secondFDeriv_basis_quadratic hz hU hp t]
    exact secondFDeriv_nonneg_of_localMin hz hU hp hm _
  have hd := discrim_le_zero hq
  have hsym : ordinaryHessian z p 1 0 = ordinaryHessian z p 0 1 :=
    coordPartial_comm hz hU hp 1 0
  rw [Matrix.det_fin_two, hsym]
  dsimp [discrim] at hd
  nlinarith

theorem ordinaryHessian_det_nonneg_of_localMax (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (hM : IsLocalMax z p) :
    0 ≤ (ordinaryHessian z p).det := by
  have hq : ∀ t : ℝ, ordinaryHessian z p 0 0 * (t * t) +
      (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 ≤ 0 := by
    intro t
    rw [← secondFDeriv_basis_quadratic hz hU hp t]
    exact secondFDeriv_nonpos_of_localMax hz hU hp hM _
  have hd := discrim_le_zero_of_nonpos hq
  have hsym : ordinaryHessian z p 1 0 = ordinaryHessian z p 0 1 :=
    coordPartial_comm hz hU hp 1 0
  rw [Matrix.det_fin_two, hsym]
  dsimp [discrim] at hd
  nlinarith

theorem ordinaryHessian_det_nonneg_of_localExtr (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (he : IsLocalExtr z p) :
    0 ≤ (ordinaryHessian z p).det :=
  he.elim (ordinaryHessian_det_nonneg_of_localMin hz hU hp)
    (ordinaryHessian_det_nonneg_of_localMax hz hU hp)

theorem covHessian_eq_ordinaryHessian_of_localExtr (g : MetricField)
    (he : IsLocalExtr z p) : covHessian g z p = ordinaryHessian z p := by
  have hd : fderiv ℝ z p = 0 := he.fderiv_eq_zero
  ext i j
  simp [covHessian, ordinaryHessian, coordPartial, hd]

theorem covHessian_at_localExtr {g : MetricField} (_hg : SmoothPositiveOn g U)
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (hp : p ∈ U)
    (he : IsLocalExtr z p) :
    fderiv ℝ z p = 0 ∧ covHessian g z p = ordinaryHessian z p ∧
      0 ≤ (covHessian g z p).det := by
  refine ⟨he.fderiv_eq_zero, covHessian_eq_ordinaryHessian_of_localExtr g he, ?_⟩
  rw [covHessian_eq_ordinaryHessian_of_localExtr g he]
  exact ordinaryHessian_det_nonneg_of_localExtr hz hU hp he

end SmoothLocal.Geometry

end

end OAI
