import OAI.Geometry.Perimeter.Regularity.EllipticLocality
import OAI.Geometry.Perimeter.Regularity.SphericalFrankel

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack
namespace SphericalFrankel

abbrev End (n : ℕ) := Euc n →L[ℝ] Euc n

def linTrace {n : ℕ} (A : End n) : ℝ :=
  ∑ i : Fin n, inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)
    (A ((EuclideanSpace.basisFun (Fin n) ℝ) i))

def linkTrace {n : ℕ} (e : Frame n) (A : End n) : ℝ :=
  linTrace A - inner ℝ e.1 (A e.1) - inner ℝ e.2 (A e.2)

def projMap {n : ℕ} (e : Frame n) : End n :=
  ContinuousLinearMap.id ℝ (Euc n) - (innerSL ℝ e.1).smulRight e.1 -
    (innerSL ℝ e.2).smulRight e.2

lemma projMap_apply {n : ℕ} (e : Frame n) (v : Euc n) :
    projMap e v = proj e v := rfl

lemma linTrace_sub {n : ℕ} (A B : End n) :
    linTrace (A - B) = linTrace A - linTrace B := by
  simp only [linTrace, sub_apply, inner_sub_right,
    Finset.sum_sub_distrib]

lemma linTrace_add {n : ℕ} (A B : End n) :
    linTrace (A + B) = linTrace A + linTrace B := by
  simp only [linTrace, add_apply, inner_add_right,
    Finset.sum_add_distrib]

lemma linTrace_smul {n : ℕ} (t : ℝ) (A : End n) :
    linTrace (t • A) = t * linTrace A := by
  simp only [linTrace, smul_apply, real_inner_smul_right,
    Finset.mul_sum]

lemma linTrace_id {n : ℕ} : linTrace (ContinuousLinearMap.id ℝ (Euc n)) = n := by
  simp [linTrace]

lemma linTrace_rank {n : ℕ} (v w : Euc n) :
    linTrace ((innerSL ℝ v).smulRight w) = inner ℝ v w := by
  simpa only [linTrace, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    real_inner_smul_right] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner v w

lemma linkTrace_sub {n : ℕ} (e : Frame n) (A B : End n) :
    linkTrace e (A-B) = linkTrace e A - linkTrace e B := by
  simp only [linkTrace, linTrace_sub, sub_apply, inner_sub_right]
  ring

lemma linkTrace_add {n : ℕ} (e : Frame n) (A B : End n) :
    linkTrace e (A+B) = linkTrace e A + linkTrace e B := by
  simp only [linkTrace, linTrace_add, add_apply, inner_add_right]
  ring

lemma linkTrace_smul {n : ℕ} (e : Frame n) (t : ℝ) (A : End n) :
    linkTrace e (t • A) = t * linkTrace e A := by
  simp only [linkTrace, linTrace_smul, smul_apply,
    real_inner_smul_right]
  ring

lemma linkTrace_rank {n : ℕ} (e : Frame n) (v w : Euc n) :
    linkTrace e ((innerSL ℝ v).smulRight w) = inner ℝ (proj e v) w := by
  simp only [linkTrace, linTrace_rank, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, real_inner_smul_right, proj, inner_sub_left,
    real_inner_smul_left]
  rw [real_inner_comm v e.1, real_inner_comm v e.2]

lemma proj_self_left {n : ℕ} {e : Frame n} (he : IsFrame e) : proj e e.1 = 0 := by
  have h11 : inner ℝ e.1 e.1 = 1 := by simp [he.1]
  have h21 : inner ℝ e.2 e.1 = 0 := by rw [real_inner_comm, he.2.2]
  simp only [proj, h11, h21, one_smul, zero_smul, sub_self]

lemma proj_self_right {n : ℕ} {e : Frame n} (he : IsFrame e) : proj e e.2 = 0 := by
  have h22 : inner ℝ e.2 e.2 = 1 := by simp [he.2.1]
  simp only [proj, h22, he.2.2, one_smul, zero_smul, sub_zero, sub_self]

lemma inner_proj_swap {n : ℕ} (e : Frame n) (v w : Euc n) :
    inner ℝ (proj e v) w = inner ℝ v (proj e w) := by
  simp only [proj, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm v e.1, real_inner_comm v e.2]
  ring

lemma inner_proj_self {n : ℕ} {e : Frame n} (he : IsFrame e) (v : Euc n) :
    inner ℝ (proj e v) v = ‖proj e v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, proj_inner_self he]
  simp only [proj, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

lemma linkTrace_id {n : ℕ} {e : Frame n} (he : IsFrame e) :
    linkTrace e (ContinuousLinearMap.id ℝ (Euc n)) = (n : ℝ) - 2 := by
  simp [linkTrace, linTrace_id, he.1, he.2.1]
  ring

lemma linkTrace_proj {n : ℕ} {e f : Frame n} (he : IsFrame e) (hf : IsFrame f) :
    linkTrace e (projMap f) = traceProduct e f := by
  rw [projMap, linkTrace_sub, linkTrace_sub, linkTrace_id he,
    linkTrace_rank, linkTrace_rank]
  simp only [proj, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    hf.1, hf.2.1, traceProduct, angle]
  ring

def linkDiv {n : ℕ} (e : Frame n) (W : Euc n → Euc n) : ℝ :=
  linkTrace e (fderiv ℝ W e.1) - ((n : ℝ)-2) * inner ℝ e.1 (W e.1)

lemma linkDiv_scalar_constant {n : ℕ} {e f : Frame n}
    (he : IsFrame e) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    linkDiv e (fun z ↦ φ (inner ℝ z f.1) • f.1) =
      deriv φ (angle e f) * defect e f - ((n : ℝ)-2) * φ (angle e f) * angle e f := by
  have hi : HasFDerivAt (fun z : Euc n ↦ inner ℝ z f.1) (innerSL ℝ f.1) e.1 := by
    convert (innerSL ℝ f.1).hasFDerivAt (x := e.1) using 1
    funext z
    exact real_inner_comm f.1 z
  have hd := ((hφ _).hasDerivAt.comp_hasFDerivAt e.1 hi).smul_const f.1
  have hd' : fderiv ℝ (fun z ↦ φ (inner ℝ z f.1) • f.1) e.1 =
      deriv φ (angle e f) • (innerSL ℝ f.1).smulRight f.1 := by
    have hdf := hd.fderiv
    simp only [Function.comp_def] at hdf
    rw [hdf]
    ext v
    simp [angle, mul_assoc]
  rw [linkDiv, hd', linkTrace_smul, linkTrace_rank, inner_proj_self he]
  simp only [defect, real_inner_smul_right, angle]
  ring

lemma linkDiv_scalar_proj {n : ℕ} {e f : Frame n}
    (he : IsFrame e) (hf : IsFrame f)
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    linkDiv e (fun z ↦ φ (inner ℝ z f.1) • (projMap f z)) =
      deriv φ (angle e f) * cross e f + φ (angle e f) * traceProduct e f -
        ((n : ℝ)-2) * φ (angle e f) * defect f e := by
  have hi : HasFDerivAt (fun z : Euc n ↦ inner ℝ z f.1) (innerSL ℝ f.1) e.1 := by
    convert (innerSL ℝ f.1).hasFDerivAt (x := e.1) using 1
    funext z
    exact real_inner_comm f.1 z
  have hd := ((hφ _).hasDerivAt.comp_hasFDerivAt e.1 hi).smul (projMap f).hasFDerivAt
  have hd' : fderiv ℝ (fun z ↦ φ (inner ℝ z f.1) • (projMap f z)) e.1 =
      deriv φ (angle e f) • (innerSL ℝ f.1).smulRight (proj f e.1) +
        φ (angle e f) • projMap f := by
    have hdf := hd.fderiv
    change fderiv ℝ (fun z ↦ φ (inner ℝ z f.1) • (projMap f z)) e.1 = _ at hdf
    rw [hdf]
    ext v
    simp [angle, projMap_apply, add_comm, mul_assoc]
  rw [linkDiv, hd', linkTrace_add, linkTrace_smul, linkTrace_smul,
    linkTrace_rank, linkTrace_proj he hf]
  simp only [projMap_apply, real_inner_smul_right]
  have hip : inner ℝ e.1 (proj f e.1) = ‖proj f e.1‖ ^ 2 :=
    (real_inner_comm _ _).trans (inner_proj_self hf e.1)
  rw [hip]
  dsimp [angle, cross, defect]
  ring

lemma linTrace_rank_general {n : ℕ} (ℓ : Euc n →L[ℝ] ℝ) (w : Euc n) :
    linTrace (ℓ.smulRight w) = ℓ w := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hw : (∑ i : Fin n, inner ℝ (b i) w • b i) = w := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr w
  calc
    linTrace (ℓ.smulRight w) = ∑ i : Fin n, inner ℝ (b i) w * ℓ (b i) := by
      simp only [linTrace, ContinuousLinearMap.smulRight_apply, real_inner_smul_right, b]
      congr 1; ext i; ring
    _ = ℓ (∑ i : Fin n, inner ℝ (b i) w • b i) := by simp
    _ = ℓ w := by rw [hw]

def sphereProj {n : ℕ} (z : Euc n) : End n :=
  ContinuousLinearMap.id ℝ (Euc n) - (innerSL ℝ z).smulRight z

def planeTrace {n : ℕ} (ν : Euc n) (A : End n) : ℝ :=
  linTrace A - inner ℝ ν (A ν)

lemma planeTrace_add {n : ℕ} (ν : Euc n) (A B : End n) :
    planeTrace ν (A+B) = planeTrace ν A + planeTrace ν B := by
  simp only [planeTrace, linTrace_add, add_apply, inner_add_right]
  ring

lemma planeTrace_sub {n : ℕ} (ν : Euc n) (A B : End n) :
    planeTrace ν (A-B) = planeTrace ν A - planeTrace ν B := by
  simp only [planeTrace, linTrace_sub, sub_apply, inner_sub_right]
  ring

lemma planeTrace_smul {n : ℕ} (ν : Euc n) (a : ℝ) (A : End n) :
    planeTrace ν (a • A) = a * planeTrace ν A := by
  simp only [planeTrace, linTrace_smul, smul_apply, real_inner_smul_right]
  ring

lemma planeTrace_rank {n : ℕ} (ν : Euc n) (ℓ : Euc n →L[ℝ] ℝ) (w : Euc n) :
    planeTrace ν (ℓ.smulRight w) = ℓ w - ℓ ν * inner ℝ ν w := by
  simp only [planeTrace, linTrace_rank_general, ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right]

lemma planeTrace_comp_sphereProj {n : ℕ} {e : Frame n} (he : IsFrame e) (A : End n) :
    planeTrace e.2 (A.comp (sphereProj e.1)) = linkTrace e A := by
  have hid : A.comp (sphereProj e.1) = A - (innerSL ℝ e.1).smulRight (A e.1) := by
    ext v
    simp [sphereProj]
  rw [hid, planeTrace_sub, planeTrace_rank]
  simp only [innerSL_apply_apply, he.2.2, zero_mul, sub_zero, planeTrace, linkTrace]
  ring

lemma sphereProj_self {n : ℕ} {z : Euc n} (hz : ‖z‖ = 1) : sphereProj z z = 0 := by
  simp [sphereProj, hz]

lemma planeTrace_sphereProj {n : ℕ} {e : Frame n} (he : IsFrame e) :
    planeTrace e.2 (sphereProj e.1) = (n : ℝ)-2 := by
  have hh := planeTrace_comp_sphereProj he (ContinuousLinearMap.id ℝ (Euc n))
  simpa [linkTrace_id he] using hh

def radialUnit {n : ℕ} (x : Euc n) : Euc n := ‖x‖⁻¹ • x

lemma radialUnit_norm {n : ℕ} {x : Euc n} (hx : x ≠ 0) : ‖radialUnit x‖ = 1 := by
  simp [radialUnit, norm_smul, norm_ne_zero_iff.mpr hx]

lemma radialUnit_scale {n : ℕ} {x : Euc n} (hx : x ≠ 0) : ‖x‖ • radialUnit x = x := by
  simp [radialUnit, smul_smul, norm_ne_zero_iff.mpr hx]

lemma radialUnit_contDiffAt {n : ℕ} {x : Euc n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialUnit x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma radialUnit_measurable {n : ℕ} : Measurable (radialUnit (n := n)) :=
  (measurable_norm.inv).smul measurable_id

lemma radialUnit_hasFDerivAt {n : ℕ} {x : Euc n} (hx : x ≠ 0) :
    HasFDerivAt radialUnit (‖x‖⁻¹ • sphereProj (radialUnit x)) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : HasFDerivAt (fun y : Euc n ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    have hh := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).sqrt (pow_ne_zero 2 hr)
    simp only [Real.sqrt_sq (norm_nonneg _)] at hh
    apply hh.congr_fderiv
    ext v
    simp
    ring
  have hinv := (hasDerivAt_inv hr).comp_hasFDerivAt x hnorm
  have h := hinv.smul (hasFDerivAt_id x)
  change HasFDerivAt radialUnit _ x at h
  apply h.congr_fderiv
  ext v : 1
  simp only [sphereProj, radialUnit, add_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, Function.comp_apply, real_inner_smul_left,
    smul_eq_mul, smul_smul, id_eq]
  module

def sphereLift {n : ℕ} (W : Euc n → Euc n) (x : Euc n) : Euc n :=
  W (radialUnit x) - (inner ℝ (radialUnit x) (W (radialUnit x))) • radialUnit x

lemma inner_radialUnit_sphereLift {n : ℕ} (W : Euc n → Euc n)
    {x : Euc n} (hx : x ≠ 0) : inner ℝ (radialUnit x) (sphereLift W x) = 0 := by
  simp [sphereLift, inner_sub_right, real_inner_smul_right, radialUnit_norm hx]

lemma sphereLift_contDiffAt {n : ℕ} {W : Euc n → Euc n}
    (hW : ContDiff ℝ ∞ W) {x : Euc n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (sphereLift W) x := by
  have hq := radialUnit_contDiffAt hx
  have hWq := hW.contDiffAt.comp x hq
  exact hWq.sub ((hq.inner ℝ hWq).smul hq)

lemma planeTrace_sphereLift {n : ℕ} {W : Euc n → Euc n}
    (hW : Differentiable ℝ W) {x ν : Euc n} (hx : x ≠ 0)
    (he : IsFrame (radialUnit x, ν)) :
    planeTrace ν (fderiv ℝ (sphereLift W) x) =
      ‖x‖⁻¹ * linkDiv (radialUnit x, ν) W := by
  let z := radialUnit x
  let A := fderiv ℝ W z
  let B := ‖x‖⁻¹ • sphereProj z
  let D := A.comp B
  let ℓ := (fderivInnerCLM ℝ (z, W z)).comp (B.prod D)
  have hq : HasFDerivAt radialUnit B x := radialUnit_hasFDerivAt hx
  have hWq : HasFDerivAt (W ∘ radialUnit) D x := (hW z).hasFDerivAt.comp x hq
  have hd := hWq.sub ((hq.inner ℝ hWq).smul hq)
  have hdf : fderiv ℝ (sphereLift W) x = D - (inner ℝ z (W z) • B + ℓ.smulRight z) := by
    exact hd.fderiv
  have hz : ‖z‖ = 1 := he.1
  have hBz : B z = 0 := by
    change ‖x‖⁻¹ • sphereProj z z = 0
    rw [sphereProj_self hz, smul_zero]
  have hlz : ℓ z = 0 := by simp [ℓ, D, hBz]
  have hnz : inner ℝ ν z = 0 := by exact (real_inner_comm _ _).trans he.2.2
  have hD : planeTrace ν D = ‖x‖⁻¹ * linkTrace (z,ν) A := by
    have hid : D = ‖x‖⁻¹ • (A.comp (sphereProj z)) := by ext v; simp [D, B]
    rw [hid, planeTrace_smul, planeTrace_comp_sphereProj he]
  have hB : planeTrace ν B = ‖x‖⁻¹ * ((n : ℝ)-2) := by
    change planeTrace ν (‖x‖⁻¹ • sphereProj z) = _
    rw [planeTrace_smul, planeTrace_sphereProj he]
  rw [hdf, planeTrace_sub, planeTrace_add, planeTrace_smul, planeTrace_rank,
    hlz, hnz, mul_zero, sub_zero, hD, hB]
  dsimp [linkDiv, z, A]
  ring

def annularProfile (s : ℝ) : ℝ := expNegInvGlue (s - 1) * expNegInvGlue (4 - s)

def annularCut {n : ℕ} (x : Euc n) : ℝ := annularProfile (‖x‖ ^ 2)

lemma annularProfile_contDiff : ContDiff ℝ ∞ annularProfile :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma annularCut_contDiff {n : ℕ} : ContDiff ℝ ∞ (annularCut (n := n)) :=
  annularProfile_contDiff.comp (contDiff_id.norm_sq ℝ)

lemma annularCut_nonneg {n : ℕ} (x : Euc n) : 0 ≤ annularCut x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma annularCut_eq_zero_inner {n : ℕ} {x : Euc n} (hx : ‖x‖ ≤ 1) :
    annularCut x = 0 := by
  have hh : ‖x‖ ^ 2 - 1 ≤ 0 := by nlinarith [norm_nonneg x]
  simp [annularCut, annularProfile, expNegInvGlue.zero_of_nonpos hh]

lemma annularCut_eq_zero_outer {n : ℕ} {x : Euc n} (hx : 2 ≤ ‖x‖) :
    annularCut x = 0 := by
  have hh : 4 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
  simp [annularCut, annularProfile, expNegInvGlue.zero_of_nonpos hh]

lemma annularCut_pos {n : ℕ} {x : Euc n} (hxi : 1 < ‖x‖) (hxo : ‖x‖ < 2) :
    0 < annularCut x := by
  apply mul_pos
  · exact expNegInvGlue.pos_of_pos (by nlinarith)
  · exact expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg x])

lemma annularCut_hasFDerivAt {n : ℕ} (x : Euc n) :
    HasFDerivAt annularCut
      ((2 * deriv annularProfile (‖x‖ ^ 2)) • innerSL ℝ x) x := by
  have hh := ((annularProfile_contDiff.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x
    ((hasFDerivAt_id x).norm_sq)
  apply hh.congr_fderiv
  ext v
  simp
  ring

def annularLift {n : ℕ} (W : Euc n → Euc n) (x : Euc n) : Euc n :=
  annularCut x • sphereLift W x

lemma annularLift_contDiff {n : ℕ} {W : Euc n → Euc n} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (annularLift W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : Euc n))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euc n) (by norm_num : (0 : ℝ)<1)] with y hy
    have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
    simp [annularLift, annularCut_eq_zero_inner hy']
  · exact annularCut_contDiff.contDiffAt.smul (sphereLift_contDiffAt hW hx)

lemma annularLift_tsupport {n : ℕ} (W : Euc n → Euc n) :
    tsupport (annularLift W) ⊆ Metric.closedBall (0 : Euc n) 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (by simp [annularLift, annularCut_eq_zero_outer (le_of_not_ge hn)])

lemma planeTrace_annularLift {n : ℕ} {W : Euc n → Euc n}
    (hW : ContDiff ℝ ∞ W) {x ν : Euc n} (hx : x ≠ 0)
    (he : IsFrame (radialUnit x,ν)) :
    planeTrace ν (fderiv ℝ (annularLift W) x) =
      (annularCut x * ‖x‖⁻¹) * linkDiv (radialUnit x,ν) W := by
  have hS := (sphereLift_contDiffAt hW hx).differentiableAt (by simp)
  have hd := (annularCut_hasFDerivAt x).smul hS.hasFDerivAt
  have hdf : fderiv ℝ (annularLift W) x = annularCut x • fderiv ℝ (sphereLift W) x +
      ((2 * deriv annularProfile (‖x‖^2)) • innerSL ℝ x).smulRight (sphereLift W x) := hd.fderiv
  have hxn : inner ℝ x ν = 0 := by
    rw [← radialUnit_scale hx, real_inner_smul_left, he.2.2, mul_zero]
  have hxS : inner ℝ x (sphereLift W x) = 0 := by
    calc
      inner ℝ x (sphereLift W x) = ‖x‖ * inner ℝ (radialUnit x) (sphereLift W x) := by
        rw [← real_inner_smul_left, radialUnit_scale hx]
      _ = 0 := by rw [inner_radialUnit_sphereLift W hx, mul_zero]
  rw [hdf, planeTrace_add, planeTrace_smul, planeTrace_rank,
    planeTrace_sphereLift (hW.differentiable (by simp)) hx he]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, hxn, hxS, mul_zero]
  ring

lemma annularLift_zero_nhds {n : ℕ} (W : Euc n → Euc n) :
    annularLift W =ᶠ[𝓝 (0 : Euc n)] (fun _ ↦ 0) := by
  filter_upwards [Metric.ball_mem_nhds (0 : Euc n) (by norm_num : (0 : ℝ)<1)] with y hy
  have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
  simp [annularLift, annularCut_eq_zero_inner hy']

def annularWeight {n : ℕ} (x : Euc n) : ℝ := annularCut x * ‖x‖⁻¹

lemma annularWeight_nonneg {n : ℕ} (x : Euc n) : 0 ≤ annularWeight x :=
  mul_nonneg (annularCut_nonneg x) (inv_nonneg.mpr (norm_nonneg x))

lemma annularWeight_continuous {n : ℕ} : Continuous (annularWeight (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euc n) (by norm_num : (0 : ℝ)<1)] with y hy
    have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
    simp [annularWeight, annularCut_eq_zero_inner hy']
  · exact annularCut_contDiff.continuous.continuousAt.mul
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx))

lemma annularWeight_tsupport {n : ℕ} :
    tsupport (annularWeight (n := n)) ⊆ Metric.closedBall (0 : Euc n) 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (by simp [annularWeight, annularCut_eq_zero_outer (le_of_not_ge hn)])

def annularWeightNN {n : ℕ} (x : Euc n) : ℝ≥0 := ⟨annularWeight x, annularWeight_nonneg x⟩

lemma annularWeightNN_measurable {n : ℕ} : Measurable (annularWeightNN (n := n)) :=
  annularWeight_continuous.measurable.nnreal_mk

def annularFrameMeasure {n : ℕ} (E : Set (Euc n)) : Measure (Euc n) :=
  ((perimeterMeasure E).restrict (Metric.ball 0 3)).withDensity
    (fun x ↦ (annularWeightNN x : ℝ≥0∞))

def frameOf {n : ℕ} (E : Set (Euc n)) (x : Euc n) : Frame n :=
  (radialUnit x, approximateNormal E x)

lemma frameOf_measurable {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E) :
    Measurable (frameOf E) := radialUnit_measurable.prodMk (measurable_approximateNormal hE)

def annularLink {n : ℕ} (E : Set (Euc n)) : Measure (Frame n) :=
  Measure.map (frameOf E) (annularFrameMeasure E)

lemma annularFrameMeasure_finite {n : ℕ} {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) : IsFiniteMeasure (annularFrameMeasure E) := by
  let := perimeterMeasure_locallyFinite E hE.2.1
  have hc : HasCompactSupport (annularWeight (n := n)) :=
    (isCompact_closedBall (0 : Euc n) 2).of_isClosed_subset isClosed_closure annularWeight_tsupport
  have hi : Integrable (annularWeight (n := n))
      ((perimeterMeasure E).restrict (Metric.ball 0 3)) :=
    annularWeight_continuous.integrable_of_hasCompactSupport hc
  apply isFiniteMeasure_withDensity
  have hh := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (annularWeight_nonneg (n := n)))).mp hi.2
  convert hh.ne using 1
  congr 1
  funext x
  exact (ENNReal.ofReal_coe_nnreal (p := annularWeightNN x)).symm

lemma annularLink_finite {n : ℕ} {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) : IsFiniteMeasure (annularLink E) := by
  let := annularFrameMeasure_finite hE
  exact Measure.isFiniteMeasure_map (annularFrameMeasure E) (frameOf E)

lemma annularLink_frames {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E) :
    ∀ᵐ e ∂annularLink E, IsFrame e := by
  rw [annularLink, ae_map_iff (frameOf_measurable hE.1).aemeasurable
    (isClosed_frames n).measurableSet, annularFrameMeasure,
    ae_withDensity_iff annularWeightNN_measurable.coe_nnreal_ennreal]
  filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hE),
    ae_restrict_of_ae (minimizing_cone_radial_tangent_ae hn hE hc)] with x hx ht hρ
  have hx0 : x ≠ 0 := by
    intro hh
    apply hρ
    apply ENNReal.coe_eq_zero.mpr
    apply Subtype.ext
    simp [hh, annularWeightNN, annularWeight]
  refine ⟨radialUnit_norm hx0, hx.1, ?_⟩
  change inner ℝ (radialUnit x) (approximateNormal E x) = 0
  rw [radialUnit, real_inner_smul_left, ht, mul_zero]

lemma linkDiv_continuous {n : ℕ} {W : Euc n → Euc n} (hW : ContDiff ℝ ∞ W) :
    Continuous (fun e : Frame n ↦ linkDiv e W) := by
  have hA := hW.continuous_fderiv (by simp)
  unfold linkDiv linkTrace linTrace
  fun_prop

structure LinkStationary {n : ℕ} (μ : Measure (Frame n)) : Prop where
  firstVariation : ∀ W : Euc n → Euc n, ContDiff ℝ ∞ W → (∫ e, linkDiv e W ∂μ) = 0

lemma annularLink_stationary {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E) :
    LinkStationary (annularLink E) := by
  constructor
  intro W hW
  have hV := annularLift_contDiff hW
  have hs : tsupport (annularLift W) ⊆ Metric.ball (0 : Euc n) 3 :=
    (annularLift_tsupport W).trans (Metric.closedBall_subset_ball (by norm_num))
  have hk : HasCompactSupport (annularLift W) :=
    (isCompact_closedBall (0 : Euc n) 2).of_isClosed_subset isClosed_closure (annularLift_tsupport W)
  have hstat := minimizing_tangentialDivergence_integral_eq_zero hn hE 0 (by norm_num : (0 : ℝ)<3)
    hV hk hs
  rw [annularLink, integral_map (frameOf_measurable hE.1).aemeasurable
    (linkDiv_continuous hW).measurable.aestronglyMeasurable,
    annularFrameMeasure, integral_withDensity_eq_integral_smul annularWeightNN_measurable]
  change (∫ x in Metric.ball 0 3, annularWeight x * linkDiv (frameOf E x) W ∂perimeterMeasure E) = 0
  apply (integral_congr_ae ?_).trans hstat
  filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hE),
    ae_restrict_of_ae (minimizing_cone_radial_tangent_ae hn hE hc)] with x hx ht
  by_cases hx0 : x = 0
  · subst x
    have hd : fderiv ℝ (annularLift W) 0 = 0 :=
      ((hasFDerivAt_const (0 : Euc n) (0 : Euc n)).congr_of_eventuallyEq (annularLift_zero_nhds W)).fderiv
    simp [annularWeight, tangentialDivergence, divergence, hd]
  · have hf : IsFrame (radialUnit x, approximateNormal E x) :=
      ⟨radialUnit_norm hx0, hx.1, by simp [radialUnit, real_inner_smul_left, ht]⟩
    exact (planeTrace_annularLift hW hx0 hf).symm

end SphericalFrankel
end RPISingularHarnack

end

end OAI
