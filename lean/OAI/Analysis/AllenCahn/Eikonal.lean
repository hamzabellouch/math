import OAI.Analysis.AllenCahn.JetProducts

namespace OAI

noncomputable section
namespace EikonalSupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def potential (t : ℝ) : ℝ := (1 - t ^ 2) ^ 2 / 4

def profile (s : ℝ) : ℝ := Real.tanh (s / Real.sqrt 2)

def surfaceTension : ℝ := 2 * Real.sqrt 2 / 3

def AllenCahn {n : ℕ} (v : Space n → ℝ) : Prop :=
  ∀ x, Laplacian.laplacian v x = v x ^ 3 - v x

def SecondVariation {n : ℕ} (v φ : Space n → ℝ) : ℝ :=
  ∫ x, (‖gradient φ x‖ ^ 2 + (3 * v x ^ 2 - 1) * φ x ^ 2)

def Stable {n : ℕ} (v : Space n → ℝ) : Prop :=
  ∀ φ : Space n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    0 ≤ SecondVariation v φ

def Energy {n : ℕ} (v : Space n → ℝ) (Ω : Set (Space n)) : ℝ :=
  ∫ x in Ω, (‖gradient v x‖ ^ 2 / 2 + potential (v x))

def unitBallVolume (m : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : Space m) 1)

def density {n : ℕ} (v : Space n → ℝ) (R : ℝ) (y : Space n) : ℝ :=
  Energy v (Metric.ball y R) / (surfaceTension * unitBallVolume (n - 1) * R ^ (n - 1))

def densityAtInfinity {n : ℕ} (v : Space n → ℝ) : ℝ≥0∞ :=
  ⨆ R : { R : ℝ // 0 < R }, ENNReal.ofReal (density v R.val 0)

def Classified {n : ℕ} (v : Space n → ℝ) : Prop :=
  (∀ x, v x = 1) ∨ (∀ x, v x = -1) ∨
    ∃ (a : Space n) (b : ℝ), ‖a‖ = 1 ∧ ∀ x, v x = profile (inner ℝ a x - b)

def StableRigiditySeven : Prop :=
  ∀ v : Space 7 → ℝ, ContDiff ℝ 2 v →
    (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v → Stable v → Classified v

def MonotoneRigidityEight : Prop :=
  ∀ u : Space 8 → ℝ, ContDiff ℝ 2 u →
    (∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1) → AllenCahn u →
    (∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single (7 : Fin 8) 1)) →
    ∃ (e : Space 8) (c : ℝ), ‖e‖ = 1 ∧ 0 < e 7 ∧
      ∀ x, u x = profile (inner ℝ e x - c)

def FiniteDensityRigidity : Prop :=
  ∀ (n : ℕ), 4 ≤ n → n ≤ 7 →
    ∀ v : Space n → ℝ, ContDiff ℝ 2 v →
      (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v → Stable v →
      densityAtInfinity v < ⊤ → Classified v

end EikonalSupport.DeGiorgi
end

noncomputable section
namespace EikonalSupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal
variable {n : ℕ} {U : Space n → ℝ}

lemma gradient_contDiff (hU : ContDiff ℝ 2 U) : ContDiff ℝ 1 (gradient U) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearEquiv.contDiff.comp
    (hU.fderiv_right (m := 1) (by norm_num))

lemma inner_fderiv_gradient (hU : ContDiff ℝ 2 U) (x a b : Space n) :
    inner ℝ (fderiv ℝ (gradient U) x a) b =
      fderiv ℝ (fderiv ℝ U) x a b := by
  have hdg := (gradient_contDiff hU).differentiable (by norm_num)
  have hdf := (hU.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := fderiv_inner_apply ℝ (hdg x) (differentiableAt_const (c := b)) a
  simp only [inner_gradient_left] at h
  rw [fderiv_clm_apply (hdf x) (differentiableAt_const (c := b))] at h
  simpa using h.symm

lemma fderiv_gradient_symmetric (hU : ContDiff ℝ 2 U) (x a b : Space n) :
    inner ℝ (fderiv ℝ (gradient U) x a) b =
      inner ℝ (fderiv ℝ (gradient U) x b) a := by
  rw [inner_fderiv_gradient hU, inner_fderiv_gradient hU]
  exact hU.contDiffAt.isSymmSndFDerivAt (by simp) a b

lemma eikonal_acceleration_zero (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) (x : Space n) :
    fderiv ℝ (gradient U) x (gradient U x) = 0 := by
  have hc : (fun y => inner ℝ (gradient U y) (gradient U y)) = fun _ => (1 : ℝ) := by
    funext y
    simp [hunit]
  have hdg := (gradient_contDiff hU).differentiable (by norm_num)
  have hd (b : Space n) := fderiv_inner_apply ℝ (hdg x) (hdg x) b
  simp only [hc] at hd
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [fderiv_gradient_symmetric hU]
  have hb := hd (fderiv ℝ (gradient U) x (gradient U x))
  simp only [fderiv_const_apply, zero_apply] at hb
  have hcmt := real_inner_comm (gradient U x)
    (fderiv ℝ (gradient U) x (fderiv ℝ (gradient U) x (gradient U x)))
  linarith

lemma eikonal_gradient_on_line (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) (x : Space n) (t : ℝ) :
    gradient U (x + t • gradient U x) = gradient U x := by
  let p := gradient U
  let y : ℝ → Space n := fun s => x + s • (t • p x)
  let g : ℝ → Space n := fun s => p (y s) - p x
  let g' : ℝ → Space n := fun s => fderiv ℝ p (y s) (t • p x)
  have hp : ContDiff ℝ 1 p := gradient_contDiff hU
  have hy (s : ℝ) : HasDerivAt y (t • p x) s := by
    simpa [y] using (hasDerivAt_const s x).fun_add
      ((hasDerivAt_id s).smul_const (t • p x))
  have hgc : Continuous g := (hp.continuous.comp (by fun_prop)).sub continuous_const
  have hgd (s : ℝ) : HasDerivAt g (g' s) s := by
    simpa [g, g', Function.comp_def] using
      (((hp.differentiable (by norm_num) (y s)).hasFDerivAt.comp_hasDerivAt s
        (hy s)).sub_const (p x))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (((hp.continuous_fderiv (by norm_num)).comp (by fun_prop : Continuous y)).continuousOn)
  have hz (s : ℝ) : fderiv ℝ p (y s) (p (y s)) = 0 :=
    eikonal_acceleration_zero hU hunit _
  have hrep (s : ℝ) : g' s = -(t • (fderiv ℝ p (y s) (g s))) := by
    simp [g', g, map_sub, hz]
  have hb (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      ‖g' s‖ ≤ (‖t‖ * C) * ‖g s‖ := by
    rw [hrep, norm_neg, norm_smul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg t)
    exact (fderiv ℝ p (y s)).le_opNorm (g s) |>.trans
      (mul_le_mul_of_nonneg_right (hC s ⟨hs.1, hs.2.le⟩) (norm_nonneg _))
  have hg0 : g 0 = 0 := by simp [g, y]
  have hh := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hgc.continuousOn
    (fun s _ => (hgd s).hasDerivWithinAt) hg0 hb 1 (by simp)
  simpa [g, y, sub_eq_zero] using hh

lemma eikonal_value_on_line (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) (x : Space n) (t : ℝ) :
    U (x + t • gradient U x) = U x + t := by
  have hd (s : ℝ) : HasDerivAt (fun r => U (x + r • gradient U x)) 1 s := by
    have hy : HasDerivAt (fun r : ℝ => x + r • gradient U x) (gradient U x) s := by
      simpa using (hasDerivAt_const s x).fun_add
        ((hasDerivAt_id s).smul_const (gradient U x))
    have H := ((hU.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hy)
    rw [← inner_gradient_left, eikonal_gradient_on_line hU hunit,
      real_inner_self_eq_norm_sq, hunit, one_pow] at H
    exact H
  have hd0 (s : ℝ) : HasDerivAt (fun r => U (x + r • gradient U x) - r) 0 s := by
    simpa using (hd s).fun_sub (hasDerivAt_id s)
  have H := is_const_of_deriv_eq_zero (fun s => (hd0 s).differentiableAt)
    (fun s => (hd0 s).deriv) t 0
  simp only [zero_smul, add_zero, sub_zero] at H
  linarith

lemma eikonal_lipschitz (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) : LipschitzWith 1 U := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hU.differentiable (by norm_num))
  intro x
  have hn : ‖fderiv ℝ U x‖ = 1 := by
    rw [← (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map]
    exact hunit x
  exact_mod_cast hn.le

lemma eikonal_gradient_constant (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) (x y : Space n) :
    gradient U x = gradient U y := by
  let a := gradient U x
  let b := gradient U y
  have ha : ‖a‖ = 1 := hunit x
  have hb : ‖b‖ = 1 := hunit y
  have hbound (t : ℝ) (ht : 0 ≤ t) :
      2 * t + (U x - U y) ≤ ‖x - y‖ + t * ‖a + b‖ := by
    have H := (eikonal_lipschitz hU hunit).norm_sub_le
      (x + t • a) (y + (-t) • b)
    simp only [NNReal.coe_one, one_mul] at H
    rw [show U (x + t • a) = U x + t from eikonal_value_on_line hU hunit x t,
      show U (y + (-t) • b) = U y + -t from eikonal_value_on_line hU hunit y (-t)] at H
    have hn : ‖(x + t • a) - (y + (-t) • b)‖ ≤ ‖x - y‖ + t * ‖a + b‖ := by
      rw [show (x + t • a) - (y + (-t) • b) = (x - y) + t • (a + b) by module]
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht])
    have H' := le_abs_self ((U x + t) - (U y + -t))
    rw [Real.norm_eq_abs] at H
    linarith
  have hn : 2 ≤ ‖a + b‖ := by
    by_contra h
    have hg : 0 < 2 - ‖a + b‖ := by linarith
    let t := (|‖x - y‖ - (U x - U y)| + 1) / (2 - ‖a + b‖)
    have ht : 0 ≤ t := div_nonneg (by positivity) hg.le
    have hc : t * (2 - ‖a + b‖) = |‖x - y‖ - (U x - U y)| + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hg)
    have H := hbound t ht
    have H' := le_abs_self (‖x - y‖ - (U x - U y))
    nlinarith
  have ha2 := norm_add_sq_real a b
  have hb2 := norm_sub_sq_real a b
  rw [ha, hb] at ha2 hb2
  have hn2 : 4 ≤ ‖a + b‖ ^ 2 := by nlinarith [norm_nonneg (a + b)]
  have hzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b), sq_nonneg ‖a - b‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

lemma eikonal_affine (hU : ContDiff ℝ 2 U)
    (hunit : ∀ x, ‖gradient U x‖ = 1) :
    ∃ a : Space n, ‖a‖ = 1 ∧ ∀ x, U x = inner ℝ a x + U 0 := by
  let a := gradient U 0
  have hi : Differentiable ℝ (fun x : Space n => inner ℝ a x) :=
    (innerSL ℝ a).differentiable
  have hu : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hz (x : Space n) : fderiv ℝ (fun y => U y - inner ℝ a y) x = 0 := by
    rw [fderiv_fun_sub (hu x) (hi x)]
    apply sub_eq_zero.mpr
    have H : fderiv ℝ (fun y : Space n => inner ℝ a y) x = innerSL ℝ a :=
      (innerSL ℝ a).hasFDerivAt.fderiv
    rw [H]
    ext b
    rw [← inner_gradient_left, eikonal_gradient_constant hU hunit x 0]
    rfl
  refine ⟨a, hunit 0, fun x => ?_⟩
  have H := is_const_of_fderiv_eq_zero (hu.sub hi) hz x 0
  change U x - inner ℝ a x = U 0 - inner ℝ a 0 at H
  simp only [inner_zero_right, sub_zero] at H
  linarith

end EikonalSupport.DeGiorgi
end

noncomputable section
namespace EikonalSupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

def inverseProfile {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  Real.sqrt 2 * Real.artanh (v x)

def diffuseDefect {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  1 - ‖gradient (inverseProfile v) x‖ ^ 2

lemma inverseProfile_contDiff {n : ℕ} {v : Space n → ℝ} (hv : ContDiff ℝ 2 v)
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) : ContDiff ℝ 2 (inverseProfile v) := by
  have hm (x : Space n) : 1 - v x ≠ 0 := ne_of_gt (sub_pos.mpr (hi x).2)
  have hp (x : Space n) : 1 + v x ≠ 0 := ne_of_gt (by linarith [(hi x).1])
  have hq : ContDiff ℝ 2 (fun x => (1 + v x) / (1 - v x)) :=
    (contDiff_const.add hv).div (contDiff_const.sub hv) hm
  have hl : ContDiff ℝ 2 (fun x => (Real.sqrt 2 / 2) * Real.log ((1 + v x) / (1 - v x))) :=
    contDiff_const.mul (hq.log (fun x => div_ne_zero (hp x) (hm x)))
  convert hl using 1
  funext x
  dsimp [inverseProfile]
  rw [Real.artanh_eq_half_log ⟨(hi x).1.le, (hi x).2.le⟩]
  ring

lemma profile_inverseProfile {n : ℕ} {v : Space n → ℝ}
    (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (x : Space n) :
    profile (inverseProfile v x) = v x := by
  have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp only [profile, inverseProfile, mul_div_cancel_left₀ _ h2]
  exact Real.tanh_artanh (hi x)

theorem classified_of_zero_defect {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hD : ∀ x, diffuseDefect v x = 0) : Classified v := by
  have hunit (x : Space n) : ‖gradient (inverseProfile v) x‖ = 1 := by
    have H := hD x
    dsimp [diffuseDefect] at H
    nlinarith [norm_nonneg (gradient (inverseProfile v) x)]
  obtain ⟨a, ha, hU⟩ := eikonal_affine (inverseProfile_contDiff hv hi) hunit
  refine Or.inr (Or.inr ⟨a, -(inverseProfile v 0), ha, fun x => ?_⟩)
  rw [← profile_inverseProfile hi x, hU x]
  simp

end EikonalSupport.DeGiorgi
end

end OAI
