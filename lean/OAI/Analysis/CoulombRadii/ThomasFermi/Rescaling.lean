import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.SpatialAnnulus
import OAI.Analysis.CoulombRadii.FieldAnalysis.Field

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def scaledDensity (D : ℝ) (σ : Position → ℝ) (x : Position) : ℝ := D^6*σ (D • x)

theorem scaledDensity_integrable {D : ℝ} (hD : 0 < D) {σ : Position → ℝ}
    (hi : Integrable σ) : Integrable (scaledDensity D σ) :=
  (hi.comp_smul hD.ne').const_mul _

theorem integral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) :
    (∫ x, scaledDensity D σ x) = D^3*(∫ x, σ x) := by
  unfold scaledDensity
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume σ D (hR := hD.le)]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem coulombKernel_smul {D : ℝ} (hD : 0 < D) (x : Position) :
    coulombKernel (D • x) = D⁻¹*coulombKernel x := by
  simp only [coulombKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_inv_rev, mul_comm]

theorem potentialOf_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (x : Position) :
    potentialOf (scaledDensity D σ) x = D^4*potentialOf σ (D • x) := by
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun y => coulombKernel (D • x-y)*σ y) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at h
  simp_rw [← smul_sub, coulombKernel_smul hD, mul_assoc, integral_const_mul] at h
  unfold potentialOf scaledDensity
  simp_rw [show ∀ y, coulombKernel (x-y)*(D^6*σ (D • y)) =
    D^6*(coulombKernel (x-y)*σ (D • y)) by intro y; ring, integral_const_mul]
  field_simp [hD.ne'] at h ⊢
  nlinarith [h]

theorem screenedField_scaledDensity {D : ℝ} (hD : 0 < D) (lam : ℝ)
    (σ : Position → ℝ) (x : Position) :
    screenedField (D^3*lam) (scaledDensity D σ) x =
      D^4*screenedField lam σ (D • x) := by
  rw [screenedField, screenedField, potentialOf_scaledDensity hD,
    coulombKernel_smul hD]
  field_simp

theorem WeakNuclearSubsolution.dilate {U q : Position → ℝ} {lam : ℝ}
    {D : ℝ} (hD : 0 < D) (hw : WeakNuclearSubsolution U lam Set.univ q) :
    WeakNuclearSubsolution (fun x => D^4*U (D • x)) (D^3*lam) Set.univ
      (scaledDensity D q) := by
  intro φ hφ hc _ht hφp
  let e : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 D⁻¹ (inv_ne_zero hD.ne'))
  let ψ : Position → ℝ := fun x => φ (D⁻¹ • x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul D⁻¹)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e
  have hid (x : Position) : D⁻¹ • (D • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hLap (x : Position) : coordinateLaplacian ψ (D • x) =
      (D⁻¹)^2*coordinateLaplacian φ x := by
    change coordinateLaplacian (fun y => φ (D⁻¹ • y)) (D • x) = _
    rw [coordinateLaplacian_comp_smul, hid]
  have hleft := Measure.integral_comp_smul_of_nonneg volume
    (fun x => U x*coordinateLaplacian ψ x) D (hR := hD.le)
  have hright := Measure.integral_comp_smul_of_nonneg volume
    (fun x => q x*ψ x) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at hleft hright
  simp_rw [hLap, show ∀ x, U (D • x)*((D⁻¹)^2*coordinateLaplacian φ x) =
    (D⁻¹)^2*(U (D • x)*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul] at hleft
  simp only [ψ, hid] at hright
  have hwe := mul_le_mul_of_nonneg_left
    (hw ψ hψ hψc (Set.subset_univ _) (fun x => hφp _)) (pow_nonneg hD.le 3)
  have hψ0 : ψ 0 = φ 0 := by simp [ψ]
  rw [hψ0] at hwe
  have hli : D^4*(∫ x, U (D • x)*coordinateLaplacian φ x) =
      D^3*(∫ x, U x*coordinateLaplacian ψ x) := by
    field_simp [hD.ne'] at hleft
    rw [← hleft]
    ring
  have hri : D^6*(∫ x, q (D • x)*φ x) = D^3*(∫ x, q x*ψ x) := by
    field_simp [hD.ne'] at hright
    simp only [one_div] at hright
    change (∫ x, q (D • x)*φ x)*D^3 = (∫ x, q x*ψ x) at hright
    rw [← hright]
    ring
  simp only [scaledDensity, mul_assoc, integral_const_mul]
  rw [hli, hri]
  linarith

theorem barrierSource_dilate {D : ℝ} (hD : 0 < D) (r : ℝ)
    (U σ p : Position → ℝ) (x : Position) :
    barrierSource (r/D) (fun y => D^4*U (D • y))
      (scaledDensity D σ) (scaledDensity D p) x =
        scaledDensity D (barrierSource r U σ p) x := by
  have hlt : ‖D • x‖ < r ↔ ‖x‖ < r/D := by
    rw [lt_div_iff₀ hD, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm]
  have hle : r ≤ ‖D • x‖ ↔ r/D ≤ ‖x‖ := by
    rw [div_le_iff₀ hD, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm]
  simp only [barrierSource, cutoffReaction, scaledDensity, Set.indicator_apply,
    Set.mem_ofPred_eq, hlt, hle, tfReaction_dilate hD]
  split_ifs <;> ring

theorem WeakNuclearSubsolution.dilate_barrier {D : ℝ} (hD : 0 < D)
    {U σ p : Position → ℝ} {lam r : ℝ}
    (hw : WeakNuclearSubsolution U lam Set.univ (barrierSource r U σ p)) :
    WeakNuclearSubsolution (fun x => D^4*U (D • x)) (D^3*lam) Set.univ
      (barrierSource (r/D) (fun x => D^4*U (D • x))
        (scaledDensity D σ) (scaledDensity D p)) := by
  simpa only [show barrierSource (r/D) (fun x => D^4*U (D • x))
      (scaledDensity D σ) (scaledDensity D p) =
        scaledDensity D (barrierSource r U σ p) from funext (barrierSource_dilate hD r U σ p)]
    using hw.dilate hD

theorem scaledDensity_nonneg {D : ℝ} {σ : Position → ℝ}
    (hσ : ∀ x, 0 ≤ σ x) (x : Position) : 0 ≤ scaledDensity D σ x :=
  mul_nonneg (by positivity) (hσ _)

theorem scaledDensity_bound {D A : ℝ} {σ : Position → ℝ}
    (hσ : ∀ x, σ x ≤ A) (x : Position) : scaledDensity D σ x ≤ D^6*A :=
  mul_le_mul_of_nonneg_left (hσ _) (by positivity)

theorem scaledDensity_support {D r : ℝ} (hD : 0 < D) {p : Position → ℝ}
    (hp : ∀ x, r < ‖x‖ → p x = 0) (x : Position) (hx : r/D < ‖x‖) :
    scaledDensity D p x = 0 := by
  have hh : r < ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_lt_iff₀ hD).mp hx
  simp only [scaledDensity, hp _ hh, mul_zero]

theorem barrier_bounds_dilate {D r B C : ℝ} (hD : 0 < D) {U : Position → ℝ}
    (hbound : ∀ y, r ≤ ‖y‖ →
      B/‖y‖^4*(1-r/(8*‖y‖)) ≤ U y ∧ U y ≤ C/‖y‖^4)
    (x : Position) (hx : r/D ≤ ‖x‖) :
    B/‖x‖^4*(1-(r/D)/(8*‖x‖)) ≤ D^4*U (D • x) ∧
      D^4*U (D • x) ≤ C/‖x‖^4 := by
  have hh : r ≤ ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_le_iff₀ hD).mp hx
  have hb := hbound _ hh
  have hnorm : ‖D • x‖ = D*‖x‖ := by simp [norm_smul, abs_of_pos hD]
  have hlo : D^4*(B/‖D • x‖^4*(1-r/(8*‖D • x‖))) =
      B/‖x‖^4*(1-(r/D)/(8*‖x‖)) := by
    rw [hnorm]
    by_cases hz : ‖x‖ = 0
    · simp [hz]
    · field_simp
  have hup : D^4*(C/‖D • x‖^4) = C/‖x‖^4 := by
    rw [hnorm, mul_pow]
    field_simp
  constructor
  · rw [← hlo]
    exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · rw [← hup]
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

theorem tfDensityScalar_dilate {D : ℝ} (hD : 0 < D) (t : ℝ) :
    tfDensityScalar (D^4*t) = D^6*tfDensityScalar t := by
  have hm : max (D^4*t) 0 = D^4*max t 0 := by
    rw [mul_max_of_nonneg t 0 (pow_nonneg hD.le 4), mul_zero]
  have hr : (D^4)^(3/2 : ℝ) = D^6 := by
    rw [← Real.rpow_natCast D 4, ← Real.rpow_mul hD.le]
    norm_num
  rw [tfDensityScalar, hm, Real.mul_rpow (pow_nonneg hD.le 4) (le_max_right t 0), hr,
    tfDensityScalar]
  ring

theorem mul_inverse_power_dilate {D : ℝ} (hD : 0 < D) (C : ℝ) (n : ℕ) (x : Position) :
    D^n*(C/‖D • x‖^n) = C/‖x‖^n := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_pow]
  field_simp

theorem screened_comparison_dilate {D r q C δ lam : ℝ} (hD : 0 < D)
    {σ : Position → ℝ}
    (hbound : ∀ y, r ≤ ‖y‖ → ‖y‖ ≤ q*D →
      screenedField lam σ y ≤ C/‖y‖^4 ∧
      |σ y-tfDensityScalar (screenedField lam σ y)| ≤ δ/‖y‖^6)
    (x : Position) (hx : r/D ≤ ‖x‖) (hxq : ‖x‖ ≤ q) :
    screenedField (D^3*lam) (scaledDensity D σ) x ≤ C/‖x‖^4 ∧
      |scaledDensity D σ x-tfDensityScalar
        (screenedField (D^3*lam) (scaledDensity D σ) x)| ≤ δ/‖x‖^6 := by
  have hxl : r ≤ ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_le_iff₀ hD).mp hx
  have hxu : ‖D • x‖ ≤ q*D := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      mul_le_mul_of_nonneg_left hxq hD.le
  obtain ⟨hc,he⟩ := hbound _ hxl hxu
  rw [screenedField_scaledDensity hD, tfDensityScalar_dilate hD]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg hD.le 4)
    rwa [mul_inverse_power_dilate hD] at hh
  · have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hD.le 6)
    rw [mul_inverse_power_dilate hD] at hh
    simpa only [scaledDensity, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hD.le 6)] using hh

theorem setIntegral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (S : Set Position) :
    (∫ x in S, scaledDensity D σ x) = D^3*(∫ x in D • S, σ x) := by
  unfold scaledDensity
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume σ S hD]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  field_simp

theorem smul_spatialAnnulus {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    D • spatialAnnulus a b = spatialAnnulus (a*D) (b*D) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hD.ne']
  simp only [spatialAnnulus, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hD), ← div_eq_inv_mul]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨(lt_div_iff₀ hD).mp ha, (div_lt_iff₀ hD).mp hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨(lt_div_iff₀ hD).mpr ha, (div_lt_iff₀ hD).mpr hb⟩

theorem annularIntegral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (a b : ℝ) :
    (∫ x in spatialAnnulus a b, scaledDensity D σ x) =
      D^3*(∫ x in spatialAnnulus (a*D) (b*D), σ x) := by
  rw [setIntegral_scaledDensity hD, smul_spatialAnnulus hD]

structure PhysicalRetainedFamily (Θ : ℕ → Type*) where
  μ : ∀ n, Θ n → Position → ℝ
  u : ∀ n, Θ n → Position → ℝ
  p : ∀ n, Θ n → Position → ℝ
  Z : ℕ → ℕ
  s : ℕ → ℝ
  r : ℕ → ℝ
  q : ℕ → ℕ
  Aμ : ∀ n, Θ n → ℝ
  Ap : ∀ n, Θ n → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  sp : ∀ n, 0 < s n
  rp : ∀ n, 0 < r n
  slim : Tendsto s atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  rlo : ∀ n, 1/(2*(q n : ℝ)) ≤ r n/s n
  rhi : ∀ n, r n/s n ≤ ((q n : ℝ))⁻¹
  μi : ∀ n θ, Integrable (μ n θ)
  μp : ∀ n θ x, 0 ≤ μ n θ x
  μb : ∀ n θ x, μ n θ x ≤ Aμ n θ
  μmass : ∀ n θ, (∫ x, μ n θ x) = (Z n : ℝ)
  pi : ∀ n θ, Integrable (p n θ)
  pp : ∀ n θ x, 0 ≤ p n θ x
  pb : ∀ n θ x, p n θ x ≤ Ap n θ
  ps : ∀ n θ x, r n < ‖x‖ → p n θ x = 0
  pm : ∀ n θ, (∫ x, p n θ x) ≤ 1
  ucont : ∀ n θ, Continuous (fun x => u n θ x-(Z n : ℝ)*coulombKernel x)
  ubounds : ∀ n θ x, r n ≤ ‖x‖ →
    B/‖x‖^4*(1-r n/(8*‖x‖)) ≤ u n θ x ∧ u n θ x ≤ Cinv/‖x‖^4
  uweak : ∀ n θ, WeakNuclearSubsolution (u n θ) (Z n : ℝ) Set.univ
    (barrierSource (r n) (u n θ) (μ n θ) (p n θ))
  band : ∀ n θ x, r n ≤ ‖x‖ → ‖x‖ ≤ (q n : ℝ)*s n →
    screenedField (Z n : ℝ) (μ n θ) x ≤ Ccap/‖x‖^4 ∧
    |μ n θ x-tfDensityScalar (screenedField (Z n : ℝ) (μ n θ) x)| ≤
      (((q n : ℝ)^8)⁻¹)/‖x‖^6

theorem continuous_scaled_offset {D z : ℝ} (hD : 0 < D) {u : Position → ℝ}
    (hu : Continuous (fun x => u x-z*coulombKernel x)) :
    Continuous (fun x => D^4*u (D • x)-(D^3*z)*coulombKernel x) := by
  have he : (fun x => D^4*u (D • x)-(D^3*z)*coulombKernel x) =
      fun x => D^4*(u (D • x)-z*coulombKernel (D • x)) := by
    funext x
    simp only [coulombKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_inv_rev]
    field_simp
  rw [he]
  exact (hu.comp (continuous_const_smul D)).const_mul _

def PhysicalRetainedFamily.toAnalytic {Θ : ℕ → Type*} (d : PhysicalRetainedFamily Θ) :
    RetainedAnalyticFamily Θ where
  σ := fun n θ => scaledDensity (d.s n) (d.μ n θ)
  U := fun n θ x => d.s n^4*d.u n θ (d.s n • x)
  p := fun n θ => scaledDensity (d.s n) (d.p n θ)
  lam := fun n => d.s n^3*(d.Z n : ℝ)
  a := fun n => d.r n/d.s n
  q := fun n => (d.q n : ℝ)
  ε := fun n => d.s n^3
  Aσ := fun n θ => d.s n^6*d.Aμ n θ
  Ap := fun n θ => d.s n^6*d.Ap n θ
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n θ => scaledDensity_integrable (d.sp n) (d.μi n θ)
  σp := fun n θ => scaledDensity_nonneg (d.μp n θ)
  σb := fun n θ => scaledDensity_bound (d.μb n θ)
  σmass := fun n θ => by rw [integral_scaledDensity (d.sp n), d.μmass]
  pi := fun n θ => scaledDensity_integrable (d.sp n) (d.pi n θ)
  pp := fun n θ => scaledDensity_nonneg (d.pp n θ)
  pb := fun n θ => scaledDensity_bound (d.pb n θ)
  ps := fun n θ => scaledDensity_support (d.sp n) (d.ps n θ)
  pm := fun n θ => by
    rw [integral_scaledDensity (d.sp n)]
    exact (mul_le_mul_of_nonneg_left (d.pm n θ) (pow_nonneg (d.sp n).le 3)).trans_eq
      (mul_one _)
  εlim := by simpa using d.slim.pow 3
  apos := fun n => div_pos (d.rp n) (d.sp n)
  alim := by
    apply squeeze_zero (fun n => (div_pos (d.rp n) (d.sp n)).le) d.rhi
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp d.qlim)
  qlim := tendsto_natCast_atTop_atTop.comp d.qlim
  aq := Eventually.of_forall d.rlo
  Ucont := fun n θ => continuous_scaled_offset (d.sp n) (d.ucont n θ)
  Ulower := fun n θ x hx => (barrier_bounds_dilate (d.sp n) (d.ubounds n θ) x hx).1
  Uupper := fun n θ x hx => (barrier_bounds_dilate (d.sp n) (d.ubounds n θ) x hx).2
  Uweak := fun n θ => (d.uweak n θ).dilate_barrier (d.sp n)
  cap := fun n θ x hx hxq => (screened_comparison_dilate (d.sp n) (d.band n θ) x hx hxq).1
  err := fun n θ x hx hxq => by
    simpa only [div_eq_mul_inv] using
      (screened_comparison_dilate (d.sp n) (d.band n θ) x hx hxq).2

end NeutralAtom
end

end

end OAI
