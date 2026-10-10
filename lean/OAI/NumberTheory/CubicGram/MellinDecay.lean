import Mathlib
import OAI.NumberTheory.CubicGram.GramPoisson

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def normProfileFourierSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) : 𝓢(ℂ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) • traceFourierSchwartz (normProfileSchwartz W hW hW' 1
    (by norm_num))

lemma normProfileFourierSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (y : ℂ) :
    normProfileFourierSchwartz W hW hW' y = normProfileFourier W y := by
  simp only [normProfileFourierSchwartz, smul_apply,
    traceFourierSchwartz_apply, normProfileFourier]
  congr 2
  ext z
  simp

theorem radialDualProfile_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1+t)^A * ‖radialDualProfile W t‖ ≤ C := by
  let F := normProfileFourierSchwartz W hW hW'
  let C := 2 ^ (2*A) * (Finset.Iic (2*A,0)).sup
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  have hC : 0 ≤ C := by positivity
  refine ⟨C+1, by linarith, ?_⟩
  intro t ht
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2*A,0)) (k := 2*A) (n := 0) (by rfl) (by rfl) F
      (Real.sqrt t : ℂ)
  simp only [norm_iteratedFDeriv_zero] at hb
  have hn : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsmall : (1+t)^A ≤ (1+‖(Real.sqrt t : ℂ)‖)^(2*A) := by
    rw [hn, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have he : F (Real.sqrt t : ℂ) = radialDualProfile W t :=
    normProfileFourierSchwartz_apply W hW hW' _
  have hbound := mul_le_mul_of_nonneg_right hsmall (_root_.norm_nonneg (F (Real.sqrt t : ℂ)))
  rw [he] at hb hbound
  exact (hbound.trans hb).trans (by dsimp [C]; linarith)

end CubicFirstMoment

namespace CubicFirstMoment

def gramLogBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def gramLogKernel (W : ℝ → ℂ) (ρ u : ℝ) : ℂ :=
  gramLogBump u • normProfileFourier W ((Real.sqrt ρ * Real.exp (u/2) : ℝ) : ℂ)

lemma gramLogKernel_smooth (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    ContDiff ℝ ∞ (gramLogKernel W ρ) := by
  have he : (normProfileFourierSchwartz W hW hW' : ℂ → ℂ) = normProfileFourier W :=
    funext (normProfileFourierSchwartz_apply W hW hW')
  have hF : ContDiff ℝ ∞ (normProfileFourier W) := by
    rw [← he]
    exact (normProfileFourierSchwartz W hW hW').smooth ⊤
  apply gramLogBump.contDiff.smul
  refine hF.comp ?_
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2)))

lemma gramLogKernel_compact (W : ℝ → ℂ) (ρ : ℝ) :
    HasCompactSupport (gramLogKernel W ρ) :=
  gramLogBump.hasCompactSupport.smul_right

def gramLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  (gramLogKernel_compact W ρ).toSchwartzMap (gramLogKernel_smooth W hW hW' ρ)

@[simp] lemma gramLogSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    gramLogSchwartz W hW hW' ρ u = gramLogKernel W ρ u := rfl

lemma gramLogKernel_eq_radial (W : ℝ → ℂ) {ρ u : ℝ} (hρ : 0 ≤ ρ)
    (hu : |u| ≤ 1) :
    gramLogKernel W ρ u = radialDualProfile W (ρ * Real.exp u) := by
  have hcut : gramLogBump u = 1 := gramLogBump.one_of_mem_closedBall
    (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump] using hu)
  rw [gramLogKernel, hcut, one_smul, normProfileFourier_radial]
  congr 1
  rw [Complex.normSq_ofReal]
  calc
    (Real.sqrt ρ * Real.exp (u/2)) * (Real.sqrt ρ * Real.exp (u/2)) =
        (Real.sqrt ρ * Real.sqrt ρ) * (Real.exp (u/2) * Real.exp (u/2)) := by ring
    _ = ρ * Real.exp u := by
      rw [Real.mul_self_sqrt hρ, ← Real.exp_add]
      congr 2
      ring

lemma gramLogKernel_dyad_ratio (W : ℝ → ℂ) {ρ x y : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Set.Icc (1 : ℝ) 2) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    gramLogKernel W ρ (Real.log x - Real.log y) = radialDualProfile W (ρ*x/y) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hxlog : Real.log x ≤ 1 := (Real.log_le_sub_one_of_pos hx0).trans (by linarith [hx.2])
  have hylog : Real.log y ≤ 1 := (Real.log_le_sub_one_of_pos hy0).trans (by linarith [hy.2])
  have hlog : |Real.log x - Real.log y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.log_nonneg hx.1, Real.log_nonneg hy.1]
  rw [gramLogKernel_eq_radial W hρ hlog, Real.exp_sub,
    Real.exp_log hx0, Real.exp_log hy0, mul_div_assoc]

def gramMellinCoefficient (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (gramLogSchwartz W hW hW' ρ) t

def gramMellinPhase (t x : ℝ) : ℂ :=
  (Real.fourierChar (t * Real.log x) : ℂ)

@[simp] lemma norm_gramMellinPhase (t x : ℝ) : ‖gramMellinPhase t x‖ = 1 :=
  Circle.norm_coe _

lemma gramMellinCoefficient_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (gramMellinCoefficient W hW hW' ρ) :=
  (𝓕 (gramLogSchwartz W hW hW' ρ)).integrable

theorem radialDualProfile_mellin_separated (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Set.Icc (1 : ℝ) 2) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      gramMellinCoefficient W hW hW' ρ t * gramMellinPhase t x *
        star (gramMellinPhase t y) := by
  rw [← gramLogKernel_dyad_ratio W hρ hx hy]
  have he := congrArg (fun f : 𝓢(ℝ, ℂ) => f (Real.log x - Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) (gramLogSchwartz W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at he
  rw [← gramLogSchwartz_apply W hW hW' ρ, ← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x - Real.log y) =
      t * Real.log x - t * Real.log y := by
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x - Real.log y)) : ℂ) =
      gramMellinPhase t x * star (gramMellinPhase t y) := by
    rw [hi, AddChar.map_sub_eq_div, div_eq_mul_inv, Circle.coe_mul,
      Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x - Real.log y)) : ℂ) *
      gramMellinCoefficient W hW hW' ρ t = _
  rw [hp]
  ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def gramExp (u : ℝ) : ℂ := (Real.exp (u/2) : ℂ)

lemma gramExp_contDiff : ContDiff ℝ ∞ gramExp :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))

lemma gramExp_deriv_bound (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2 →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2 : ℝ) 2,
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u (abs_le.mp hu)).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma gramExp_scale_growth {c u : ℝ} (hc : 0 ≤ c) (hu : |u| ≤ 2) :
    1+c ≤ Real.exp 1 * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp 1 := by simp
  have hEu : 1 ≤ Real.exp 1 * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ 1 + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_gramExp_comp_uniform (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2 →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := gramExp_deriv_bound n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp 1)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp 1 * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact gramExp_scale_growth hc hu
      _ = (Real.exp 1)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp 1)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp

def gramBumpSchwartz : 𝓢(ℝ, ℝ) :=
  gramLogBump.hasCompactSupport.toSchwartzMap gramLogBump.contDiff

def annularLogSchwartz (F : 𝓢(ℂ, ℂ)) (c : ℝ) : 𝓢(ℝ, ℂ) :=
  (gramLogBump.hasCompactSupport.smul_right (f' := fun u => F (c • gramExp u))).toSchwartzMap
    (gramLogBump.contDiff.smul ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)))

@[simp] lemma annularLogSchwartz_apply (F : 𝓢(ℂ, ℂ)) (c u : ℝ) :
    annularLogSchwartz F c u = gramLogBump u • F (c • gramExp u) := rfl

lemma annularLogSchwartz_deriv_zero (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2) : iteratedFDeriv ℝ n (annularLogSchwartz F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := annularLogSchwartz F c) n hn
  have hb := tsupport_smul_subset_left (gramLogBump : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [gramLogBump.tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump] using hb)

theorem annularLogSchwartz_seminorm_uniform (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (annularLogSchwartz F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_gramExp_comp_uniform F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i gramBumpSchwartz * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨2^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) gramLogBump.contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (annularLogSchwartz F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i gramLogBump u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i gramLogBump u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i gramLogBump u‖ ≤
              SchwartzMap.seminorm ℝ 0 i gramBumpSchwartz := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i gramBumpSchwartz u
            rw [show (gramBumpSchwartz : ℝ → ℝ) = (gramLogBump : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (annularLogSchwartz F c) u‖) := by ring
      _ ≤ 2^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [annularLogSchwartz_deriv_zero F c u n hu, norm_zero, mul_zero]
    positivity

theorem annularLogSchwartz_fourier_uniform (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (𝓕 (annularLogSchwartz F c)) ≤ C := by
  let f : ℝ → 𝓢(ℝ, ℂ) := fun c => (1+c)^K • annularLogSchwartz F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C, hC, hc⟩ := annularLogSchwartz_seminorm_uniform F i.1 i.2 K
    refine ⟨C+1, by linarith, ?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • annularLogSchwartz F c) < _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (pow_pos (by linarith) _)]
    exact (hc c hc0).trans_lt (by linarith)
  have hbf := hb.image (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ))
  obtain ⟨C, hC, hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hbf (k,n)
  refine ⟨C, hC, ?_⟩
  intro c hc0
  have hmem : SchwartzMap.fourierTransformCLM ℝ (f c) ∈
      SchwartzMap.fourierTransformCLM ℝ '' (f '' Set.Ici 0) :=
    ⟨f c, ⟨c, hc0, rfl⟩, rfl⟩
  have h := hc _ hmem
  change SchwartzMap.seminorm ℝ k n
    (SchwartzMap.fourierTransformCLM ℝ ((1+c)^K • annularLogSchwartz F c)) < C at h
  rw [map_smul, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem annularLogSchwartz_fourier_L1_uniform (F : 𝓢(ℂ, ℂ)) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * (∫ t : ℝ, ‖𝓕 (annularLogSchwartz F c) t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k : ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀, hC₀, hc₀⟩ := annularLogSchwartz_fourier_uniform F 0 0 K
  obtain ⟨C₁, hC₁, hc₁⟩ := annularLogSchwartz_fourier_uniform F k 0 K
  refine ⟨D*(C₀+C₁)+1, by positivity, ?_⟩
  intro c hc
  have h := (𝓕 (annularLogSchwartz F c)).integral_pow_mul_iteratedFDeriv_le ℝ volume 0 0
  simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul, zero_add] at h
  have hb : (1+c)^K * (∫ t : ℝ, ‖𝓕 (annularLogSchwartz F c) t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+c)^K * (D * (SchwartzMap.seminorm ℝ 0 0 (𝓕 (annularLogSchwartz F c)) +
            SchwartzMap.seminorm ℝ k 0 (𝓕 (annularLogSchwartz F c)))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = D*((1+c)^K * SchwartzMap.seminorm ℝ 0 0 (𝓕 (annularLogSchwartz F c)) +
            (1+c)^K * SchwartzMap.seminorm ℝ k 0 (𝓕 (annularLogSchwartz F c))) := by ring
      _ ≤ D*(C₀+C₁) := mul_le_mul_of_nonneg_left (add_le_add (hc₀ c hc) (hc₁ c hc)) hD
  linarith

lemma annularLogSchwartz_eq_gramLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    annularLogSchwartz (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      gramLogSchwartz W hW hW' ρ := by
  ext u
  simp only [annularLogSchwartz_apply, gramLogSchwartz_apply, gramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

theorem gramMellinCoefficient_mass_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) ≤ C := by
  obtain ⟨C, hC, hc⟩ := annularLogSchwartz_fourier_L1_uniform
    (normProfileFourierSchwartz W hW hW') (2*A)
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ, Real.sqrt_nonneg ρ]
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [annularLogSchwartz_eq_gramLogSchwartz W hW hW' ρ] at h
  exact (mul_le_mul_of_nonneg_right hs (integral_nonneg (fun t => _root_.norm_nonneg _))).trans h

theorem gramMellinCoefficient_pointwise_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^A * ‖t‖^B * ‖gramMellinCoefficient W hW hW' ρ t‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := annularLogSchwartz_fourier_uniform
    (normProfileFourierSchwartz W hW hW') B 0 (2*A)
  refine ⟨C, hC, ?_⟩
  intro ρ hρ t
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ, Real.sqrt_nonneg ρ]
  have hb := SchwartzMap.le_seminorm ℝ B 0 (𝓕 (gramLogSchwartz W hW hW' ρ)) t
  simp only [norm_iteratedFDeriv_zero] at hb
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [annularLogSchwartz_eq_gramLogSchwartz W hW hW' ρ] at h
  calc
    _ = (1+ρ)^A * (‖t‖^B * ‖gramMellinCoefficient W hW hW' ρ t‖) := by ring
    _ ≤ (1+Real.sqrt ρ)^(2*A) *
        SchwartzMap.seminorm ℝ B 0 (𝓕 (gramLogSchwartz W hW hW' ρ)) :=
      mul_le_mul hs hb (by positivity) (by positivity)
    _ ≤ C := h

end CubicFirstMoment
end
end

end OAI
