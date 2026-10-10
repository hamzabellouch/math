import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.Conformal
noncomputable def profile (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1^m*z.2^α*f (κ*z.1*z.2^β)

lemma profile_contDiffOn {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (profile m α β κ f) {z | 0 < z.2} := by
  apply ContDiffOn.mul
  · exact (contDiffOn_fst.pow m).mul (contDiffOn_snd.rpow_const_of_ne (fun z hz => ne_of_gt hz))
  · exact hf.contDiffOn.comp ((contDiffOn_const.mul contDiffOn_fst).mul
      (contDiffOn_snd.rpow_const_of_ne (fun z hz => ne_of_gt hz))) (mapsTo_univ _ _)

lemma profile_fderiv {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) (h : ℝ × ℝ) :
    fderiv ℝ (profile m α β κ f) (r,z) h =
      ((m:ℝ)*r^(m-1)*h.1*z^α+r^m*(α*z^(α-1)*h.2))*f (κ*r*z^β)+
      (r^m*z^α)*(deriv f (κ*r*z^β)*(κ*h.1*z^β+(κ*r)*(β*z^(β-1)*h.2))) := by
  have hr := (hasFDerivAt_fst : HasFDerivAt (𝕜 := ℝ) (Prod.fst : ℝ × ℝ → ℝ) _ (r,z))
  have hz' := (hasFDerivAt_snd : HasFDerivAt (𝕜 := ℝ) (Prod.snd : ℝ × ℝ → ℝ) _ (r,z))
  have hp := hr.pow m
  have hα := hz'.rpow_const (p := α) (Or.inl hz.ne')
  have hβ := hz'.rpow_const (p := β) (Or.inl hz.ne')
  have ht := (hr.const_mul κ).mul hβ
  have hf' := (hf (κ*r*z^β)).hasDerivAt.comp_hasFDerivAt (r,z) ht
  have hF := (hp.mul hα).mul hf'
  change HasFDerivAt (profile m α β κ f) _ (r,z) at hF
  rw [hF.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.fst,ContinuousLinearMap.snd,smul_eq_mul,Function.comp_def,Pi.mul_apply,
    nsmul_eq_mul]
  dsimp
  ring

lemma profile_partial_r {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (1,0) =
      (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β)+κ*r^m*z^(α+β)*deriv f (κ*r*z^β) := by
  rw [profile_fderiv hf hz,Real.rpow_add hz]
  norm_num only [mul_one,mul_zero,add_zero,zero_add,Prod.fst,Prod.snd]
  ring

lemma profile_partial_z {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (0,1) =
      α*r^m*z^(α-1)*f (κ*r*z^β)+β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β) := by
  have he : z^(α+β-1) = z^α*z^(β-1) := by rw [←Real.rpow_add hz]; congr 1; ring
  rw [profile_fderiv hf hz,he,pow_succ]
  norm_num only [mul_one,mul_zero,add_zero,zero_add,Prod.fst,Prod.snd]
  ring

lemma profile_measurable {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (profile m α β κ f) := by
  exact (measurable_fst.pow_const m |>.mul (measurable_snd.pow measurable_const)).mul
    (hf.comp ((measurable_const.mul measurable_fst).mul (measurable_snd.pow measurable_const)))

lemma profile_zero {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (r : ℝ) :
    profile m α β κ f (r,0) = 0 := by simp [profile,Real.zero_rpow hα.ne']

lemma profile_tendsto_zero {m : ℕ} {α β κ r : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun z => profile m α β κ f (r,z)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hpow (q : ℝ) (hq : 0 < q) : Tendsto (fun z : ℝ => z^q) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne'] using
      (Real.continuousAt_rpow_const (0:ℝ) q (Or.inr hq.le)).tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hpow β hβ).const_mul (κ*r)
  simp only [mul_zero] at ht
  have h := ((hpow α hα).const_mul (r^m)).mul (hf.continuousAt.tendsto.comp ht)
  simpa only [profile,mul_zero,zero_mul,Function.comp_def] using h

lemma profile_partial_r_tendsto_zero {m : ℕ} {α β κ r : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun z => fderiv ℝ (profile m α β κ f) (r,z) (1,0)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have h1 := (profile_tendsto_zero (m := 0) (κ := κ) (r := r) hf.continuous hα hβ).const_mul ((m:ℝ)*r^(m-1))
  have h2 := (profile_tendsto_zero (m := 0) (κ := κ) (r := r) hd (add_pos hα hβ) hβ).const_mul (κ*r^m)
  have h := h1.add h2
  simp only [mul_zero,add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [profile_partial_r (hf.differentiable (by norm_num)) hz]
  simp only [profile,pow_zero,one_mul]
  ring
end CAT0Fillings.Conformal
end

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.Conformal

lemma power_domination {z q a : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q) (hqa : q ≤ a) :
    z^q ≤ 1+z^a := by
  by_cases h : z ≤ 1
  · have hle : z^q ≤ 1 := Real.rpow_le_one hz h hq
    exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg hz _))
  · have hz1 : 1 ≤ z := (lt_of_not_ge h).le
    have hle := Real.rpow_le_rpow_of_exponent_le hz1 hqa
    linarith

lemma monomial_bound {r z R B q a c : ℝ} {m : ℕ} {f : ℝ → ℝ}
    (hr : r ∈ Icc (0:ℝ) R) (hz : 0 ≤ z) (hq : 0 ≤ q) (hqa : q ≤ a)
    (hB : 0 ≤ B) (hf : |f c| ≤ B) :
    |r^m*z^q*f c| ≤ (R^m*B)*(1+z^a) := by
  have hR : 0 ≤ R := hr.1.trans hr.2
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hr.1 _),abs_of_nonneg (Real.rpow_nonneg hz _)]
  have h1 := mul_le_mul (pow_le_pow_left₀ hr.1 hr.2 m) (power_domination hz hq hqa)
    (Real.rpow_nonneg hz q) (pow_nonneg hR m)
  have h2 := (mul_le_mul_of_nonneg_left hf
    (mul_nonneg (pow_nonneg hr.1 m) (Real.rpow_nonneg hz q))).trans
    (mul_le_mul_of_nonneg_right h1 hB)
  nlinarith [h2]

lemma profile_polynomial_growth {m : ℕ} {α β κ R B : ℝ} {f : ℝ → ℝ}
    (hα : 1 ≤ α) (hβ : 0 < β) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hf : Differentiable ℝ f) (hb : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ z : ℝ, 0 < z →
      |profile m α β κ f (r,z)| ≤ C*(1+z^(α+β)) ∧
      |fderiv ℝ (profile m α β κ f) (r,z) (1,0)| ≤ C*(1+z^(α+β)) ∧
      |fderiv ℝ (profile m α β κ f) (r,z) (0,1)| ≤ C*(1+z^(α+β)) := by
  let C0 := R^m*B
  let C1 := (m:ℝ)*(R^(m-1)*B)+|κ| *(R^m*B)
  let C2 := |α| *(R^m*B)+|β*κ| *(R^(m+1)*B)
  have h0 : 0 ≤ C0 := mul_nonneg (pow_nonneg hR _) hB
  have h1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have h2 : 0 ≤ C2 := by dsimp [C2]; positivity
  refine ⟨C0+C1+C2,by positivity,fun r hr z hz => ?_⟩
  have hs : 0 ≤ 1+z^(α+β) := by positivity
  have hf0 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α) (by linarith : α ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hf1 := monomial_bound (m := m-1) hr hz.le (by linarith : 0 ≤ α) (by linarith : α ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hd1 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α+β) le_rfl hB (hb (κ*r*z^β)).2
  have hf2 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α-1) (by linarith : α-1 ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hd2 := monomial_bound (m := m+1) hr hz.le (by linarith : 0 ≤ α+β-1) (by linarith : α+β-1 ≤ α+β)
    hB (hb (κ*r*z^β)).2
  have hrb : |fderiv ℝ (profile m α β κ f) (r,z) (1,0)| ≤ C1*(1+z^(α+β)) := by
    rw [profile_partial_r hf hz]
    apply (abs_add_le _ _).trans
    have he1 : (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β) = (m:ℝ)*(r^(m-1)*z^α*f (κ*r*z^β)) := by ring
    have he2 : κ*r^m*z^(α+β)*deriv f (κ*r*z^β) = κ*(r^m*z^(α+β)*deriv f (κ*r*z^β)) := by ring
    rw [he1,he2,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg m)]
    have H1 := mul_le_mul_of_nonneg_left hf1 (Nat.cast_nonneg (α := ℝ) m)
    have H2 := mul_le_mul_of_nonneg_left hd1 (abs_nonneg κ)
    dsimp [C1]
    simp only [abs_mul] at H1 H2 ⊢
    nlinarith
  have hzb : |fderiv ℝ (profile m α β κ f) (r,z) (0,1)| ≤ C2*(1+z^(α+β)) := by
    rw [profile_partial_z hf hz]
    apply (abs_add_le _ _).trans
    have he1 : α*r^m*z^(α-1)*f (κ*r*z^β) = α*(r^m*z^(α-1)*f (κ*r*z^β)) := by ring
    have he2 : β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β) = (β*κ)*(r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β)) := by ring
    rw [he1,he2,abs_mul,abs_mul]
    have H1 := mul_le_mul_of_nonneg_left hf2 (abs_nonneg α)
    have H2 := mul_le_mul_of_nonneg_left hd2 (abs_nonneg (β*κ))
    dsimp [C2]
    simp only [abs_mul] at H1 H2 ⊢
    nlinarith
  refine ⟨hf0.trans ?_,hrb.trans ?_,hzb.trans ?_⟩ <;>
    apply mul_le_mul_of_nonneg_right _ hs <;> linarith
end CAT0Fillings.Conformal
end

end OAI
