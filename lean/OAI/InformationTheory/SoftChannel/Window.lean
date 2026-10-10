import OAI.InformationTheory.SoftChannel.PairEntropy

namespace OAI

section

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma clipKernel_scaled (b v : ℝ) :
    ell * clipKernel b (ell*v) = clipKernel (b/ell) v := by
  have hL := ell_pos
  have he : ell*v-b = ell*(v-b/ell) := by field_simp
  have hm : max (ell*(v-b/ell)) 0 = ell*max (v-b/ell) 0 := by
    simpa using (mul_max_of_nonneg (v-b/ell) 0 hL.le).symm
  rw [clipKernel,clipKernel,he,hm]
  simp only [mul_pow]
  field_simp

lemma clipKernel_integral_scaled (b q s : ℝ) :
    (∫ h in q..s, clipKernel b h) = ∫ v in q/ell..s/ell, clipKernel (b/ell) v := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := q/ell) (b := s/ell)
    (clipKernel b) ell
  simp only [smul_eq_mul, mul_div_cancel₀ _ ell_pos.ne'] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  exact clipKernel_scaled b v

lemma entropy_interval_bound {x z q s : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hz0 : 0 ≤ z) (hzg : z < (1-x)/(1+x))
    (hql : ell*(1-x-(1+x)*z) ≤ q) (hqs : q ≤ s)
    (hsL : s ≤ ell) (hJ : s-q ≤ ell*z) :
    (∫ h in q..s, clipKernel (Real.log (1+x)) h) ≤
      -(3/2:ℝ)*Real.log (1-((1-x)/(1+x))*z) := by
  have hL := ell_pos
  have hp : 0 < 1+x := by linarith
  have hlo : 0 < 1-x-(1+x)*z := by
    have := (lt_div_iff₀ hp).mp hzg
    nlinarith
  have hq0 : 0 < q := (mul_pos hL hlo).trans_le hql
  let u := min (q/ell) (1-z)
  have hzl : 1-x-(1+x)*z ≤ 1-z := by nlinarith
  have hul : 1-x-(1+x)*z ≤ u := le_min ((le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hql)) hzl
  have huh : u ≤ 1-z := min_le_right _ _
  have huq : u ≤ q/ell := min_le_left _ _
  have hss : s/ell ≤ u+z := by
    dsimp [u]
    rw [← min_add_add_right]
    apply le_min
    · apply (div_le_iff₀ hL).mpr
      have : q/ell*ell = q := div_mul_cancel₀ q hL.ne'
      nlinarith
    · simpa using (div_le_one hL).mpr hsL
  have hu0 : 0 < u := hlo.trans_le hul
  have huz0 : 0 < u+z := by linarith
  rw [clipKernel_integral_scaled]
  calc
    _ ≤ ∫ v in u..u+z, clipKernel (Real.log (1+x)/ell) v :=
      intervalIntegral.integral_mono_interval huq ((div_le_div_iff_of_pos_right hL).mpr hqs)
        hss (Filter.Eventually.of_forall (fun v => clipKernel_nonneg _ v))
        (intervalIntegrable_clipKernel _ hu0 huz0)
    _ ≤ _ := by
      exact thinning_interval hx0 hx1 hz0 hzg hul huh

lemma entropy_common_output {a k : ℝ} (ha : a ∈ Icc (-1) 1) (hk : k ∈ Icc (0:ℝ) 1) :
    k*entropy a ≤ entropy (1-k+k*a) := by
  have h := concaveOn_entropy.2 (by norm_num : (1:ℝ) ∈ Icc (-1) 1) ha
    (by linarith [hk.2] : 0 ≤ 1-k) hk.1 (by ring : 1-k+k=1)
  simpa only [smul_eq_mul,mul_one,entropy_one,mul_zero,zero_add] using h

lemma pair_entropy_floor {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hxd : x+d < 1) :
    (1-x)*entropy (d/(1-x)) ≤ (entropy (x+d)+entropy (x-d))/2 := by
  have hs : 0 < 1-x := by linarith
  have hr : d/(1-x) ∈ Icc (-1) 1 := by
    constructor
    · linarith [div_nonneg hd hs.le]
    · exact (div_le_one hs).mpr (by linarith)
  have hnr : -(d/(1-x)) ∈ Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hk : 1-x ∈ Icc (0:ℝ) 1 := ⟨hs.le,by linarith⟩
  have h₁ := entropy_common_output hr hk
  have h₂ := entropy_common_output hnr hk
  have he₁ : 1-(1-x)+(1-x)*(d/(1-x)) = x+d := by field_simp; ring
  have he₂ : 1-(1-x)+(1-x)*(-(d/(1-x))) = x-d := by field_simp; ring
  rw [he₁] at h₁
  rw [he₂,entropy_neg] at h₂
  linarith

lemma thinning_window {x d e : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1)
    (hefloor : (1-x)*entropy (d/(1-x)) ≤ e)
    (hehi : e ≤ (entropy (x+d)+entropy (x-d))/2) :
    (∫ h in (e+psi x)..(e+ell-(entropy (x+d)+entropy (x-d))/2),
      clipKernel (Real.log (1+x)) h) ≤
      -(3/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hs : 0 < 1-x := by linarith
  have hp : 0 < 1+x := by linarith
  have hh : |x|+|d| < 1 := by rw [abs_of_nonneg hx,abs_of_pos hd]; exact hxd
  let z := d^2/((1-x)*(1+x))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hdz : z < (1-x)/(1+x) := by
    dsimp [z]
    apply (div_lt_div_iff₀ (mul_pos hs hp) hp).mpr
    nlinarith [mul_pos (show 0 < 1-x-d by linarith) (show 0 < 1-x+d by linarith)]
  have hratio : |d/(1-x)| ≤ 1 := by
    rw [abs_of_pos (div_pos hd hs)]
    exact (div_le_one hs).mpr (by linarith)
  have hfloor := mul_le_mul_of_nonneg_left (ell_mul_one_sub_sq_le_entropy hratio) hs.le
  have hfloorEq : (1-x)*(ell*(1-(d/(1-x))^2)) = ell*(1-x-(1+x)*z) := by
    dsimp [z]; field_simp
  rw [hfloorEq] at hfloor
  have hql : ell*(1-x-(1+x)*z) ≤ e+psi x := by linarith [psi_nonneg x]
  have hqs : e+psi x ≤ e+ell-(entropy (x+d)+entropy (x-d))/2 := by
    have h := pairEntropyGap_nonneg x d hh
    simp only [pairEntropyGap,entropy] at h ⊢
    linarith
  have hJ : e+ell-(entropy (x+d)+entropy (x-d))/2-(e+psi x) ≤ ell*z := by
    have h := pairEntropyGap_le_quadratic x d hh
    have heq : 1-x^2 = (1-x)*(1+x) := by ring
    rw [heq] at h
    change pairEntropyGap x d ≤ ell*z at h
    simp only [pairEntropyGap,entropy] at h ⊢
    linarith
  have hzEq : ((1-x)/(1+x))*z = d^2/(1+x)^2 := by
    dsimp [z]; field_simp
  have H := entropy_interval_bound hx (by linarith) hz hdz hql hqs (by linarith) hJ
  rwa [hzEq] at H

end LeanBlast.CourtadeKumar
end
end

end OAI
