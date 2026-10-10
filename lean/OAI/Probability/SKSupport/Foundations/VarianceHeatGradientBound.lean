import Mathlib
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily
import OAI.Probability.SKSupport.Foundations.InvSqrtNegHalf

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma varianceHeat_gradient_bound {g : ℝ → ℝ} (hg : BoundedSmooth g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |g z| ≤ C) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv (varianceHeat h g) x| ≤ kernelConstant*C/Real.sqrt h := by
  change |deriv (scaled (Real.sqrt h) g) x| ≤ _
  exact scaled_gradient_bound hg (C := ⟨C,hC⟩) hbound (Real.sqrt_pos.mpr hh) x

lemma deriv_varianceHeat_of_bounded {g : ℝ → ℝ} (hg : BoundedSmooth g) (h : ℝ) :
    deriv (varianceHeat h g) = varianceHeat h (deriv g) := by
  obtain ⟨A,hA⟩ := hg.bound
  obtain ⟨B,hB⟩ := hg.deriv.bound
  exact deriv_varianceHeat (hg.smooth.of_le (by simp))
    (ExponentialBound.of_bounded hA) (ExponentialBound.of_bounded hB) h

lemma deriv_of_mild {V G : ℝ → ℝ → ℝ} {A B : ℝ≥0} {t b : ℝ}
    (hV : BoundedSmooth (V b)) (hm : Measurable (fun p : ℝ × ℝ => G p.1 p.2))
    (hG : ∀ r, BoundedSmooth (G r)) (hA : ∀ r z, |G r z| ≤ A)
    (hB : ∀ r z, |deriv (G r) z| ≤ B)
    (hmild : ∀ x, V t x = varianceHeat (b-t) (V b) x+
      ∫ r in t..b, varianceHeat (r-t) (G r) x) (x : ℝ) :
    deriv (V t) x = deriv (varianceHeat (b-t) (V b)) x+
      ∫ r in t..b, deriv (varianceHeat (r-t) (G r)) x := by
  have hDt := hasDerivAt_integral_varianceHeat hm hG hA hB t b x
  obtain ⟨C,hC⟩ := hV.bound
  obtain ⟨D,hD⟩ := hV.deriv.bound
  have hHt : HasDerivAt (varianceHeat (b-t) (V b)) (varianceHeat (b-t) (deriv (V b)) x) x :=
    hasDerivAt_scaled_space (hV.smooth.of_le (by simp))
      (ExponentialBound.of_bounded hC) (ExponentialBound.of_bounded hD) (Real.sqrt (b-t)) x
  have heV : V t = fun z => varianceHeat (b-t) (V b) z+∫ r in t..b, varianceHeat (r-t) (G r) z := funext hmild
  have hdR : deriv (fun z => varianceHeat (b-t) (V b) z+∫ r in t..b, varianceHeat (r-t) (G r) z) x =
      varianceHeat (b-t) (deriv (V b)) x+∫ r in t..b, varianceHeat (r-t) (deriv (G r)) x := (hHt.add hDt).deriv
  rw [heV,hdR]
  simp_rw [deriv_varianceHeat_of_bounded hV,deriv_varianceHeat_of_bounded (hG _)]

lemma uniform_gradient_bound_of_mild {V G : ℝ → ℝ → ℝ} {A₀ B₀ : ℝ≥0}
    {a b A D R C : ℝ} (hab : a < b) (hA : 0 ≤ A) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hV : BoundedSmooth (V b)) (hm : Measurable (fun p : ℝ × ℝ => G p.1 p.2))
    (hG : ∀ r, BoundedSmooth (G r)) (hA₀ : ∀ r z, |G r z| ≤ A₀)
    (hB₀ : ∀ r z, |deriv (G r) z| ≤ B₀)
    (hC : ∀ r ∈ Icc a b, ∀ x, |deriv (V r) x| ≤ C)
    (hterminal : ∀ x, |V b x| ≤ A)
    (hsource : ∀ r ∈ Icc a b, ∀ x, |G r x| ≤ D*|deriv (V r) x|+R)
    (hmild : ∀ t ∈ Ico a b, ∀ x, V t x = varianceHeat (b-t) (V b) x+
      ∫ r in t..b, varianceHeat (r-t) (G r) x)
    (hsmall : 8*kernelConstant*D*Real.sqrt (b-a) ≤ 1/2) (x : ℝ) :
    |deriv (V a) x| ≤ 2*kernelConstant*(A+2*R*(b-a))/Real.sqrt (b-a) := by
  let W : ℝ → ℝ → ℝ := fun r => deriv (V r)
  let M : ℝ := weightedSize W a b
  have hM : 0 ≤ M := weightedSize_nonneg hab.le hC
  have hκ := kernelConstant_nonneg
  have hpoint (t : ℝ) (ht : t ∈ Ico a b) (z : ℝ) :
      Real.sqrt (b-t)*|W t z| ≤ kernelConstant*(A+2*R*(b-a))+
        (8*kernelConstant*D)*Real.sqrt (b-t)*M := by
    have htb : 0 < b-t := sub_pos.mpr ht.2
    have hs : 0 < Real.sqrt (b-t) := Real.sqrt_pos.mpr htb
    let H : ℝ → ℝ := fun r => (kernelConstant*D*M)*(1/(Real.sqrt (r-t)*Real.sqrt (b-r)))+
      (kernelConstant*R)*(1/Real.sqrt (r-t))
    have hHi : IntervalIntegrable H volume t b :=
      ((intervalIntegrable_sqrt_kernel ht.2).const_mul _).add
        ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul _)
    have hdom (r : ℝ) (hr : r ∈ Ioo t b) :
        |deriv (varianceHeat (r-t) (G r)) z| ≤ H r := by
      have hrab : r ∈ Ico a b := ⟨ht.1.trans hr.1.le,hr.2⟩
      have hwr (y : ℝ) : |W r y| ≤ M/Real.sqrt (b-r) := abs_le_weightedSize hC hrab y
      have hbnd (y : ℝ) : |G r y| ≤ D*(M/Real.sqrt (b-r))+R :=
        (hsource r ⟨hrab.1,hrab.2.le⟩ y).trans (add_le_add (mul_le_mul_of_nonneg_left (hwr y) hD) le_rfl)
      have hbnd0 : 0 ≤ D*(M/Real.sqrt (b-r))+R := by positivity
      apply (varianceHeat_gradient_bound (hG r) hbnd0 hbnd (sub_pos.mpr hr.1) z).trans_eq
      dsimp only [H]
      field_simp
    have hnorm : |∫ r in t..b, deriv (varianceHeat (r-t) (G r)) z| ≤ ∫ r in t..b, H r := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le ht.2.le _ hHi
      filter_upwards [volume.ae_ne b] with r hrb hr
      simpa only [Real.norm_eq_abs] using hdom r ⟨hr.1,lt_of_le_of_ne hr.2 hrb⟩
    have hHbound : (∫ r in t..b,H r) ≤ 8*kernelConstant*D*M+2*kernelConstant*R*Real.sqrt (b-t) := by
      dsimp only [H]
      rw [intervalIntegral.integral_add ((intervalIntegrable_sqrt_kernel ht.2).const_mul _)
        ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul _),intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,integral_inv_sqrt_sub ht.2.le]
      have hh := mul_le_mul_of_nonneg_left (integral_sqrt_kernel_le ht.2)
        (show 0 ≤ kernelConstant*D*M by positivity)
      nlinarith
    have he := deriv_of_mild hV hm hG hA₀ hB₀ (hmild t ht) z
    have hinitial := varianceHeat_gradient_bound hV hA hterminal htb z
    have hsum : |W t z| ≤ kernelConstant*A/Real.sqrt (b-t)+
        8*kernelConstant*D*M+2*kernelConstant*R*Real.sqrt (b-t) := by
      change |deriv (V t) z| ≤ _
      rw [he]
      have hh := abs_add_le (deriv (varianceHeat (b-t) (V b)) z)
        (∫ r in t..b, deriv (varianceHeat (r-t) (G r)) z)
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hsum hs.le
    have hcancel : Real.sqrt (b-t)*(kernelConstant*A/Real.sqrt (b-t)) = kernelConstant*A := by
      field_simp
    have hsq := Real.sq_sqrt htb.le
    have hgap : b-t ≤ b-a := by linarith [ht.1]
    have hrr := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*kernelConstant*R by positivity)
    have hscaled' : Real.sqrt (b-t)*|W t z| ≤ kernelConstant*A+
        8*kernelConstant*D*Real.sqrt (b-t)*M+2*kernelConstant*R*(b-t) := by
      apply hscaled.trans_eq
      rw [mul_add,mul_add,hcancel]
      have he : Real.sqrt (b-t)*(2*kernelConstant*R*Real.sqrt (b-t)) = 2*kernelConstant*R*(b-t) := by
        calc
          _ = 2*kernelConstant*R*(Real.sqrt (b-t))^2 := by ring
          _ = _ := by rw [hsq]
      rw [he]
      ring
    nlinarith [hscaled']
  have hMbound : M ≤ 2*(kernelConstant*(A+2*R*(b-a))) :=
    weighted_absorption hab hC (by positivity) (by positivity) hsmall hpoint
  have hw := abs_le_weightedSize hC (t := a) ⟨le_rfl,hab⟩ x
  apply hw.trans
  exact (div_le_div_of_nonneg_right hMbound (Real.sqrt_nonneg _)).trans_eq (by ring)

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma iteratedDeriv_mild {V G : ℝ → ℝ → ℝ}
    (hV : BoundedSmoothFamily V) (hG : BoundedSmoothFamily G) {a b : ℝ}
    (hmild : ∀ z, V a z = varianceHeat (b-a) (V b) z+
      ∫ r in a..b, varianceHeat (r-a) (G r) z) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (V a) x = varianceHeat (b-a) (iteratedDeriv n (V b)) x+
      ∫ r in a..b, varianceHeat (r-a) (iteratedDeriv n (G r)) x := by
  induction n generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using hmild x
  | succ n ih =>
    have hGn := hG.iteratedDeriv n
    obtain ⟨A,hA⟩ := hGn.bound
    obtain ⟨B,hB⟩ := hGn.deriv.bound
    have hd := deriv_of_mild (V := fun t => iteratedDeriv n (V t))
      ((hV.iteratedDeriv n).regular b) hGn.measurable hGn.regular hA hB ih x
    simp_rw [deriv_varianceHeat_of_bounded ((hV.iteratedDeriv n).regular b),
      deriv_varianceHeat_of_bounded (hGn.regular _)] at hd
    simpa only [iteratedDeriv_succ] using hd

lemma burgers_source_derivative_bound {U : ℝ → ℝ} (hU : BoundedSmooth U)
    {C : ℝ} (hC : 0 ≤ C) (hU1 : ∀ x, |U x| ≤ 1) (n : ℕ)
    (hb : ∀ j ≤ n, ∀ x, |iteratedDeriv j U x| ≤ C) (x : ℝ) :
    |iteratedDeriv n (fun z => U z*deriv U z) x| ≤ |iteratedDeriv (n+1) U x|+
      (∑ j ∈ Finset.range n, (n.choose (j+1):ℝ))*C^2 := by
  rw [iteratedDeriv_fun_mul
    (hU.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    (hU.deriv.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right,Nat.cast_one,iteratedDeriv_zero,one_mul,Nat.sub_zero,
    ← iteratedDeriv_succ']
  apply (abs_add_le _ _).trans
  have hlead : |U x*iteratedDeriv (n+1) U x| ≤ |iteratedDeriv (n+1) U x| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hU1 x) (abs_nonneg (iteratedDeriv (n+1) U x))
  have hrem : |∑ j ∈ Finset.range n,
      (n.choose (j+1):ℝ)*iteratedDeriv (j+1) U x*iteratedDeriv (n-(j+1)+1) U x| ≤
        (∑ j ∈ Finset.range n,(n.choose (j+1):ℝ))*C^2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hb (j+1) (by omega) x
    have h2 := hb (n-(j+1)+1) (by omega) x
    have hh := mul_le_mul h1 h2 (abs_nonneg _) hC
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ (n.choose (j+1):ℝ) by positivity)
    nlinarith
  simpa only [add_comm] using add_le_add hrem hlead

lemma iteratedDeriv_finiteBurgersSource_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i n : ℕ)
    {C D t : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hcoef : finiteCoeff c h N i t ≤ D)
    (hb : ∀ j ≤ n, ∀ x, |iteratedDeriv j (deriv (finiteValue c h f N i t)) x| ≤ C) (x : ℝ) :
    |iteratedDeriv n (finiteBurgersSource c h f N i t) x| ≤
      D*|deriv (iteratedDeriv n (deriv (finiteValue c h f N i t))) x|+
        D*(∑ j ∈ Finset.range n,(n.choose (j+1):ℝ))*C^2 := by
  have hUnn : 0 ≤ finiteCoeff c h N i t := by
    obtain ⟨K,hK⟩ := finiteCoeff_bounds c h N i; exact (hK t).1
  have hU1 (z : ℝ) : |deriv (finiteValue c h f N i t) z| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := z) (finiteValue_lipschitz hLip c h N i t)
  have hbnd := burgers_source_derivative_bound
    (finiteValue_regular hf hLip c h N i t).deriv_bounded hC hU1 n hb x
  change |iteratedDeriv n (fun z => finiteCoeff c h N i t*
    (deriv (finiteValue c h f N i t) z*deriv (deriv (finiteValue c h f N i t)) z)) x| ≤ _
  rw [iteratedDeriv_const_mul_field,abs_mul,abs_of_nonneg hUnn]
  have hm := mul_le_mul hcoef hbnd (abs_nonneg _) hD
  apply hm.trans_eq
  simp only [iteratedDeriv_succ]
  ring

end ZeroTemperatureSK.Heat

end
end
end
end
end

end OAI
