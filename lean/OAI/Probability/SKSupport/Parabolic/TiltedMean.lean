import Mathlib
import OAI.Probability.SKSupport.Foundations.BoundedSmooth

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
namespace ZeroTemperatureSK.Heat

def tiltedMean (c : ℝ) (h : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  semigroup h (fun z => g z*Real.exp (c*f z)) x /
    semigroup h (fun z => Real.exp (c*f z)) x

lemma tiltedMean_bound {f g : ℝ → ℝ} {K G : ℝ≥0}
    (hLip : LipschitzWith K f) (hgm : Measurable g) (hG : ∀ x, |g x| ≤ G)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) : |tiltedMean c h f g x| ≤ G := by
  have hE := semigroup_exp_pos hLip c h x
  unfold tiltedMean
  rw [abs_div, abs_of_pos hE, div_le_iff₀ hE]
  unfold semigroup
  rw [← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (integrable_weight_exp_translate hLip hgm hG c h x).abs
    ((integrable_exp_translate_of_lipschitz hLip c h x).const_mul _)
  intro y
  change |g (x+y)*Real.exp (c*f (x+y))| ≤ (G:ℝ)*Real.exp (c*f (x+y))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hG _) (Real.exp_nonneg _)

lemma contDiff_semigroup_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    ContDiff ℝ ∞ (semigroup h (fun z => Real.exp (c*f z))) := by
  simpa only [one_mul] using contDiff_semigroup_weight_exp hf hLip (BoundedSmooth.const 1) hc h

lemma contDiff_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) : ContDiff ℝ ∞ (tiltedMean c h f g) := by
  exact (contDiff_semigroup_weight_exp hf hLip hg hc h).div
    (contDiff_semigroup_exp hf hLip hc h) (fun x => ne_of_gt (semigroup_exp_pos hLip c h x))

lemma hasDerivAt_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (tiltedMean c h f g)
      (tiltedMean c h f (fun z => deriv g z+c*g z*deriv f z) x -
        c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) x := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨G₁,hG₁⟩ := hg.deriv.bound
  have hN := hasDerivAt_semigroup_weight_exp (hf.smooth.of_le (by simp)) hLip
    (hg.smooth.of_le (by simp)) hG hG₁ hc h x
  have hD := hasDerivAt_semigroup_exp (hf.smooth.of_le (by simp)) hLip hc h x
  have he : (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) =
      c*semigroup h (fun z => deriv f z*Real.exp (c*f z)) x := by
    unfold semigroup
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [he] at hD
  have hE := ne_of_gt (semigroup_exp_pos hLip c h x)
  change HasDerivAt _ (semigroup h (fun z => (deriv g z+c*g z*deriv f z)*Real.exp (c*f z)) x) x at hN
  have hND := hN.div hD hE
  change HasDerivAt _ (_/semigroup h (fun z => Real.exp (c*f z)) x -
    c*(_/semigroup h (fun z => Real.exp (c*f z)) x)*
      (_/semigroup h (fun z => Real.exp (c*f z)) x)) x
  convert hND using 1 <;> first | rfl | field_simp

lemma deriv_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (tiltedMean c h f g) = fun x =>
      tiltedMean c h f (fun z => deriv g z+c*g z*deriv f z) x -
        c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x := by
  funext x
  exact (hasDerivAt_tiltedMean hf hLip hg hc h x).deriv

lemma iteratedDeriv_mul_bound {f g : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (A B : ℕ → ℝ≥0)
    (hA : ∀ i ≤ n, ∀ x, |iteratedDeriv i f x| ≤ A i)
    (hB : ∀ i ≤ n, ∀ x, |iteratedDeriv i g x| ≤ B i) (x : ℝ) :
    |iteratedDeriv n (fun z => f z*g z) x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*A i*B (n-i) := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (n.choose i:ℝ) from Nat.cast_nonneg _)]
  gcongr
  · exact hA i hi' x
  · exact hB (n-i) (Nat.sub_le _ _) x

lemma boundedSmooth_tiltedMean {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) : BoundedSmooth (tiltedMean c h f g) := by
  classical
  constructor
  · exact contDiff_tiltedMean hf hLip hg hc h
  · have hbounds : ∀ n : ℕ, ∀ g : ℝ → ℝ, BoundedSmooth g →
        ∃ C : ℝ≥0, ∀ x, |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n IH =>
        intro g hg
        cases n with
        | zero =>
          obtain ⟨G,hG⟩ := hg.bound
          refine ⟨G, fun x => ?_⟩
          simpa only [iteratedDeriv_zero] using
            (tiltedMean_bound hLip hg.smooth.continuous.measurable hG c h x)
        | succ m =>
          let q (z : ℝ) := deriv g z+c*g z*deriv f z
          have hq : BoundedSmooth q := weighted_derivative_boundedSmooth hf hg c
          obtain ⟨Cq,hCq⟩ := IH m (by omega) q hq
          have hAg : ∀ i : ℕ, ∃ C : ℝ≥0,
              i ≤ m → ∀ x, |iteratedDeriv i (tiltedMean c h f g) x| ≤ C := by
            intro i
            by_cases hi : i ≤ m
            · obtain ⟨C,hC⟩ := IH i (by omega) g hg
              exact ⟨C, fun _ => hC⟩
            · exact ⟨0, fun hi' => (hi hi').elim⟩
          have hBg : ∀ i : ℕ, ∃ C : ℝ≥0,
              i ≤ m → ∀ x, |iteratedDeriv i (tiltedMean c h f (deriv f)) x| ≤ C := by
            intro i
            by_cases hi : i ≤ m
            · obtain ⟨C,hC⟩ := IH i (by omega) (deriv f) hf.deriv_bounded
              exact ⟨C, fun _ => hC⟩
            · exact ⟨0, fun hi' => (hi hi').elim⟩
          choose A hA using hAg
          choose B hB using hBg
          let Cprod : ℝ≥0 := ∑ i ∈ Finset.range (m+1), (m.choose i:ℝ≥0)*A i*B (m-i)
          refine ⟨Cq+⟨|c|, abs_nonneg c⟩*Cprod, fun x => ?_⟩
          rw [iteratedDeriv_succ', deriv_tiltedMean hf hLip hg hc h]
          have hcg := contDiff_tiltedMean hf hLip hg hc h
          have hcdf := contDiff_tiltedMean hf hLip hf.deriv_bounded hc h
          have hcq := contDiff_tiltedMean hf hLip hq hc h
          have he : (fun x => tiltedMean c h f q x-c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) =
              (fun x => tiltedMean c h f q x-c*(tiltedMean c h f g x*tiltedMean c h f (deriv f) x)) := by
            funext x; ring
          change |iteratedDeriv m (fun x => tiltedMean c h f q x-
            c*tiltedMean c h f g x*tiltedMean c h f (deriv f) x) x| ≤ _
          rw [he, iteratedDeriv_fun_sub (n := m) (hcq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)
            (contDiff_const.mul (hcg.mul hcdf) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt),
            iteratedDeriv_const_mul_field]
          have hp := iteratedDeriv_mul_bound m (hcg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)) (hcdf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
            A B hA hB x
          have hp' : |iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| ≤ Cprod := by
            simpa only [Cprod, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast] using hp
          calc
            _ ≤ |iteratedDeriv m (tiltedMean c h f q) x| +
                |c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| := by
                  have hh := norm_sub_le (iteratedDeriv m (tiltedMean c h f q) x)
                    (c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x)
                  simpa only [Real.norm_eq_abs] using hh
            _ ≤ (Cq:ℝ)+|c| *(Cprod:ℝ) := by rw [abs_mul]; gcongr; exact hCq x
            _ = _ := rfl
    exact fun n => hbounds n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
