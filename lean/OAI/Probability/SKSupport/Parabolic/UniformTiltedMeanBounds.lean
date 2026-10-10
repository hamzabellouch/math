import Mathlib
import OAI.Probability.SKSupport.Parabolic.TiltedMean

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

lemma uniform_tiltedMean_bounds {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∀ n : ℕ, ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x,
      |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
  classical
  have hbounds : ∀ n : ℕ, ∀ g : ℝ → ℝ, BoundedSmooth g →
      ∃ C : ℝ≥0, ∀ h : ℝ≥0, ∀ x, |iteratedDeriv n (tiltedMean c h f g) x| ≤ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IH =>
      intro g hg
      cases n with
      | zero =>
        obtain ⟨G,hG⟩ := hg.bound
        refine ⟨G, fun h x => ?_⟩
        simpa only [iteratedDeriv_zero] using
          (tiltedMean_bound hLip hg.smooth.continuous.measurable hG c h x)
      | succ m =>
        let q (z : ℝ) := deriv g z+c*g z*deriv f z
        have hq : BoundedSmooth q := weighted_derivative_boundedSmooth hf hg c
        obtain ⟨Cq,hCq⟩ := IH m (by omega) q hq
        have hAg : ∀ i : ℕ, ∃ C : ℝ≥0,
            i ≤ m → ∀ h : ℝ≥0, ∀ x, |iteratedDeriv i (tiltedMean c h f g) x| ≤ C := by
          intro i
          by_cases hi : i ≤ m
          · obtain ⟨C,hC⟩ := IH i (by omega) g hg
            exact ⟨C, fun _ => hC⟩
          · exact ⟨0, fun hi' => (hi hi').elim⟩
        have hBg : ∀ i : ℕ, ∃ C : ℝ≥0,
            i ≤ m → ∀ h : ℝ≥0, ∀ x, |iteratedDeriv i (tiltedMean c h f (deriv f)) x| ≤ C := by
          intro i
          by_cases hi : i ≤ m
          · obtain ⟨C,hC⟩ := IH i (by omega) (deriv f) hf.deriv_bounded
            exact ⟨C, fun _ => hC⟩
          · exact ⟨0, fun hi' => (hi hi').elim⟩
        choose A hA using hAg
        choose B hB using hBg
        let Cprod : ℝ≥0 := ∑ i ∈ Finset.range (m+1), (m.choose i:ℝ≥0)*A i*B (m-i)
        refine ⟨Cq+⟨|c|, abs_nonneg c⟩*Cprod, fun h x => ?_⟩
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
          A B (fun i hi => hA i hi h) (fun i hi => hB i hi h) x
        have hp' : |iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| ≤ Cprod := by
          simpa only [Cprod, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast] using hp
        calc
          _ ≤ |iteratedDeriv m (tiltedMean c h f q) x| +
              |c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x| := by
                have hh := norm_sub_le (iteratedDeriv m (tiltedMean c h f q) x)
                  (c*iteratedDeriv m (fun z => tiltedMean c h f g z*tiltedMean c h f (deriv f) z) x)
                simpa only [Real.norm_eq_abs] using hh
          _ ≤ (Cq:ℝ)+|c| *(Cprod:ℝ) := by rw [abs_mul]; gcongr; exact hCq h x
          _ = _ := rfl
  exact fun n => hbounds n g hg

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
