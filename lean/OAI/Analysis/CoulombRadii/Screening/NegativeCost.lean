import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace NeutralAtom

lemma negative_center_of_oscillation {v w θ B : ℝ} (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2)
    (hB : 0 ≤ B) (hosc : ‖w-v‖ ≤ θ*(B+max (-v) 0)) :
    max (-v) 0 ≤ 2*max (-w) 0+2*θ*B := by
  have hz := (abs_le.mp (Real.norm_eq_abs (w-v) ▸ hosc)).2
  have hm : max (-v) 0 ≤ max (-w) 0+θ*(B+max (-v) 0) :=
    max_le (by linarith [le_max_left (-w) 0]) (by positivity)
  have hhalf := mul_le_mul_of_nonneg_right hθh (le_max_right (-v) 0)
  nlinarith

theorem negative_center_of_test_mass {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (W σ χ : X → ℝ) (v θ B K m : ℝ)
    (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2) (hB : 0 ≤ B) (hK : 0 ≤ K) (hm : 0 < m)
    (hσ : ∀ᵐ x ∂μ, 0 ≤ σ x) (hχ : ∀ᵐ x ∂μ, 0 ≤ χ x ∧ χ x ≤ K)
    (hi : Integrable (fun x => σ x*χ x) μ)
    (hc : Integrable (fun x => max (-W x) 0*σ x) μ)
    (hmass : m ≤ ∫ x, σ x*χ x ∂μ)
    (hosc : ∀ᵐ x ∂μ, χ x≠0 → ‖W x-v‖ ≤ θ*(B+max (-v) 0)) :
    max (-v) 0 ≤ (2*K/m)*(∫ x, max (-W x) 0*σ x ∂μ)+2*θ*B := by
  let Y := max (-v) 0
  let d := 2*θ*B
  let I := ∫ x, max (-W x) 0*σ x ∂μ
  let q := ∫ x, σ x*χ x ∂μ
  have hI : 0 ≤ I := integral_nonneg_of_ae (hσ.mono fun x hx => mul_nonneg (le_max_right _ _) hx)
  have H : Y*q ≤ 2*K*I+d*q := by
    calc
      Y*q = ∫ x, Y*(σ x*χ x) ∂μ := (integral_const_mul _ _).symm
      _  ≤  ∫ x, (2*K)*(max (-W x) 0*σ x)+d*(σ x*χ x) ∂μ := by
        apply integral_mono_ae (hi.const_mul _) ((hc.const_mul _).add (hi.const_mul _))
        filter_upwards [hσ,hχ,hosc] with x hs hx ho
        change Y*(σ x*χ x) ≤ (2*K)*(max (-W x) 0*σ x)+d*(σ x*χ x)
        by_cases hz : χ x=0
        · simp only [hz,mul_zero,add_zero]
          positivity
        · have hy := negative_center_of_oscillation hθ hθh hB (ho hz)
          have hy' := mul_le_mul_of_nonneg_right hy (mul_nonneg hs hx.1)
          have hk := mul_le_mul_of_nonneg_left hx.2 (mul_nonneg (le_max_right (-W x) 0) hs)
          dsimp only [Y,d]
          nlinarith
      _ = 2*K*I+d*q := by rw [integral_add (hc.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul]
  have hnon : 0 ≤ 2*K*I/m := div_nonneg (by positivity) hm.le
  have H' : Y ≤ 2*K*I/m+d := by
    by_cases hd : Y ≤ d
    · linarith
    · have hl : (Y-d)*m ≤ (Y-d)*q := mul_le_mul_of_nonneg_left hmass (by linarith)
      have hb : Y-d ≤ 2*K*I/m := (le_div_iff₀ hm).mpr (by nlinarith)
      linarith
  dsimp only [Y,d,I] at H'
  simpa only [div_mul_eq_mul_div] using H'

end NeutralAtom
end

end
end

end OAI
