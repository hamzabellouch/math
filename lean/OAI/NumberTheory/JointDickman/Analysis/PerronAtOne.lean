import OAI.NumberTheory.JointDickman.Analysis.RieszDenominatorBounds
import PrimeNumberTheoremAnd.PerronFormula
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

/-! # The endpoint of the triangular Perron kernel -/
namespace JointDickman
open Complex Filter MeasureTheory Set
open scoped Topology

theorem perron_integral_continuousAt_one {σ : ℝ} (hσ : 1 < σ) :
    ContinuousAt (fun x : ℝ => VerticalIntegral' (Perron.f x) σ) 1 := by
  let B : ℝ → ℝ := fun t => 5*(2:ℝ)^σ/(1+t^2)
  have hi : Integrable B := by
    simpa only [B,div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (5*(2:ℝ)^σ)
  have hnear : Ioo (0:ℝ) 2 ∈ 𝓝 (1:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hc : ContinuousAt (fun x : ℝ => ∫ t : ℝ, Perron.f x ((σ:ℂ)+(t:ℂ)*I)) 1 := by
    apply continuousAt_of_dominated
    · filter_upwards [hnear] with x hx
      exact (Perron.isIntegrable hx.1 (by linarith) (by linarith)).aestronglyMeasurable
    · filter_upwards [hnear] with x hx
      filter_upwards with t
      have hs : 1/2 ≤ ((σ:ℂ)+(t:ℂ)*I).re := by simp; linarith
      have hd := rieszDenominator_inv_bound hs
      have hb : x^σ ≤ (2:ℝ)^σ := Real.rpow_le_rpow hx.1.le hx.2.le (by linarith)
      change ‖(x:ℂ)^((σ:ℂ)+(t:ℂ)*I) /
        (((σ:ℂ)+(t:ℂ)*I)*((σ:ℂ)+(t:ℂ)*I+1))‖ ≤ _
      rw [norm_div,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero] at *
      have hd' : 1/(‖(σ:ℂ)+(t:ℂ)*I‖*‖(σ:ℂ)+(t:ℂ)*I+1‖) ≤ 5/(1+t^2) := by
        simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
          zero_add,add_zero] using hd
      calc
        _ = x^σ*(1/(‖(σ:ℂ)+(t:ℂ)*I‖*‖(σ:ℂ)+(t:ℂ)*I+1‖)) := by ring
        _ ≤ (2:ℝ)^σ*(5/(1+t^2)) :=
          mul_le_mul hb hd' (by positivity) (by positivity)
        _ = B t := by dsimp [B]; ring
    · exact hi
    · filter_upwards with t
      unfold Perron.f
      apply ContinuousAt.div_const
      exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (by simpa only [ofReal_one] using one_mem_slitPlane)
  simpa only [VerticalIntegral',VerticalIntegral,smul_eq_mul,mul_assoc] using
    hc.const_mul ((1/(2*(Real.pi:ℂ)*I))*I)

theorem perron_formula_one {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegral' (Perron.f 1) σ = 0 := by
  have hcont := (perron_integral_continuousAt_one hσ).continuousWithinAt (s := Ioi (1:ℝ))
  have hright : (fun x : ℝ => VerticalIntegral' (Perron.f x) σ) =ᶠ[𝓝[>] 1]
      (fun x => 1-1/(x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Perron.formulaGtOne hx (by linarith)
  have hlim : Tendsto (fun x : ℝ => (1:ℂ)-1/(x:ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => (1:ℂ)-1/(x:ℂ)) 1 := by
      apply ContinuousAt.sub continuousAt_const
      exact continuousAt_const.div Complex.continuous_ofReal.continuousAt (by norm_num)
    simpa only [ofReal_one,div_one,sub_self] using h.continuousWithinAt.tendsto (s := Ioi (1:ℝ))
  exact tendsto_nhds_unique hcont (hlim.congr' hright.symm)

end JointDickman

end OAI
