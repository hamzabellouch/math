import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicCDFStability
import OAI.Probability.SKBarriers.Scalar.ScalarGeneralTerminal

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalar_cdf_mass_bound_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β γ n s t f x| ≤
      scalarTimeMassConstantK β K*dyadicCDFDistance α γ n s t := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_zero,dyadicCDFDistance]
    have H := scalarTimeStep_mass_lipschitz_general hf hLip β ht (hγ s) (hα s) x
    exact H.trans_eq (by dsimp [scalarTimeMassConstantK]; ring)
  | succ n ih =>
    rw [dyadicScalar_succ β α n s t f,dyadicScalar_succ β γ n s t f,dyadicCDFDistance]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    let fα := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    let fγ := dyadicScalar β γ n (s+(t:ℝ)/2) (t/2) f
    have hfα : BoundedDerivs fα := dyadicScalar_regular hf β α _ _ _
    have hfγ : BoundedDerivs fγ := dyadicScalar_regular hf β γ _ _ _
    have hlγ : LipschitzWith K fγ := dyadicScalar_lipschitz hf hLip β hγ _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hfα hfγ β hα n s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hfγ hlγ s (t/2) hhalf x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) fα x-dyadicScalar β α n s (t/2) fγ x|+
          |dyadicScalar β α n s (t/2) fγ x-dyadicScalar β γ n s (t/2) fγ x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₂
      _ = _ := by ring

theorem scalarCDFOperator_cdf_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFOperator β α s t f x-scalarCDFOperator β γ s t f x| ≤
      scalarTimeMassConstantK β K*(∫ z in s..s+t, |α z-γ z|) := by
  have H (n : ℕ) := (dyadicScalar_cdf_mass_bound_general hf hLip β hα hγ n s t ht x).trans
    (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hαm hγm n s t)
      (scalarTimeMassConstantK_nonneg β K))
  have hv := ((dyadicScalar_general_uniform hf hLip β hα hαm s t ht).tendsto_at x).sub
    ((dyadicScalar_general_uniform hf hLip β hγ hγm s t ht).tendsto_at x)
  have hzero : Tendsto (fun n : ℕ => (t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := (((hzero.mul_const ((α (s+t)-α s)+(γ (s+t)-γ s))).const_add
    (∫ z in s..s+t, |α z-γ z|)).const_mul (scalarTimeMassConstantK β K))
  have Hlim := le_of_tendsto_of_tendsto hv.abs hr (Eventually.of_forall H)
  simpa only [zero_mul,add_zero] using Hlim

end SK.Analytic

end
end

end OAI
