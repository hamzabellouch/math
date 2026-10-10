import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionCompatibility
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUniformTail

namespace OAI

/-! The nonlinear outgoing solution is independent of its asymptotic truncation order. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_corrected_orders_difference (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k : ℕ) (hjk : j ≤ k) (v w : ℝ →ᵇ ℂ × ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖(radialPolynomialJet (radialExteriorExpansion ν n m j) t+
          radialExteriorUnweight (2*(j : ℝ)) v t)-
        (radialPolynomialJet (radialExteriorExpansion ν n m k) t+
          radialExteriorUnweight (2*(k : ℝ)) w t)‖ ≤
        C*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨C,hC,hP⟩ := radialExteriorExpansion_jet_difference_decay ν n m j k hjk
  refine ⟨C+‖v‖+‖w‖,by positivity,?_⟩
  intro t ht
  have hE : Real.exp (-(2*(k : ℝ))*t) ≤ Real.exp (-(2*(j : ℝ))*t) := by
    apply Real.exp_le_exp.mpr
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  have he : (radialPolynomialJet (radialExteriorExpansion ν n m j) t+
      radialExteriorUnweight (2*(j : ℝ)) v t)-
      (radialPolynomialJet (radialExteriorExpansion ν n m k) t+
      radialExteriorUnweight (2*(k : ℝ)) w t) =
    (radialPolynomialJet (radialExteriorExpansion ν n m j) t-
      radialPolynomialJet (radialExteriorExpansion ν n m k) t)+
      radialExteriorUnweight (2*(j : ℝ)) v t-
      radialExteriorUnweight (2*(k : ℝ)) w t := by abel
  rw [he]
  calc
    _ ≤ ‖radialPolynomialJet (radialExteriorExpansion ν n m j) t-
        radialPolynomialJet (radialExteriorExpansion ν n m k) t‖+
        ‖radialExteriorUnweight (2*(j : ℝ)) v t‖+
        ‖radialExteriorUnweight (2*(k : ℝ)) w t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C*Real.exp (-(2*(j : ℝ))*t)+
        Real.exp (-(2*(j : ℝ))*t)*‖v‖+
        Real.exp (-(2*(k : ℝ))*t)*‖w‖ := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using hP t ht
        · exact radialExteriorUnweight_norm _ _ v ‖v‖ (v.norm_coe_le_norm t)
      · exact radialExteriorUnweight_norm _ _ w ‖w‖ (w.norm_coe_le_norm t)
    _ ≤ C*Real.exp (-(2*(j : ℝ))*t)+
        Real.exp (-(2*(j : ℝ))*t)*‖v‖+
        Real.exp (-(2*(j : ℝ))*t)*‖w‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
    _ = _ := by ring

theorem radialExterior_ordered_outgoing_unique (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k : ℕ) (hjk : j ≤ k) (v w : ℝ →ᵇ ℂ × ℂ)
    (Z W : ℝ → ℂ × ℂ) (T : ℝ)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
        radialExteriorErrorMatrix ν (Z t)+(0,oddPowerNonlinearity n (Z t).1)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(W t).2)+
        radialExteriorErrorMatrix ν (W t)+(0,oddPowerNonlinearity n (W t).1)) t)
    (heZ : ∀ t, T ≤ t → Z t=radialPolynomialJet (radialExteriorExpansion ν n m j) t+
      radialExteriorUnweight (2*(j : ℝ)) v t)
    (heW : ∀ t, T ≤ t → W t=radialPolynomialJet (radialExteriorExpansion ν n m k) t+
      radialExteriorUnweight (2*(k : ℝ)) w t)
    (hκ : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*‖m‖^(2*n) < 2*(j : ℝ)) :
    ∀ᶠ t in atTop, Z t=W t := by
  have hκ0 : 0 < 2*(j : ℝ) := lt_of_lt_of_le (radialExteriorMatrixBound_pos ν)
    (by have h := pow_nonneg (norm_nonneg m) (2*n); nlinarith)
  have hκk : 0 < 2*(k : ℝ) := by
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have hZlim : Tendsto Z atTop (nhds (m,0)) := by
    have hh : Tendsto (fun t => radialPolynomialJet (radialExteriorExpansion ν n m j) t+
        radialExteriorUnweight (2*(j : ℝ)) v t) atTop (nhds (m,0)) := by
      simpa only [radialExteriorExpansion_constant] using
        radialExterior_corrected_jet_tendsto _ hκ0 (radialExteriorExpansion ν n m j) v
    apply hh.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (heZ t ht).symm
  have hWlim : Tendsto W atTop (nhds (m,0)) := by
    have hh : Tendsto (fun t => radialPolynomialJet (radialExteriorExpansion ν n m k) t+
        radialExteriorUnweight (2*(k : ℝ)) w t) atTop (nhds (m,0)) := by
      simpa only [radialExteriorExpansion_constant] using
        radialExterior_corrected_jet_tendsto _ hκk (radialExteriorExpansion ν n m k) w
    apply hh.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (heW t ht).symm
  have hcont : Continuous (fun ρ : ℝ => radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*ρ^(2*n)) := by
    fun_prop
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp
    (hcont.continuousAt.eventually (gt_mem_nhds hκ))
  let ρ := ‖m‖+ε/2
  have hρm : ‖m‖ < ρ := by dsimp [ρ]; linarith
  have hρ : 0 ≤ ρ := (norm_nonneg m).trans hρm.le
  have hρbound : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*ρ^(2*n) < 2*(j : ℝ) := by
    apply hεbound
    rw [Real.dist_eq]
    dsimp [ρ]
    rw [add_sub_cancel_left,abs_of_pos (by positivity : 0 < ε/2)]
    linarith
  have hZnorm : ∀ᶠ t in atTop, ‖(Z t).1‖ < ρ := by
    have hh := ((continuous_fst.tendsto (m,0)).comp hZlim).norm
    exact hh.eventually (gt_mem_nhds hρm)
  have hWnorm : ∀ᶠ t in atTop, ‖(W t).1‖ < ρ := by
    have hh := ((continuous_fst.tendsto (m,0)).comp hWlim).norm
    exact hh.eventually (gt_mem_nhds hρm)
  obtain ⟨S,hS⟩ := eventually_atTop.mp
    (((eventually_ge_atTop T).and (eventually_ge_atTop (0 : ℝ))).and (hZnorm.and hWnorm))
  obtain ⟨C,_,hdec⟩ := radialExterior_corrected_orders_difference ν n m j k hjk v w
  filter_upwards [eventually_ge_atTop S] with t ht
  apply radialExterior_nonlinear_fast_decay_unique ν n Z W ρ (2*(j : ℝ)) C S hρ
    (fun s hs => hZ s (hS s hs).1.1) (fun s hs => hW s (hS s hs).1.1)
    (fun s hs => (hS s hs).2.1.le) (fun s hs => (hS s hs).2.2.le) ?_ hρbound t ht
  intro s hs
  rw [heZ s (hS s hs).1.1,heW s (hS s hs).1.1]
  exact hdec s (hS s hs).1.2

end DefocusingNLS

end OAI
