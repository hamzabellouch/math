import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlapConvergence
import OAI.Probability.SKBarriers.Parisi.CDFMetric

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_real_mul_bounded {f g : ℝ → ℝ} {fn gn : ℕ → ℝ → ℝ} {S : Set ℝ}
    (hf : TendstoUniformlyOn fn f atTop S) (hg : TendstoUniformlyOn gn g atTop S)
    (hfn : ∀ n x, x∈S → |fn n x|≤1) {C : ℝ} (hC : 0≤C) (hgb : ∀ x, x∈S → |g x|≤C) :
    TendstoUniformlyOn (fun n x => fn n x*gn n x) (fun x => f x*g x) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε/(2*(C+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have Hf := Metric.tendstoUniformlyOn_iff.mp hf δ hδ
  have Hg := Metric.tendstoUniformlyOn_iff.mp hg δ hδ
  filter_upwards [Hf,Hg] with n hnf hng x hx
  rw [Real.dist_eq,abs_sub_comm]
  have he : fn n x*gn n x-f x*g x=fn n x*(gn n x-g x)+(fn n x-f x)*g x := by ring
  rw [he]
  calc
    _ ≤ |fn n x| * |gn n x-g x|+|fn n x-f x| * |g x| := by simpa only [abs_mul] using abs_add_le (fn n x*(gn n x-g x)) ((fn n x-f x)*g x)
    _ ≤ 1*δ+δ*C := add_le_add
      (mul_le_mul (hfn n x hx) (by simpa only [Real.dist_eq,abs_sub_comm] using (hng x hx).le) (abs_nonneg _) (by norm_num))
      (mul_le_mul (by simpa only [Real.dist_eq,abs_sub_comm] using (hnf x hx).le) (hgb x hx) (abs_nonneg _) hδ.le)
    _ < ε := by dsimp [δ]; field_simp; nlinarith

theorem uniformCDFQuantiles_tendstoUniformlyOn (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) :
    TendstoUniformlyOn (fun n => quantileCDF n (uniformCDFQuantiles n α)) α atTop (Icc (0:ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have H : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  filter_upwards [(tendsto_order.mp H).2 ε hε] with n hn x hx
  rw [Real.dist_eq,abs_sub_comm]
  exact (quantileCDF_uniformCDFQuantiles_error n α ha h1 hx).trans_lt hn

theorem scalarCDFVariation_integrable {β : ℝ} {α γ : ℝ → ℝ}
    (hα : Monotone α) (hγ : Monotone γ)
    (hΓ : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    IntegrableOn (fun s => (γ s-α s)*(scalarCDFOverlap β α s-s)) (Icc (0:ℝ) 1) :=
  ((hγ.monotoneOn _).integrableOn_isCompact isCompact_Icc).sub
    ((hα.monotoneOn _).integrableOn_isCompact isCompact_Icc) |>.mul_continuousOn
      (hΓ.sub continuousOn_id) isCompact_Icc

theorem scalarCDFVariation_quantile_integral_tendsto (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1) :
    Tendsto (fun n => ∫ s in Icc (0:ℝ) 1,
      (quantileCDF n (uniformCDFQuantiles n γ) s-quantileCDF n (uniformCDFQuantiles n α) s)*
        (scalarCDFOverlap β (quantileCDF n (uniformCDFQuantiles n α)) s-s)) atTop
      (𝓝 (∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s))) := by
  have HA := uniformCDFQuantiles_tendstoUniformlyOn α ha hα1
  have HG := uniformCDFQuantiles_tendstoUniformlyOn γ hg hγ1
  have HΓ := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α))
    (uniformCDFQuantiles_L1_tendsto α ha hα1)
  have Hc := scalarCDFOverlap_continuousOn β α ha hα1
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (Hc.sub continuousOn_id)
  apply unitInterval_tendsto_integral_uniform (scalarCDFVariation_integrable α.mono γ.mono Hc)
    (fun n => scalarCDFVariation_integrable (quantileCDF_monotone n _) (quantileCDF_monotone n _)
      (scalarCDFOverlap_continuousOn_quantile β _ (uniformCDFQuantiles_admissible n α hα1)))
  have HId : TendstoUniformlyOn (fun _ : ℕ => fun s : ℝ => s) (fun s => s) atTop (Icc (0:ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  apply uniform_real_mul_bounded (HG.fun_sub HA) (HΓ.fun_sub HId) _
    (C:=|C|) (abs_nonneg C) _
  · intro n x _
    have H₁ := quantileCDF_bounds n (uniformCDFQuantiles n α) x
    have H₂ := quantileCDF_bounds n (uniformCDFQuantiles n γ) x
    exact abs_le.mpr ⟨by linarith [H₁.2,H₂.1],by linarith [H₁.1,H₂.2]⟩
  · intro x hx
    have H : |scalarCDFOverlap β α x-x| ≤ C := by simpa only [Real.norm_eq_abs, Pi.sub_apply, id_eq] using hC x hx
    exact H.trans (le_abs_self C)

end SK.Analytic

end
end

end OAI
