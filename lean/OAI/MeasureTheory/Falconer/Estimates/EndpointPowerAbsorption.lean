import OAI.MeasureTheory.Falconer.Estimates.EndpointCountBudget

namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

theorem eventually_endpoint_selection_powers {u τ c₁ c₂ : ℝ}
    (hu : 0 < u) (hτ : 30*u < τ) (hc₁ : τ+10*u < c₁) (hc₂ : τ+10*u < c₂)
    (V C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      12*δ^(τ-6*u) < δ^(24*u) ∧
      2*δ^(40*u) < δ^(36*u) ∧
      C*δ^(-6*u) < δ^(-40*u) ∧
      V*δ^(2*u) < δ^u/4 ∧
      V*δ^(c₁-τ-9*u) < δ^u/4 ∧ V*δ^(c₂-τ-9*u) < δ^u/4 := by
  have hbad := eventually_const_mul_rpow_lt (show 24*u < τ-6*u by linarith) 12
  have hmass := eventually_const_mul_rpow_lt (show 36*u < 40*u by linarith) 2
  have hcoef := eventually_const_mul_rpow_lt (show -40*u < -6*u by linarith) C
  have hbase := eventually_const_mul_rpow_lt (show u < 2*u by linarith) (4*V)
  have hpair := eventually_const_mul_rpow_lt (show u < c₁-τ-9*u by linarith) (4*V)
  have htriple := eventually_const_mul_rpow_lt (show u < c₂-τ-9*u by linarith) (4*V)
  filter_upwards [hbad,hmass,hcoef,hbase,hpair,htriple] with δ hb hm hC hB hP hT
  exact ⟨hb.1,hb.2,hm.2,hC.2,by linarith [hB.2],by linarith [hP.2],by linarith [hT.2]⟩

end Falconer

end OAI
