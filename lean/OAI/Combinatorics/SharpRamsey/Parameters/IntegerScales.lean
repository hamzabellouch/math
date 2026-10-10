import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceScaleComparisons

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma K_le_Kstar {σ η D : ℝ} (hσ : 1≤σ) (hη : 0<η) (hD : 0≤D) :
    scaleK σ η D≤ scaleKstar σ η D := by
  unfold scaleK scaleKstar
  apply mul_le_mul_of_nonneg_left _ hD
  exact rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη; linarith)

theorem eventually_integer_regime (η : ℝ) (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ,σ^beta η≤D → D≤σ^(1-η/2) →
      log 1024+3*scaleK σ η D+scaleKstar σ η D<σ ∧
      log (200/97)≤ scaleK σ η D ∧
      2*scaleKstar σ η D+2*scaleK σ η D+log 4≤16*scaleKstar σ η D ∧
      0<σ^(-100*beta η) ∧ σ^(-100*beta η)≤1/40000 := by
  have hb:=beta_pos hη
  have hneg : 0<η/2-6*beta η := by unfold beta; linarith
  have ha : Tendsto (fun σ : ℝ=>σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    rw [show -η/2+6*beta η = -(η/2-6*beta η) by ring]
    exact tendsto_rpow_neg_atTop hneg
  have ht : Tendsto (fun σ : ℝ=>log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul (log 1024)).add (ha.const_mul 4)
  have hg : Tendsto (fun σ : ℝ=>σ^(4*beta η)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hτ : Tendsto (fun σ : ℝ=>σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using
      tendsto_rpow_neg_atTop (show 0<100*beta η by positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hg.eventually (eventually_ge_atTop (log (200/97))),
    hτ.eventually (gt_mem_nhds (show (0:ℝ)<1/40000 by norm_num))] with σ hσ hs hg hτ D hDl hDu
  have hσ0 : 0<σ := by linarith
  have hD : 1≤D := (one_le_rpow hσ hb.le).trans hDl
  have hKK:=K_le_Kstar hσ hη (by linarith : 0≤D)
  have hK : σ^(4*beta η)≤ scaleK σ η D := by
    calc
      _ = σ^beta η*σ^(3*beta η) := by rw [←rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDl (by positivity)
  have hKu : scaleKstar σ η D≤σ^(1-η/2+6*beta η) := by
    unfold scaleKstar
    rw [rpow_add hσ0]
    exact mul_le_mul_of_nonneg_right hDu (by positivity)
  have hK1 : 1≤ scaleKstar σ η D :=
    one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ (by positivity))
  refine ⟨?_,hg.trans hK,?_,rpow_pos_of_pos hσ0 _,hτ.le⟩
  · have hh : log 1024+4*σ^(1-η/2+6*beta η)<σ := by
      have he : log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)=
          (log 1024+4*σ^(1-η/2+6*beta η))/σ := by
        have hep : σ^(1-η/2+6*beta η)/σ=σ^(-η/2+6*beta η) := by
          calc
            _ = σ^(1-η/2+6*beta η)/σ^(1:ℝ) := by rw [rpow_one]
            _ = _ := by rw [←rpow_sub hσ0]; congr 1; ring
        rw [rpow_neg_one,add_div,mul_div_assoc,hep]
        ring
      rw [he] at hs
      simpa only [one_mul] using (div_lt_iff₀ hσ0).mp hs
    linarith
  · have hlog : log (4:ℝ)≤3 := by
      have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      linarith
    linarith
end
end SharpLogRamsey.SourceScales

end

end OAI
