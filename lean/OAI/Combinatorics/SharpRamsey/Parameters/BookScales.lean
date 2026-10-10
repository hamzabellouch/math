import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.UniformBook

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma Kstar_ge_one {σ η D : ℝ} {R : ℕ} (hσ : 1≤σ) (hη : 0<η)
    (had : Admissible σ η D R) : 1≤ scaleKstar σ η D := by
  apply one_le_mul_of_one_le_of_one_le
  · exact (one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  · exact one_le_rpow hσ (by have := beta_pos hη; positivity)

lemma P_ge_Kstar {σ η D : ℝ} {R : ℕ} (hσ : 0<σ)
    (had : Admissible σ η D R) :
    scaleKstar σ η D*σ^(3*beta η)≤ scaleP σ η D R := by
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le had.D_lower
  calc
    _ = scaleL σ η D*σ^beta η := by
      unfold scaleKstar scaleL
      rw [mul_assoc,mul_assoc,←rpow_add hσ,←rpow_add hσ]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left had.R_lower (by unfold scaleL; positivity)

theorem eventually_book_scales {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      0≤16*scaleKstar σ η D ∧ 4≤ scaleP σ η D R ∧
      16*scaleKstar σ η D+log 1000000≤ scaleP σ η D R ∧
      0<σ^(-100*beta η) ∧ σ^(-100*beta η)≤1/40000 := by
  have hb:=beta_pos hη
  have ht : Tendsto (fun σ : ℝ=>σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<100*beta η by positivity)
  filter_upwards [(tendsto_rpow_atTop (show 0<3*beta η by positivity)).eventually_ge_atTop
      (16+log 1000000),ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/40000)),
      eventually_ge_atTop (1:ℝ)] with σ hpow hτ hσ D R had
  have hσ0 : 0<σ:=by linarith
  have hK:=Kstar_ge_one hσ hη had
  have hlo:=P_ge_Kstar hσ0 had
  have hlog : 0≤log (1000000:ℝ):=log_nonneg (by norm_num)
  have hKP : 16*scaleKstar σ η D+log 1000000≤ scaleP σ η D R := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (by linarith : 0≤ scaleKstar σ η D),
      mul_le_mul_of_nonneg_left hK hlog]
  exact ⟨by positivity,by linarith,hKP,rpow_pos_of_pos hσ0 _,hτ⟩
end
end SharpLogRamsey.SourceScales

end

end OAI
