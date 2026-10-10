import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

def scaleK (σ η D : ℝ) : ℝ := D*σ^(3*beta η)
def scaleKstar (σ η D : ℝ) : ℝ := D*σ^(6*beta η)

lemma Kstar_eq (σ η D : ℝ) (hσ : 0<σ) :
    scaleKstar σ η D=scaleL σ η D*σ^(-2*beta η) := by
  unfold scaleKstar scaleL
  rw [mul_assoc,←Real.rpow_add hσ]
  congr 2
  ring

lemma R_bound {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0<η)
    (h : Admissible σ η D R) : (R:ℝ) ≤ 4*σ^beta η := by
  have hh := Real.one_le_rpow hσ (beta_pos hη).le
  linarith [h.R_upper]

lemma L_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0<scaleL σ η D := by
  have hD : 0<D := (Real.rpow_pos_of_pos hσ _).trans_le h.D_lower
  unfold scaleL
  positivity

lemma P_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0<scaleP σ η D R := by
  have hR : (0:ℝ)<R := (Real.rpow_pos_of_pos hσ _).trans_le h.R_lower
  exact mul_pos (L_pos hσ h) hR

theorem eventually_sparse_loss {η : ℝ} (hη : 0<η) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      ∀ b τ : ℝ, b ≤ C*scaleKstar σ η D → τ ≤ C*σ^(-100*beta η) →
      b+scaleP σ η D R*τ ≤ δ*scaleL σ η D := by
  have hb := beta_pos hη
  have h1 : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C using 1 <;> simp [neg_mul]
  have h2 : Tendsto (fun σ : ℝ => 4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<99*beta η by positivity)).const_mul (4*C) using 1 <;> simp [neg_mul]
  have ht : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    simpa using h1.add h2
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1:ℝ)] with σ he hσ D R had b τ hb' hτ
  have hσ0 : 0<σ := by linarith
  have hL := (L_pos hσ0 had).le
  have hP := (P_pos hσ0 had).le
  have hR := R_bound hσ hη had
  have hh : (R:ℝ)*(C*σ^(-100*beta η)) ≤ 4*C*σ^(-99*beta η) := by
    calc
      _  ≤  (4*σ^beta η)*(C*σ^(-100*beta η)) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ = _ := by
        rw [show (4*σ^beta η)*(C*σ^(-100*beta η))=4*C*(σ^beta η*σ^(-100*beta η)) by ring,
          ←Real.rpow_add hσ0]
        congr 2
        ring
  have hb'' : b ≤ scaleL σ η D*(C*σ^(-2*beta η)) := by
    rw [Kstar_eq σ η D hσ0] at hb'
    nlinarith only [hb']
  have hτ' : scaleP σ η D R*τ ≤ scaleL σ η D*(4*C*σ^(-99*beta η)) := by
    calc
      _  ≤  scaleP σ η D R*(C*σ^(-100*beta η)) := mul_le_mul_of_nonneg_left hτ hP
      _ = scaleL σ η D*((R:ℝ)*(C*σ^(-100*beta η))) := mul_assoc _ _ _
      _  ≤  _ := mul_le_mul_of_nonneg_left hh hL
  calc
    _  ≤  scaleL σ η D*(C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) := by linarith
    _  ≤  scaleL σ η D*δ := mul_le_mul_of_nonneg_left he.le hL
    _ = _ := mul_comm _ _

theorem eventually_log_le_L {η : ℝ} (hη : 0<η) (C δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      C*Real.log σ ≤ δ*scaleL σ η D := by
  have hb : 0<9*beta η := by have := beta_pos hη; positivity
  have ht : Tendsto (fun σ : ℝ => C*(Real.log σ/σ^(9*beta η))) atTop (𝓝 0) := by
    simpa using ((isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1:ℝ)] with σ hh hσ D R had
  have hp : 0<σ^(9*beta η) := Real.rpow_pos_of_pos (by linarith) _
  have hmul := (div_lt_iff₀ hp).mp (show C*Real.log σ/σ^(9*beta η)<δ by simpa [mul_div_assoc] using hh)
  exact hmul.le.trans (mul_le_mul_of_nonneg_left (scale_bounds hσ hη had).1 hδ.le)

end
end SharpLogRamsey.SourceScales

end

end OAI
