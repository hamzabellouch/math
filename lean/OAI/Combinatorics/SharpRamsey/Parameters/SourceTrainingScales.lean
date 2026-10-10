import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourcePencilScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_training_loss {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        b+2*scaleP σ η D R*τ≤δ*scaleL σ η D := by
  filter_upwards [eventually_sparse_loss hη (2*C) δ (by positivity) hδ,
    eventually_ge_atTop (1:ℝ)] with σ hh hσ D R had b τ hb hτ
  have hK : 0 ≤ scaleKstar σ η D := by
    rw [Kstar_eq _ _ _ (by linarith)]
    exact mul_nonneg (L_pos (by linarith) had).le (Real.rpow_nonneg (by linarith) _)
  have h1 : b≤(2*C)*scaleKstar σ η D := by nlinarith
  have h2 : 2*τ≤(2*C)*σ^(-100*beta η) := by linarith
  have hh' := hh D R had b (2*τ) h1 h2
  nlinarith only [hh']

theorem eventually_exceptional_training {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        50000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
          Real.exp (-b-2*scaleP σ η D R*τ)/800 := by
  have he : ∀ᶠ L : ℝ in atTop,(40000000:ℝ)≤Real.exp (L/2) := by
    filter_upwards [eventually_ge_atTop (80000000:ℝ)] with L hL
    have hh := Real.add_one_le_exp (L/2)
    linarith
  filter_upwards [eventually_training_loss hη C (1/100) hC (by norm_num),
    eventually_uniform_L hη he,eventually_ge_atTop (1:ℝ)] with σ hl he hσ D R had b τ hb hτ
  have hL := (L_pos (by linarith) had).le
  have hl' := hl D R had b τ hb hτ
  have he' := he D R had
  have hh : 40000000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
      Real.exp (-b-2*scaleP σ η D R*τ) := by
    calc
      _ ≤ Real.exp (scaleL σ η D/2)*Real.exp (-(95/100:ℝ)*scaleL σ η D) :=
        mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
      _ = Real.exp (scaleL σ η D/2-(95/100:ℝ)*scaleL σ η D) := by
        rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma exceptional_below_threshold {B q T z L P b τ : ℝ}
    (hB : 0≤B) (hq : 0<q)
    (hT : q*B*Real.exp (-b)/2≤T)
    (hz : T*Real.exp (-2*P*τ)/4≤z)
    (he : 50000*Real.exp (-(95/100:ℝ)*L)≤Real.exp (-b-2*P*τ)/800) :
    50000*B*Real.exp (-(95/100:ℝ)*L)≤z/(100*q) := by
  have hprod : q*B*Real.exp (-b-2*P*τ)/8≤z := by
    have hh := mul_le_mul_of_nonneg_right hT (Real.exp_pos (-2*P*τ)).le
    have ee : Real.exp (-b-2*P*τ)=Real.exp (-b)*Real.exp (-2*P*τ) := by
      rw [←Real.exp_add]; congr 1; ring
    rw [ee]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he hB
  apply (le_div_iff₀ (by positivity : 0<100*q)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm hq.le]

end
end SharpLogRamsey.SourceScales

end

end OAI
