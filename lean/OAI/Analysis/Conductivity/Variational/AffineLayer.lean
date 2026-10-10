import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma affine_layer_interval {a b ε : ℝ} (ha : a≠0) (hε : 0≤ε) :
    let l := min b (b+ε/a)
    let r := max b (b+ε/a)
    r-l=ε/|a| ∧
    b-ε/|a|≤l ∧ r≤b+ε/|a| ∧
    (∀ t,t∈Icc l r ↔ a*(t-b)∈Icc 0 ε) ∧
    (∀ t∈Icc l r,|t-b|≤ε/|a|) := by
  dsimp only
  have hc : a*(ε/a)=ε := by field_simp
  rcases lt_or_gt_of_ne ha with hn|hp
  · have hd : ε/a≤0 := div_nonpos_of_nonneg_of_nonpos hε hn.le
    rw [min_eq_right (by linarith : b+ε/a≤b),max_eq_left (by linarith : b+ε/a≤b),abs_of_neg hn,div_neg]
    refine ⟨by ring,by linarith,by linarith,?_,?_⟩
    · intro t
      constructor
      · intro ht
        have h1 := mul_le_mul_of_nonpos_left ht.2 hn.le
        have h2 := mul_le_mul_of_nonpos_left ht.1 hn.le
        constructor <;> nlinarith
      · intro ht
        constructor
        · apply (mul_le_mul_left_of_neg hn).mp
          nlinarith [ht.2]
        · apply (mul_le_mul_left_of_neg hn).mp
          nlinarith [ht.1]
    · intro t ht
      apply abs_le.mpr
      constructor <;> linarith [ht.1,ht.2]
  · have hd : 0≤ε/a := div_nonneg hε hp.le
    rw [min_eq_left (by linarith : b≤b+ε/a),max_eq_right (by linarith : b≤b+ε/a),abs_of_pos hp]
    refine ⟨by ring,by linarith,le_refl _,?_,?_⟩
    · intro t
      constructor
      · intro ht
        have h1 := mul_le_mul_of_nonneg_left ht.1 hp.le
        have h2 := mul_le_mul_of_nonneg_left ht.2 hp.le
        constructor <;> nlinarith
      · intro ht
        constructor
        · apply (mul_le_mul_iff_right₀ hp).mp
          nlinarith [ht.1]
        · apply (mul_le_mul_iff_right₀ hp).mp
          nlinarith [ht.2]
    · intro t ht
      apply abs_le.mpr
      constructor <;> linarith [ht.1,ht.2]

lemma seamLayer_scaled_tendsto_of_cubic_pi {τ u : (Fin 3 → ℝ) → ℝ}
    {δ A : ℝ} (hδ : 0<δ)
    (hbound : ∀ ε,0<ε → ε≤δ → (∫ x in {x | 0<τ x ∧ τ x≤ε},u x^2)≤A*ε^3) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},u x^2) atTop (𝓝 0) := by
  have hn (n : ℕ) : 0<(n:ℝ)+1 := by positivity
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have he : ∀ᶠ n : ℕ in atTop,2/((n:ℝ)+1)≤δ := by
    have hh := ht.const_mul 2
    simp only [mul_zero] at hh
    simpa only [←div_eq_mul_inv] using (hh.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hlim := ht.const_mul (8*A)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _)))) _ hlim
  filter_upwards [he] with n hnδ
  have hs : {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2}={x | 0<τ x ∧ τ x≤2/((n:ℝ)+1)} := by
    ext x
    exact and_congr_right (fun _ => by rw [le_div_iff₀ (hn n),mul_comm])
  rw [hs]
  have hb := mul_le_mul_of_nonneg_left (hbound _ (div_pos (by norm_num) (hn n)) hnδ) (sq_nonneg ((n:ℝ)+1))
  apply hb.trans_eq
  field_simp
  ring

end ScalarConductivity

end

end OAI
