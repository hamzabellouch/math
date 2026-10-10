import Mathlib

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma separation_inverse_cube {D b : ℝ} (hD : 0 < D) :
    ((b*D^(-(1/3):ℝ))⁻¹)^3=b⁻¹^3*D := by
  have hp : ((D^(-(1/3):ℝ))⁻¹)^3 = D := by
    rw [←Real.rpow_neg hD.le,←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  rw [mul_inv,mul_pow,hp]

lemma boundary_ratio_le {D : ℝ} (hD : 1 ≤ D) :
    D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)  ≤  8*Real.sqrt 2*D^(-(1/4):ℝ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hR : 1 ≤ D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hcube : (1+D^(1/12:ℝ))^3 ≤ 8*D^(1/4:ℝ) := by
    calc
      _  ≤  (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by
        have hp : (D^(1/12:ℝ))^3 = D^(1/4:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hDp.le]
          norm_num
        rw [mul_pow,hp]
        norm_num
  have hs : Real.sqrt (D⁻¹)=D^(-(1/2):ℝ) := by
    rw [Real.sqrt_inv,Real.sqrt_eq_rpow,Real.rpow_neg hDp.le]
  calc
    _ = (1+D^(1/12:ℝ))^3*(D⁻¹/Real.sqrt (D⁻¹))*Real.sqrt 2 := by
      rw [Real.sqrt_div (inv_nonneg.mpr hDp.le)]
      simp only [div_eq_mul_inv,mul_inv,inv_inv]
      ring
    _ = (1+D^(1/12:ℝ))^3*D^(-(1/2):ℝ)*Real.sqrt 2 := by rw [Real.div_sqrt,hs]
    _  ≤  (8*D^(1/4:ℝ))*D^(-(1/2):ℝ)*Real.sqrt 2 := by gcongr
    _ = _ := by
      rw [mul_assoc (8:ℝ),←Real.rpow_add hDp]
      norm_num
      ring

lemma boundary_ratio_tendsto :
    Tendsto (fun D:ℝ  ↦  D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD using boundary_ratio_le hD
  · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).const_mul (8*Real.sqrt 2)

lemma collision_error_majorant {D b A H C t α m : ℝ}
    (hD : 1 ≤ D) (hb : 0 < b) (hA : 0 ≤ A) (hH : 0 ≤ H) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hα : 0 ≤ α) (hαA : α ≤ A) (hm : 0 ≤ m) (hmH : m ≤ H*D) :
    8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+m)+
      8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)  ≤
        8*C*t*A*(b⁻¹^3+H)+64*A*Real.sqrt 2*D^(-(1/4):ℝ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  rw [separation_inverse_cube hDp]
  apply add_le_add
  · calc
      _  ≤  8*C*t*(A/D)*(b⁻¹^3*D+H*D) := by
        have hαD := div_nonneg hα hDp.le
        gcongr
      _ = _ := by field_simp
  · calc
      _  ≤  8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2) := by gcongr
      _ = (8*A)*(D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)) := by ring
      _  ≤  (8*A)*(8*Real.sqrt 2*D^(-(1/4):ℝ)) := mul_le_mul_of_nonneg_left (boundary_ratio_le hD) (by positivity)
      _ = _ := by ring

theorem collision_error_small {b A H C J ε : ℝ}
    (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) (hC : 0 < C) (hJ : 0 < J) (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀  ∧  ∀ t : ℝ, 0 < t  →  t ≤ t₀  →  ∃ D₀ : ℝ, 1 ≤ D₀  ∧
    ∀ D α m : ℝ, D₀ ≤ D  →  0 ≤ α  →  α ≤ A  →  0 ≤ m  →  m ≤ H*D  →
      J*(8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+m)+
        8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))  ≤  ε := by
  let Q := 8*C*A*(b⁻¹^3+H)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨ε/(2*J*Q),by positivity,?_⟩
  intro t ht htt
  have hl : Tendsto (fun D:ℝ  ↦  J*(64*A*Real.sqrt 2*D^(-(1/4):ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).const_mul (64*A*Real.sqrt 2)).const_mul J
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 (hl.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/2)))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro D α m hDD hα hαA hm hmH
  have hD : 1 ≤ D := (le_max_left _ _).trans hDD
  have hd := hD₀ D ((le_max_right _ _).trans hDD)
  have hsmall : J*(8*C*t*A*(b⁻¹^3+H)) ≤ ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*J*Q)).mp htt
    dsimp [Q] at hh
    nlinarith
  have he := mul_le_mul_of_nonneg_left (collision_error_majorant hD hb hA.le hH.le hC.le ht.le hα hαA hm hmH) hJ.le
  nlinarith

end HardSphere.Bridge

end
end

end

end OAI
