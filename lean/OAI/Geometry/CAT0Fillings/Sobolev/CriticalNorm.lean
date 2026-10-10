import Mathlib

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma lpNorm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    lpNorm f (ENNReal.ofReal p) μ ^ 2 = (∫ x, |f x|^p ∂μ)^(2/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs]
  rw [←Real.rpow_mul_natCast (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) ]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

lemma no_loss {a Λ S t : ℝ} (ha : a ≤ 1) (hΛ : 0 ≤ Λ) (hS : Λ < S)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : Λ*t^a+S*(1-t)^a ≤ Λ) : t = 1 := by
  have ht' := Real.self_le_rpow_of_le_one ht ht1 ha
  have hd' := Real.self_le_rpow_of_le_one (by linarith : 0 ≤ 1-t) (by linarith : 1-t ≤ 1) ha
  have h1 := mul_le_mul_of_nonneg_left ht' hΛ
  have h2 := mul_le_mul_of_nonneg_left hd' (hΛ.trans hS.le)
  nlinarith

lemma concentration_inequality {a Λ S t q : ℝ} (_ : 0 < a) (_ : 0 ≤ t)
    (_ : t ≤ 1) (hS : 0 < S)
    (hQ : Λ*t^a ≤ q)
    (hb : ∀ ε : ℝ, 0 < ε → ε < S → (S-ε)*(1-t)^a ≤ Λ-q) :
    Λ*t^a+S*(1-t)^a ≤ Λ := by
  have hlim : Tendsto (fun ε : ℝ => (S-ε)*(1-t)^a) (𝓝[>] 0)
      (𝓝 (S*(1-t)^a)) := by
    simpa using (((tendsto_const_nhds.sub tendsto_id).mul_const ((1-t)^a)).mono_left inf_le_left :
      Tendsto (fun ε : ℝ => (S-ε)*(1-t)^a) (𝓝[>] 0) (𝓝 ((S-0)*(1-t)^a)))
  have hh : S*(1-t)^a ≤ Λ-q := le_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hS).filter_mono inf_le_left] with ε hε hεS
    exact hb ε hε hεS)
  linarith

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma lpNorm_congr_ae {f g : α → ℝ} (h : f =ᵐ[μ] g) (p : ℝ≥0∞) :
    lpNorm f p μ = lpNorm g p μ := by
  simp only [←toReal_eLpNorm, eLpNorm_congr_ae h]

noncomputable def criticalNorm (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :=
  lpNorm (I u) (ENNReal.ofReal p) μ

noncomputable def criticalMass (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :=
  ∫ x, |(I u) x|^p ∂μ

lemma criticalNorm_nonneg (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :
    0 ≤ criticalNorm I p u := lpNorm_nonneg

lemma criticalMass_nonneg (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :
    0 ≤ criticalMass I p u :=
  integral_nonneg fun point => Real.rpow_nonneg (abs_nonneg ((I u) point)) p

lemma criticalNorm_smul (I : H →L[ℝ] Lp ℝ 2 μ) (p c : ℝ) (u : H) :
    criticalNorm I p (c • u) = |c| *criticalNorm I p u := by
  dsimp [criticalNorm]
  rw [map_smul,lpNorm_congr_ae (Lp.coeFn_smul c (I u)) _,lpNorm_const_smul]
  rfl

lemma criticalNorm_sq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalNorm I p u ^ 2 = criticalMass I p u ^ (2/p) :=
  lpNorm_sq_eq_integral hp (Lp.aestronglyMeasurable _)

lemma criticalMass_eq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalMass I p u = criticalNorm I p u ^ p := by
  dsimp [criticalNorm,criticalMass]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ofReal_ne_top (Lp.aestronglyMeasurable _)]
  simp only [toReal_ofReal hp.le,Real.norm_eq_abs]
  exact (Real.rpow_inv_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) hp.ne').symm

lemma criticalMass_sub (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u v : H) :
    criticalMass I p (u-v) = ∫ x, |(I u) x-(I v) x|^p ∂μ := by
  dsimp [criticalMass]
  rw [map_sub]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (I u) (I v)] with x hx
  rw [hx]
  rfl

lemma criticalMass_integrable (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H)
    (h : MemLp (I u) (ENNReal.ofReal p) μ) : Integrable (fun x => |(I u) x|^p) μ := by
  simpa only [toReal_ofReal hp.le,Real.norm_eq_abs] using h.integrable_norm_rpow (by positivity) ofReal_ne_top

end CAT0Fillings.AnalyticMinimizer
end

end OAI
