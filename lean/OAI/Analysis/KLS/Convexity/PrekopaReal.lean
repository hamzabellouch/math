import OAI.Analysis.KLS.Convexity.Prekopa

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_integral {n : ℕ} {f g h : Space n → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫ x, f x) ^ t * (∫ y, g y) ^ (1 - t) ≤ ∫ z, h z := by
  have hp := prekopaLeindler_space hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
    ht0 ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

theorem concaveOn_log_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (f : E → Space n → ℝ)
    (hf0 : ∀ u ∈ S, ∀ x, 0 ≤ f u x)
    (hf : ∀ u ∈ S, Measurable (f u))
    (hfi : ∀ u ∈ S, Integrable (f u))
    (hpos : ∀ u ∈ S, 0 < ∫ x, f u x)
    (hjoint : ∀ u ∈ S, ∀ v ∈ S, ∀ x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y)) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, f u x)) := by
  refine ⟨hS, ?_⟩
  intro u hu v hv a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hba : 1 - a = b := by linarith
  have huv : a • u + b • v ∈ S := hS hu hv ha hb hab
  have hp := prekopaLeindler_integral (hf0 u hu) (hf0 v hv) (hf0 _ huv)
    (hf u hu) (hf v hv) (hf _ huv) (hfi u hu) (hfi v hv) (hfi _ huv)
    ha' (by linarith) (by
      intro x y
      simpa only [hba] using hjoint u hu v hv x y a ha' (by linarith))
  rw [hba] at hp
  apply (Real.le_log_iff_exp_le (hpos _ huv)).mpr
  simpa only [smul_eq_mul, Real.rpow_def_of_pos (hpos u hu),
    Real.rpow_def_of_pos (hpos v hv), Real.exp_add, mul_comm] using hp

theorem concaveOn_log_integral_exp_neg {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (F : E × Space n → ℝ)
    (hF : ConvexOn ℝ (S ×ˢ (univ : Set (Space n))) F)
    (hmeas : ∀ u ∈ S, Measurable (fun x => Real.exp (-F (u, x))))
    (hint : ∀ u ∈ S, Integrable (fun x => Real.exp (-F (u, x)))) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, Real.exp (-F (u, x)))) := by
  apply concaveOn_log_integral hS (fun u x => Real.exp (-F (u, x)))
    (fun u hu x => (Real.exp_pos _).le) hmeas hint
  · intro u hu
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (hint u hu)]
    have hs : Function.support (fun x : Space n => Real.exp (-F (u, x))) = univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne volume)
  · intro u hu v hv x y t ht0 ht1
    have hc := hF.2 (x := (u, x)) ⟨hu, mem_univ x⟩ (y := (v, y)) ⟨hv, mem_univ y⟩
      ht0.le (sub_pos.mpr ht1).le (by ring)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, Real.log_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change F (t • u + (1 - t) • v, t • x + (1 - t) • y) ≤
      t * F (u, x) + (1 - t) * F (v, y) at hc
    nlinarith only [hc]

end LeanBlast.KLS

end

end OAI
