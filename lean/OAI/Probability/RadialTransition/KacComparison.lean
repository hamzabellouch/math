import OAI.Probability.RadialTransition.KacPressure

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_row_mono_mass {t a : ℝ} {b : ℕ → ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8 := by
  have hc : 0 ≤ 2197*t*bumpIntegral⁻¹ := by have := bumpIntegral_pos; positivity
  exact (mul_le_mul_of_nonneg_left (by linarith : (∑' n, b n) ≤ a+∑' n, b n) hc).trans hrow

lemma family_grand_prepend_limit {t β a R : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) (h : ℝ) :
    Tendsto (fun L : ℝ => finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t L β h) atTop
      (nhds (grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h)) := by
  have hba := prepend_nonneg ha hb
  have hRS := prepend_range hR hS
  have hsum := summable_prepend a hs
  have hrow' : 2197*t*bumpIntegral⁻¹*(∑' n, prepend a b n) ≤ (t^2/8)/8 := by rw [tsum_prepend _ hs]; exact hrow
  exact (grandPressure_spec (continuous_familyPotential hba hRS hsum t)
    (bounded_familyPotential hba hRS hsum t)
    (stable_family_of_master (by linarith) hba hRS hsum hsum (fun _ => le_rfl) hrow')
    (by linarith) hβ (fun _ hr => familyPotential_nonpos_outer hba hRS ht hr) h).1

lemma family_kac_lower_limit {q : ℕ} (hq : 0 < q) {t β h R₀ a R D u : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hD : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure (familyPotential t b S) t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h+
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)+
      β*a/2*kernelRowError q R*D^2+Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  have ht0 : 0 < t := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR1 : 1 ≤ R := hq1.trans hR
  have hrowb := family_row_mono_mass ht0.le ha hrow
  have hstable := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrowb
  have hl := (family_grand_prepend_limit ht hβ.le ha hR1 hb hS hs hrow h).comp
    ((tendsto_natCast_atTop_atTop.atTop_mul_const hq0).atTop_div_const (by norm_num : (0:ℝ) < 4))
  have hf : Tendsto (fun m : ℕ => ((kernelInterior m q R).card:ℝ)/(m:ℝ)^3) atTop (nhds 1) :=
    kernelInterior_ratio (cellMargin (R/q+1)).toNat
  have he := ((((tendsto_const_nhds (x := (1:ℝ))).sub (hf.mul_const (1-kernelRowError q R))).const_mul (β*a/2)).mul_const (D^2))
  have htt := (((hl.add_const (boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4))).add he).add_const
    (Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3)))
  simp only [one_mul, sub_sub_cancel] at htt
  apply ge_of_tendsto htt
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hd := (abs_le.mp (family_kac_deletion (h := h) hm hq ht hβ ha hR1 hb hS hs hR₀ hrange hrow)).1
  have hk := deletedKacPressure_branch_lower (continuous_familyPotential hb hS hs t)
    (bounded_familyPotential hb hS hs t) hm hq hstable ht0 hq1 hβ.le hR ha hks hD
  dsimp only [Function.comp_def]
  linarith

lemma family_kac_upper_limit {q : ℕ} (hq : 0 < q) {t β h R₀ a R P : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hP : Real.log (∑' n, kacSeries (familyPotential t b S) q R t a β h n)/(t*((q:ℝ)/4)^3) ≤ P) :
    grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h ≤
      P+boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  have ht0 : 0 < t := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR1 : 1 ≤ R := hq1.trans hR
  have hl := (family_grand_prepend_limit ht hβ.le ha hR1 hb hS hs hrow h).comp
    ((tendsto_natCast_atTop_atTop.atTop_mul_const hq0).atTop_div_const (by norm_num : (0:ℝ) < 4))
  apply le_of_tendsto hl
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hd := (abs_le.mp (family_kac_deletion (h := h) hm hq ht hβ ha hR1 hb hS hs hR₀ hrange hrow)).2
  have hk := deletedKacPressure_upper (continuous_familyPotential hb hS hs t)
    (bounded_familyPotential hb hS hs t) hm hq ht0 hβ.le hR ha hks
  dsimp only [Function.comp_def]
  linarith

end RadialTransition
end

end OAI
