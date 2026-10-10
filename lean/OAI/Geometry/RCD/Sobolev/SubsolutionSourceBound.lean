import OAI.Geometry.RCD.Sobolev.SubsolutionCaccioppoli

namespace OAI

/-! # Controlling the potential term by a lower truncation level -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

theorem upper_level_product_le {j k : ℝ} (hj : 0 ≤ j) (hjk : j < k) (x : ℝ) :
    x*max (x-k) 0 ≤ (k/(k-j))*(max (x-j) 0)^2 := by
  have hd : 0 < k-j := sub_pos.mpr hjk
  have hk : 0 < k := hj.trans_lt hjk
  by_cases hx : x ≤ k
  · rw [max_eq_right (sub_nonpos.mpr hx),mul_zero]
    positivity
  have hkx : k < x := lt_of_not_ge hx
  have hjx : j < x := hjk.trans hkx
  rw [max_eq_left (sub_nonneg.mpr hkx.le),max_eq_left (sub_nonneg.mpr hjx.le)]
  have hxb : x ≤ (k/(k-j))*(x-j) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_nonneg hj (sub_nonneg.mpr hkx.le)]
  calc
    x*(x-k) ≤ x*(x-j) := mul_le_mul_of_nonneg_left (by linarith) (hk.trans hkx).le
    _ ≤ ((k/(k-j))*(x-j))*(x-j) := mul_le_mul_of_nonneg_right hxb (sub_nonneg.mpr hjx.le)
    _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- Raising a nonnegative level decreases its quadratic tail energy. -/
theorem integral_upper_level_mono (u : SobolevSpace μ hQ) {j k : ℝ}
    (hj : 0 ≤ j) (hjk : j ≤ k) (A : Set X) :
    (∫ x in A, (max (SobolevSpace.toLp μ hQ u x-k) 0)^2 ∂μ) ≤
      ∫ x in A, (max (SobolevSpace.toLp μ hQ u x-j) 0)^2 ∂μ := by
  have hi (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun x => (max (SobolevSpace.toLp μ hQ u x-s) 0)^2) μ := by
    apply (Lp.memLp (SobolevSpace.toLp μ hQ (u.upperPositivePart μ hQ hs))).integrable_sq.congr
    filter_upwards [u.upperPositivePart_coe μ hQ hs] with x hx
    rw [hx]
    rfl
  apply integral_mono_ae (hi k (hj.trans hjk)).integrableOn (hi j hj).integrableOn
  apply Filter.Eventually.of_forall
  intro x
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 2

omit [ProperSpace X] in
/-- Moving the cutoff test strictly above an earlier level absorbs the
zeroth-order term into that earlier level's L² energy. -/
theorem cutoff_upper_level_source_le
    (u : SobolevSpace μ hQ) {j k : ℝ} (hj : 0 ≤ j) (hjk : j < k)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {A : Set X} (hs : tsupport χ ⊆ A) :
    (∫ x, (χ x)^2*SobolevSpace.toLp μ hQ u x*
      max (SobolevSpace.toLp μ hQ u x-k) 0 ∂μ) ≤
      (k/(k-j))*(∫ x in A, (max (SobolevSpace.toLp μ hQ u x-j) 0)^2 ∂μ) := by
  let U := SobolevSpace.toLp μ hQ u
  have hk : 0 ≤ k := hj.trans hjk.le
  let V := SobolevSpace.toLp μ hQ (u.upperPositivePart μ hQ hk)
  have hV : V =ᵐ[μ] fun x => max (U x-k) 0 := u.upperPositivePart_coe μ hQ hk
  have hiUV : Integrable (fun x => U x*max (U x-k) 0) μ := by
    apply ((Lp.memLp U).integrable_mul (Lp.memLp V)).congr
    filter_upwards [hV] with x hx
    simp only [Pi.mul_apply,hx]
  have hi : Integrable (fun x => (χ x)^2*U x*max (U x-k) 0) μ := by
    have hh : Integrable (fun x => (χ x)^2*(U x*max (U x-k) 0)) μ :=
      hiUV.bdd_mul (c := (1:ℝ)) (hχ.continuous.aestronglyMeasurable.pow 2)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
          nlinarith [(hb x).1,(hb x).2])
    exact hh.congr (Filter.Eventually.of_forall fun x => by ring)
  have hiJ : Integrable (fun x => (max (U x-j) 0)^2) μ := by
    apply (Lp.memLp (SobolevSpace.toLp μ hQ (u.upperPositivePart μ hQ hj))).integrable_sq.congr
    filter_upwards [u.upperPositivePart_coe μ hQ hj] with x hx
    rw [hx]
    rfl
  have heq : (∫ x, (χ x)^2*U x*max (U x-k) 0 ∂μ) =
      ∫ x in A, (χ x)^2*U x*max (U x-k) 0 ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : χ x = 0 := by
      by_contra hn
      exact hx (hs (subset_tsupport χ hn))
    simp only [hzero,zero_pow (by decide : 2 ≠ 0),zero_mul]
  rw [heq,← integral_const_mul]
  apply integral_mono_ae hi.integrableOn (hiJ.const_mul _).integrableOn
  apply Filter.Eventually.of_forall
  intro x
  have hprod : 0 ≤ U x*max (U x-k) 0 := by
    by_cases hx : U x ≤ k
    · rw [max_eq_right (sub_nonpos.mpr hx),mul_zero]
    · exact mul_nonneg (hk.trans (le_of_not_ge hx)) (le_max_right _ _)
  calc
    _ = (χ x)^2*(U x*max (U x-k) 0) := by ring
    _ ≤ 1*(U x*max (U x-k) 0) := mul_le_mul_of_nonneg_right (by nlinarith [(hb x).1,(hb x).2]) hprod
    _ ≤ _ := by simpa only [one_mul] using upper_level_product_le hj hjk (U x)

end RegularPointCoordinates

end

end OAI
