import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

noncomputable def genusOneFactor (ρ z : ℂ) : ℂ :=
  (1 - z / ρ) * Complex.exp (z / ρ)

theorem differentiable_genusOneFactor (ρ : ℂ) :
    Differentiable ℂ (genusOneFactor ρ) := by
  unfold genusOneFactor
  fun_prop

theorem genusOneFactor_ne_zero {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    genusOneFactor ρ z ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  intro h
  apply hz
  exact (div_eq_one_iff_eq hρ).mp (sub_eq_zero.mp h).symm

theorem logDeriv_genusOneFactor {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    logDeriv (genusOneFactor ρ) z = (z - ρ)⁻¹ + ρ⁻¹ := by
  have hd₁ : HasDerivAt (fun w : ℂ => 1 - w / ρ) (-1 / ρ) z := by
    convert (hasDerivAt_const z (1 : ℂ)).fun_sub ((hasDerivAt_id z).div_const ρ) using 1 <;>
      simp [div_eq_mul_inv]
  have hd₂ : HasDerivAt (fun w : ℂ => Complex.exp (w / ρ))
      (Complex.exp (z / ρ) * (1 / ρ)) z := by
    simpa only [id_eq] using ((hasDerivAt_id z).div_const ρ).cexp
  have hlin : 1 - z / ρ ≠ 0 := by
    intro h
    apply hz
    exact (div_eq_one_iff_eq hρ).mp (sub_eq_zero.mp h).symm
  unfold genusOneFactor
  rw [logDeriv_fun_mul (f := fun w : ℂ => 1 - w / ρ)
    (g := fun w : ℂ => Complex.exp (w / ρ)) z hlin (Complex.exp_ne_zero (z / ρ))
    hd₁.differentiableAt hd₂.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, hd₁.deriv, hd₂.deriv]
  field_simp [hρ, hlin, sub_ne_zero.mpr hz, Complex.exp_ne_zero]
  ring

noncomputable def zeroFactor (f : ℂ → ℂ) (ρ z : ℂ) : ℂ :=
  genusOneFactor ρ z ^ analyticOrderNatAt f ρ

theorem differentiable_zeroFactor (f : ℂ → ℂ) (ρ : ℂ) :
    Differentiable ℂ (zeroFactor f ρ) :=
  (differentiable_genusOneFactor ρ).pow _

theorem zeroFactor_ne_zero (f : ℂ → ℂ) {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    zeroFactor f ρ z ≠ 0 :=
  pow_ne_zero _ (genusOneFactor_ne_zero hρ hz)

theorem logDeriv_zeroFactor (f : ℂ → ℂ) {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    logDeriv (zeroFactor f ρ) z =
      (analyticOrderNatAt f ρ : ℂ) * ((z - ρ)⁻¹ + ρ⁻¹) := by
  unfold zeroFactor
  rw [logDeriv_fun_pow (differentiable_genusOneFactor ρ z), logDeriv_genusOneFactor hρ hz]

def NonzeroZero (f : ℂ → ℂ) := {ρ : ℂ // f ρ = 0 ∧ ρ ≠ 0}

theorem logDeriv_canonicalProduct (f : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hzU : z ∈ U) (hfz : f z ≠ 0)
    (hsum : Summable (fun ρ : NonzeroZero f =>
      (analyticOrderNatAt f ρ.val : ℂ) * ((z - ρ.val)⁻¹ + ρ.val⁻¹)))
    (hprod : MultipliableLocallyUniformlyOn
      (fun ρ : NonzeroZero f => zeroFactor f ρ.val) U)
    (hprod_ne : (∏' ρ : NonzeroZero f, zeroFactor f ρ.val z) ≠ 0) :
    logDeriv (fun w => ∏' ρ : NonzeroZero f, zeroFactor f ρ.val w) z =
      ∑' ρ : NonzeroZero f,
        (analyticOrderNatAt f ρ.val : ℂ) * ((z - ρ.val)⁻¹ + ρ.val⁻¹) := by
  have hzρ : ∀ ρ : NonzeroZero f, z ≠ ρ.val := by
    intro ρ h
    apply hfz
    rw [h]
    exact ρ.property.1
  have hid : (fun ρ : NonzeroZero f => logDeriv (zeroFactor f ρ.val) z) =
      (fun ρ : NonzeroZero f =>
        (analyticOrderNatAt f ρ.val : ℂ) * ((z - ρ.val)⁻¹ + ρ.val⁻¹)) := by
    funext ρ
    exact logDeriv_zeroFactor f ρ.property.2 (hzρ ρ)
  rw [← hid]
  apply logDeriv_tprod_eq_tsum hU hzU
  · intro ρ
    exact zeroFactor_ne_zero f ρ.property.2 (hzρ ρ)
  · intro ρ
    exact (differentiable_zeroFactor f ρ.val).differentiableOn
  · rwa [hid]
  · exact hprod
  · exact hprod_ne

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.W03

theorem regularized_reciprocal_eq {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    (z - ρ)⁻¹ + ρ⁻¹ = z / ((z - ρ) * ρ) := by
  field_simp [hρ, sub_ne_zero.mpr hz]
  ring

theorem norm_regularized_reciprocal_le {ρ z : ℂ}
    (hρ : ρ ≠ 0) (hz : z ≠ ρ) (hfar : 2 * ‖z‖ ≤ ‖ρ‖) :
    ‖(z - ρ)⁻¹ + ρ⁻¹‖ ≤ 2 * ‖z‖ / ‖ρ‖ ^ 2 := by
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hdist : ‖ρ‖ / 2 ≤ ‖z - ρ‖ := by
    have hn := norm_sub_norm_le ρ z
    rw [norm_sub_rev ρ z] at hn
    linarith
  have hden : ‖ρ‖ ^ 2 / 2 ≤ ‖z - ρ‖ * ‖ρ‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hdist hρpos.le]
  rw [regularized_reciprocal_eq hρ hz, norm_div, norm_mul]
  calc
    ‖z‖ / (‖z - ρ‖ * ‖ρ‖) ≤ ‖z‖ / (‖ρ‖ ^ 2 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) hden
    _ = 2 * ‖z‖ / ‖ρ‖ ^ 2 := by ring

theorem summable_regularized_actual_zeros (f : ℂ → ℂ) {z : ℂ} (hfz : f z ≠ 0)
    (hsquare : Summable (fun ρ : NonzeroZero f =>
      (analyticOrderNatAt f ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hfar : ∀ᶠ ρ : NonzeroZero f in Filter.cofinite, 2 * ‖z‖ ≤ ‖ρ.val‖) :
    Summable (fun ρ : NonzeroZero f =>
      (analyticOrderNatAt f ρ.val : ℂ) * ((z - ρ.val)⁻¹ + ρ.val⁻¹)) := by
  apply (hsquare.mul_left (2 * ‖z‖)).of_norm_bounded_eventually
  filter_upwards [hfar] with ρ hρfar
  have hzρ : z ≠ ρ.val := by
    intro h
    apply hfz
    rw [h]
    exact ρ.property.1
  have hbound := mul_le_mul_of_nonneg_left
    (norm_regularized_reciprocal_le ρ.property.2 hzρ hρfar)
    (show 0 ≤ (analyticOrderNatAt f ρ.val : ℝ) by positivity)
  simpa only [norm_mul, Complex.norm_natCast] using hbound.trans_eq (by ring)

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.W03

theorem norm_primaryFactor_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖(1 - x) * Complex.exp x - 1‖ ≤ 3 * ‖x‖ ^ 2 := by
  calc
    ‖(1 - x) * Complex.exp x - 1‖ =
        ‖(Complex.exp x - 1 - x) - x * (Complex.exp x - 1)‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.exp x - 1 - x‖ + ‖x * (Complex.exp x - 1)‖ := norm_sub_le _ _
    _ ≤ ‖x‖ ^ 2 + ‖x‖ * (2 * ‖x‖) := by
      rw [norm_mul]
      exact add_le_add (Complex.norm_exp_sub_one_sub_id_le hx)
        (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le hx) (norm_nonneg x))
    _ = _ := by ring

theorem norm_genusOneFactor_sub_one_le {ρ z : ℂ} {R : ℝ}
    (_hR : 0 ≤ R) (hρ : ρ ≠ 0) (hz : ‖z‖ ≤ R) (hfar : R ≤ ‖ρ‖) :
    ‖genusOneFactor ρ z - 1‖ ≤ (3 * R ^ 2) * (1 / ‖ρ‖ ^ 2) := by
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hquot : ‖z / ρ‖ ≤ 1 := by
    rw [norm_div, div_le_one hρpos]
    exact hz.trans hfar
  calc
    ‖genusOneFactor ρ z - 1‖ ≤ 3 * ‖z / ρ‖ ^ 2 := norm_primaryFactor_sub_one_le hquot
    _ ≤ 3 * (R / ‖ρ‖) ^ 2 := by
      rw [norm_div]
      gcongr
    _ = _ := by ring

theorem multipliableLocallyUniformlyOn_genusOne {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    {R : ℝ} (hR : 0 < R)
    (hfar : ∀ᶠ i in Filter.cofinite, R ≤ ‖ρ i‖) :
    MultipliableLocallyUniformlyOn (fun i => genusOneFactor (ρ i)) (Metric.ball 0 R) := by
  have hmajorant := hsquare.mul_left (3 * R ^ 2)
  have hbound : ∀ᶠ i in Filter.cofinite,
      ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖genusOneFactor (ρ i) z - 1‖ ≤ (3 * R ^ 2) * (1 / ‖ρ i‖ ^ 2) := by
    filter_upwards [hfar] with i hi z hz
    apply norm_genusOneFactor_sub_one_le hR.le (hρ i) _ hi
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hcts : ∀ i, ContinuousOn (fun z => genusOneFactor (ρ i) z - 1) (Metric.ball 0 R) := by
    intro i
    exact ((differentiable_genusOneFactor (ρ i)).continuous.sub continuous_const).continuousOn
  simpa using
    Summable.multipliableLocallyUniformlyOn_one_add Metric.isOpen_ball hmajorant hbound hcts

theorem summable_norm_genusOneFactor_sub_one {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    {z : ℂ} (hfar : ∀ᶠ i in Filter.cofinite, ‖z‖ ≤ ‖ρ i‖) :
    Summable (fun i => ‖genusOneFactor (ρ i) z - 1‖) := by
  apply (hsquare.mul_left (3 * ‖z‖ ^ 2)).of_norm_bounded_eventually
  filter_upwards [hfar] with i hi
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_genusOneFactor_sub_one_le (norm_nonneg z) (hρ i) le_rfl hi

theorem genusOneProduct_ne_zero {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    {z : ℂ} (hz : ∀ i, z ≠ ρ i)
    (hfar : ∀ᶠ i in Filter.cofinite, ‖z‖ ≤ ‖ρ i‖) :
    (∏' i, genusOneFactor (ρ i) z) ≠ 0 := by
  have hn : ∀ i, 1 + (genusOneFactor (ρ i) z - 1) ≠ 0 := by
    intro i
    simpa using genusOneFactor_ne_zero (hρ i) (hz i)
  simpa using tprod_one_add_ne_zero_of_summable hn
    (summable_norm_genusOneFactor_sub_one ρ hρ hsquare hfar)

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.W03

theorem reciprocal_re_bounds {ρ : ℂ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1) :
    0 ≤ (ρ⁻¹).re ∧ (ρ⁻¹).re ≤ 1 / ‖ρ‖ ^ 2 := by
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  exact ⟨div_nonneg hlo (sq_nonneg _),
    div_le_div_of_nonneg_right hhi (sq_nonneg _)⟩

theorem summable_reciprocal_re {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2)) :
    Summable (fun i => ((ρ i)⁻¹).re) :=
  hsquare.of_nonneg_of_le
    (fun i => (reciprocal_re_bounds (hstrip i).1 (hstrip i).2).1)
    (fun i => (reciprocal_re_bounds (hstrip i).1 (hstrip i).2).2)

theorem summable_real_zero_contributions {ι : Type*} (ρ : ι → ℂ) (z : ℂ)
    (hreg : Summable (fun i => (z - ρ i)⁻¹ + (ρ i)⁻¹))
    (hinv : Summable (fun i => ((ρ i)⁻¹).re)) :
    Summable (fun i => ((z - ρ i)⁻¹).re) := by
  have hreal : Summable (fun i => ((z - ρ i)⁻¹ + (ρ i)⁻¹).re) :=
    Complex.reCLM.summable hreg
  simpa only [Complex.add_re, add_sub_cancel_right] using hreal.sub hinv

theorem real_regularized_tsum {ι : Type*} (ρ : ι → ℂ) (z : ℂ)
    (hreg : Summable (fun i => (z - ρ i)⁻¹ + (ρ i)⁻¹))
    (hinv : Summable (fun i => ((ρ i)⁻¹).re)) :
    (∑' i, ((z - ρ i)⁻¹ + (ρ i)⁻¹).re) =
      (∑' i, ((z - ρ i)⁻¹).re) + ∑' i, ((ρ i)⁻¹).re := by
  simp only [Complex.add_re]
  exact (summable_real_zero_contributions ρ z hreg hinv).tsum_add hinv

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.W03

theorem logDeriv_indexedGenusOneProduct {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U)
    (hz : ∀ i, z ≠ ρ i)
    (hsum : Summable (fun i => (z - ρ i)⁻¹ + (ρ i)⁻¹))
    (hprod : MultipliableLocallyUniformlyOn (fun i => genusOneFactor (ρ i)) U)
    (hprod_ne : (∏' i, genusOneFactor (ρ i) z) ≠ 0) :
    logDeriv (fun w => ∏' i, genusOneFactor (ρ i) w) z =
      ∑' i, ((z - ρ i)⁻¹ + (ρ i)⁻¹) := by
  have hid : (fun i => logDeriv (genusOneFactor (ρ i)) z) =
      (fun i => (z - ρ i)⁻¹ + (ρ i)⁻¹) := by
    funext i
    exact logDeriv_genusOneFactor (hρ i) (hz i)
  rw [← hid]
  apply logDeriv_tprod_eq_tsum hU hzU
  · exact fun i => genusOneFactor_ne_zero (hρ i) (hz i)
  · exact fun i => (differentiable_genusOneFactor (ρ i)).differentiableOn
  · rwa [hid]
  · exact hprod
  · exact hprod_ne

end SiegelZerosAwei.W03

end

end SiegelZeros

end OAI
