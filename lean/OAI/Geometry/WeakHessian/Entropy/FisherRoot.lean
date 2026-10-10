import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FisherDensity
import OAI.Geometry.WeakHessian.Entropy.FisherEpsilon
import OAI.Geometry.WeakHessian.Sobolev.SobolevPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile45
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

def regularizedRoot (a x : ℝ) : ℝ := ∫ s in 0..x, (2*Real.sqrt (max a (s+a)))⁻¹

lemma regularizedRoot_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedRoot a) ((2*Real.sqrt (max a (x+a)))⁻¹) x := by
  have hc : Continuous (fun s : ℝ => (2*Real.sqrt (max a (s+a)))⁻¹) :=
    (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
      (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedRoot_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedRoot a) x = (2*Real.sqrt (max a (x+a)))⁻¹ :=
  (regularizedRoot_hasDeriv ha x).deriv

lemma regularizedRoot_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedRoot a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (regularizedRoot_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (regularizedRoot a) = (fun x => (2*Real.sqrt (max a (x+a)))⁻¹) from funext (regularizedRoot_deriv ha)]
  exact (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
    (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))

lemma regularizedRoot_zero (a : ℝ) : regularizedRoot a 0 = 0 := by simp [regularizedRoot]

lemma regularizedRoot_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedRoot a) x| ≤ (2*Real.sqrt a)⁻¹ := by
  rw [regularizedRoot_deriv ha,abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))]
  exact inv_anti₀ (mul_pos (by norm_num) (Real.sqrt_pos.2 ha))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left _ _)) (by norm_num))

lemma regularizedRoot_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨(2*Real.sqrt a)⁻¹,by positivity⟩ : ℝ≥0) (regularizedRoot a) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (regularizedRoot_hasDeriv ha x).differentiableAt)
  intro x
  exact NNReal.coe_le_coe.mp (regularizedRoot_deriv_bound ha x)

lemma regularizedRoot_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedRoot a x = Real.sqrt (x+a)-Real.sqrt a := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 x) :
      HasDerivAt (fun t : ℝ => Real.sqrt (t+a)) ((2*Real.sqrt (max a (s+a)))⁻¹) s := by
    rw [max_eq_right (by linarith [hs.1] : a ≤ s+a),← one_div]
    simpa only [one_div,id_eq] using! ((hasDerivAt_id s).add_const a).sqrt
      (ne_of_gt (by linarith [hs.1] : 0 < s+a))
  have hc : Continuous (fun s : ℝ => (2*Real.sqrt (max a (s+a)))⁻¹) :=
    (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
      (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))
  simpa only [regularizedRoot,zero_add] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le hx] using hs)) (hc.intervalIntegrable 0 x)

lemma regularizedRoot_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ regularizedRoot a x ∧ regularizedRoot a x ≤ Real.sqrt x := by
  rw [regularizedRoot_eq ha hx]
  constructor
  · exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  · have h : Real.sqrt (x+a) ≤ Real.sqrt x+Real.sqrt a := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      nlinarith [Real.sq_sqrt hx,Real.sq_sqrt ha.le,
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg a)]
    linarith

lemma regularizedRoot_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => regularizedRoot (fisherEpsilon n) x) atTop (𝓝 (Real.sqrt x)) := by
  simp_rw [regularizedRoot_eq (fisherEpsilon_pos _) hx]
  simpa only [Function.comp_def,add_zero,Real.sqrt_zero,sub_zero] using
    (Real.continuous_sqrt.tendsto (x+0) |>.comp (tendsto_const_nhds.add fisherEpsilon_tendsto)).sub
      (Real.continuous_sqrt.tendsto 0 |>.comp fisherEpsilon_tendsto)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.sqrt_of_fisher (hfin : FiniteOnBoundedSets m) {u : X → ℝ}
    (hu : Sobolev m u) (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    (hi : Integrable u m) (hI : Integrable (fisherDensity (m := m) u) m) :
    Sobolev m (fun x => Real.sqrt (u x)) := by
  let w (x : X) := Real.sqrt (u x)
  have hw : MemLp w 2 m := (memLp_two_iff_integrable_sq hmu.sqrt.aestronglyMeasurable).mpr
    (hi.congr (hun.mono fun x hx => (Real.sq_sqrt hx).symm))
  let fn (n : ℕ) (x : X) := regularizedRoot (fisherEpsilon n) (u x)
  have hfn (n : ℕ) : MemLp (fn n) 2 m :=
    (regularizedRoot_lipschitz (fisherEpsilon_pos n)).comp_memLp
      (regularizedRoot_zero _) hu.1
  have hT : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hw.toLp w)) := by
    apply toLp_tendsto_of_domination hfn hw hw
    · intro n
      filter_upwards [hun] with x hx
      simpa only [fn,w,Real.norm_eq_abs,abs_of_nonneg (regularizedRoot_bounds (fisherEpsilon_pos n) hx).1,
        abs_of_nonneg (Real.sqrt_nonneg _)] using (regularizedRoot_bounds (fisherEpsilon_pos n) hx).2
    · exact hun.mono fun x hx => regularizedRoot_tendsto hx
  let Dn (n : ℕ) (x : X) := |deriv (regularizedRoot (fisherEpsilon n)) (u x)| *weakGradient m u x
  have hDn (n : ℕ) : MemLp (Dn n) 2 m := by
    have hm : AEStronglyMeasurable (fun x => |deriv (regularizedRoot (fisherEpsilon n)) (u x)|) m :=
      ((regularizedRoot_contDiff (fisherEpsilon_pos n)).continuous_deriv le_rfl).measurable.comp hmu |>.abs |>.aestronglyMeasurable
    simpa only [Dn,mul_comm] using memLp_mul_bounded hu.2.2 hm
      (ae_of_all _ fun x => by simpa only [abs_abs] using regularizedRoot_deriv_bound (fisherEpsilon_pos n) (u x))
  have hUG (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) :=
    (weakGradient_isMinimal hu.2.1.2).1.comp_contDiff hu.1.aemeasurable
      (regularizedRoot_contDiff (fisherEpsilon_pos n))
        (ae_of_all _ fun x => regularizedRoot_deriv_bound (fisherEpsilon_pos n) (u x))
  have hsq (n : ℕ) : ∀ᵐ x ∂m, Dn n x^2 ≤ fisherDensity (m := m) u x := by
    filter_upwards [hun,weakGradient_zero_on_zero hu.2.1 hmu] with x hx hz
    dsimp only [Dn,fisherDensity]
    rcases hx.eq_or_lt with hx | hx
    · simp [hz hx.symm,hx.symm]
    · rw [regularizedRoot_deriv (fisherEpsilon_pos n),max_eq_right (by linarith : fisherEpsilon n ≤ u x+fisherEpsilon n)]
      have he : (2*Real.sqrt (u x+fisherEpsilon n))^2 = 4*(u x+fisherEpsilon n) := by
        rw [mul_pow,Real.sq_sqrt (by linarith [fisherEpsilon_pos n])]; ring
      rw [mul_pow,sq_abs,inv_pow,he,← div_eq_inv_mul]
      apply div_le_div_of_nonneg_left (sq_nonneg _) hx
      linarith [fisherEpsilon_pos n]
  have hB (n : ℕ) : ‖(hDn n).toLp (Dn n)‖ ≤ Real.sqrt (∫ x,fisherDensity (m := m) u x ∂m) := by
    have H := integral_mono_ae
      ((memLp_two_iff_integrable_sq (hDn n).aestronglyMeasurable).mp (hDn n)) hI (hsq n)
    rw [← norm_toLp_sq_eq_integral (hDn n)] at H
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt H
  obtain ⟨D,hD,hDB⟩ := exists_upperGradient_of_bounded_l2
    (fun n => (hUG n).congr_ae (hfn n).coeFn_toLp.symm (hDn n).coeFn_toLp.symm) hT hB
  exact Sobolev.of_upperGradient hfin hw
    (hD.congr_ae hw.coeFn_toLp Filter.EventuallyEq.rfl) (Lp.memLp D)
end WeakHessian

end
end InlinedFile45

end OAI
