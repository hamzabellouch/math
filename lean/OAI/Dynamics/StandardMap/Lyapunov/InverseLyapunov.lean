import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.HyperbolicSet

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def standardReversal (z : Torus) : Torus :=
  recurrenceCoordinates (recurrenceCoordinates z).swap

noncomputable def tangentReversal : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp (planeSwap.comp tangentCoordinates)

@[simp] lemma standardReversal_fst (z : Torus) : (standardReversal z).1 = z.1-z.2 := rfl
@[simp] lemma standardReversal_snd (z : Torus) : (standardReversal z).2 = -z.2 := by
  simp [standardReversal, recurrenceCoordinates]
@[simp] lemma tangentReversal_re (z : ℂ) : (tangentReversal z).re = z.re-z.im := rfl
@[simp] lemma tangentReversal_im (z : ℂ) : (tangentReversal z).im = -z.im := by
  simp [tangentReversal]
@[simp] lemma tangentReversal_involutive (z : ℂ) : tangentReversal (tangentReversal z)=z := by
  apply Complex.ext <;> simp

lemma standardReversal_inverseMap (k : ℝ) (z : Torus) :
    standardReversal (inverseMap k z) = standardMap k (standardReversal z) := by
  apply Prod.ext
  · simp only [standardReversal_fst, standardReversal_snd, inverseMap, standardMap, kick]
    abel
  · simp only [standardReversal_snd, inverseMap, standardMap, standardReversal_fst, kick]
    abel

lemma standardReversal_inverse_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    standardReversal ((inverseMap k)^[n] z) = (standardMap k)^[n] (standardReversal z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', standardReversal_inverseMap, ih,
        Function.iterate_succ_apply']

lemma measurePreserving_standardReversal : MeasurePreserving standardReversal area area :=
  measurePreserving_recurrenceCoordinates.comp
    (measurePreserving_torusSwap.comp measurePreserving_recurrenceCoordinates)

lemma standardInverseDerivative_conjugate (k : ℝ) (z : Torus) :
    standardInverseDerivative k z = tangentReversal.comp
      ((standardDerivative k (standardReversal z)).comp tangentReversal) := by
  apply ContinuousLinearMap.ext
  intro w
  change tangentCoordinates (transferStepInv _ (tangentCoordinates w)) = _
  have hc : (inverseMap k z).1 = (standardReversal z).1 := rfl
  rw [hc]
  simp only [standardDerivative, tangentReversal, ContinuousLinearMap.comp_apply,
    tangentCoordinates_involutive, planeSwap_transferStep]

noncomputable def standardInverseDerivativeProduct (k : ℝ) (z : Torus) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (standardInverseDerivative k ((inverseMap k)^[n] z)).comp
      (standardInverseDerivativeProduct k z n)

lemma standardInverseDerivativeProduct_area (k : ℝ) (z : Torus) (n : ℕ) :
    PlaneAreaPreserving (standardInverseDerivativeProduct k z n) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih => exact (standardInverseDerivative_area k _).comp ih

lemma standardInverseDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardInverseDerivativeProduct k z n = tangentReversal.comp
      ((standardDerivativeProduct k (standardReversal z) n).comp tangentReversal) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    exact (tangentReversal_involutive w).symm
  | succ n ih =>
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardInverseDerivativeProduct, ih, standardInverseDerivative_conjugate,
      ContinuousLinearMap.comp_apply, tangentReversal_involutive, standardDerivativeProduct,
      standardReversal_inverse_iterate]

lemma complexProjection_inverse_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardInverseLift k)^[n] z) = (inverseMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      complexProjection_standardInverseLift, ih]

lemma hasFDerivAt_standardInverseLift_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    HasFDerivAt ((standardInverseLift k)^[n])
      (standardInverseDerivativeProduct k (complexProjection z) n) z := by
  induction n with
  | zero => exact hasFDerivAt_id z
  | succ n ih =>
    have hh := (hasFDerivAt_standardInverseLift k ((standardInverseLift k)^[n] z)).comp z ih
    simpa only [complexProjection_inverse_iterate, ← Function.iterate_succ',
      standardInverseDerivativeProduct] using hh

lemma tangentReversal_conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentReversal.comp (A.comp tangentReversal)‖ ≤ 81*‖A‖ := by
  have he : tangentReversal.comp (A.comp tangentReversal) =
      tangentCoordinates.comp ((planeSwap.comp
        ((tangentCoordinates.comp (A.comp tangentCoordinates)).comp planeSwap)).comp
        tangentCoordinates) := by
    ext w
    rfl
  rw [he]
  calc
    _ ≤ 9*‖planeSwap.comp ((tangentCoordinates.comp (A.comp tangentCoordinates)).comp planeSwap)‖ :=
      conjugate_norm_le _
    _ = 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
      rw [norm_planeSwap_comp, norm_comp_planeSwap]
    _ ≤ 9*(9*‖A‖) := mul_le_mul_of_nonneg_left (conjugate_norm_le A) (by norm_num)
    _ = _ := by ring

lemma inverse_derivative_log_difference_bound (k : ℝ) (z : Torus) (n : ℕ) :
    |Real.log ‖standardInverseDerivativeProduct k z n‖-
      Real.log ‖standardDerivativeProduct k (standardReversal z) n‖| ≤ Real.log 81 := by
  let A := standardDerivativeProduct k (standardReversal z) n
  let B := standardInverseDerivativeProduct k z n
  have hA : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k _ n)
  have hB : 0 < ‖B‖ := lt_of_lt_of_le zero_lt_one
    (standardInverseDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2
  have h1 : ‖B‖ ≤ 81*‖A‖ := by
    dsimp only [B, A]
    rw [standardInverseDerivativeProduct_conjugate]
    exact tangentReversal_conjugate_norm_le _
  have h2 : ‖A‖ ≤ 81*‖B‖ := by
    convert tangentReversal_conjugate_norm_le B using 1
    congr 1
    ext w
    simp only [B, standardInverseDerivativeProduct_conjugate,
      ContinuousLinearMap.comp_apply, tangentReversal_involutive]
    rfl
  have hl1 := Real.log_le_log hB h1
  have hl2 := Real.log_le_log hA h2
  rw [Real.log_mul (by norm_num) hA.ne'] at hl1
  rw [Real.log_mul (by norm_num) hB.ne'] at hl2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma standardLyapunov_reversal_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, standardLyapunov k hk (standardReversal z) = standardLyapunov k hk z := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_swap_ae k hk)
  filter_upwards [hh] with z hz
  change transferLyapunov k hk
    (recurrenceCoordinates (recurrenceCoordinates (recurrenceCoordinates z).swap)) = _
  rw [recurrenceCoordinates_involutive]
  exact hz

lemma ae_standardInverseLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardInverseDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_standardReversal.quasiMeasurePreserving.ae
    (ae_standardLyapunov_rate k hk)
  filter_upwards [hh, standardLyapunov_reversal_ae k hk] with z hz heq
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardInverseDerivativeProduct k z n‖-
        Real.log ‖standardDerivativeProduct k (standardReversal z) n‖)/(n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 81/(n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (inverse_derivative_log_difference_bound k z n) (Nat.cast_nonneg _)
  rw [heq] at hz
  simpa only [sub_div, sub_add_cancel, zero_add] using hd.add hz

lemma standardInverseDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardInverseDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStepInv (torusPotential k (inverseMap k z).1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k (inverseMap k z).1|+1) :=
      mul_le_mul_of_nonneg_left (transferStepInv_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk _) (by norm_num)

lemma standardInverseDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardInverseDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardInverseDerivativeProduct k z (n+1) v‖ := by
  exact ((standardInverseDerivative_area k ((inverseMap k)^[n] z)).norm_lower
    (standardInverseDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardInverseDerivative_norm_bound k hk _) (norm_nonneg _))

theorem ae_inverse_hyperbolic_flag (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      ∃ u : ℂ, u ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
        PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) v
          (if wedge u v = 0 then -standardLyapunov k hk z else standardLyapunov k hk z) := by
  filter_upwards [ae_standardInverseLyapunov_rate k hk] with z hz hpos
  exact PlaneLyapunov.positive_flag (standardInverseDerivativeProduct k z)
    (standardInverseDerivativeProduct_area k z) (9*growthBase k)
    (mul_pos (by norm_num) (by have := growthBase_ge_four k hk; linarith))
    (standardInverseDerivativeProduct_step_lower k hk z) hpos hz

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace PlaneLyapunov

abbrev UnitPlane := {v : ℂ // ‖v‖ = 1}
instance : Nonempty UnitPlane := ⟨⟨1, by simp⟩⟩

noncomputable def denseUnit : ℕ → UnitPlane := TopologicalSpace.denseSeq UnitPlane

lemma exists_approx_slow (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ∃ j : ℕ, ‖A (denseUnit j)‖ < 2/‖A‖ := by
  obtain ⟨a,ha,_,_,hb,hD⟩ := hA.singular_pair
  apply (TopologicalSpace.denseRange_denseSeq UnitPlane).exists_mem_open
    (isOpen_lt ((A.continuous.comp continuous_subtype_val).norm) continuous_const)
  refine ⟨⟨quarterTurn a, by simpa only [norm_quarterTurn] using ha⟩, ?_⟩
  change ‖A (quarterTurn a)‖ < 2/‖A‖
  rw [hb, inv_eq_one_div]
  exact div_lt_div_of_pos_right (by norm_num) (lt_of_lt_of_le zero_lt_one hD)

noncomputable def approxSlow (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) : ℂ :=
  (denseUnit (Nat.find (exists_approx_slow A hA))).val

lemma approxSlow_unit (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ‖approxSlow A hA‖ = 1 := (denseUnit _).property

lemma approxSlow_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ‖A (approxSlow A hA)‖ < 2/‖A‖ := Nat.find_spec (exists_approx_slow A hA)

lemma measurable_approxSlow {X : Type*} [MeasurableSpace X]
    (A : X → ℂ →L[ℝ] ℂ) (hA : ∀ x, PlaneAreaPreserving (A x)) (hm : Measurable A) :
    Measurable (fun x => approxSlow (A x) (hA x)) := by
  classical
  unfold approxSlow
  apply Measurable.find (f := fun j (_ : X) => (denseUnit j).val) (fun j => measurable_const)
    (fun j => measurableSet_lt ?_ (measurable_const.div hm.norm))
    (fun x => exists_approx_slow (A x) (hA x))
  exact (((continuous_id.clm_apply continuous_const :
    Continuous (fun B : ℂ →L[ℝ] ℂ => B (denseUnit j))).measurable).comp hm).norm

lemma unit_sq {s : ℂ} (hs : ‖s‖ = 1) : s.re^2+s.im^2=1 := by
  have hh := Complex.sq_norm s
  rw [hs] at hh
  simpa only [Complex.normSq_apply, one_pow, pow_two, one_mul] using hh.symm

lemma unit_projection_difference {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) :
    |a.re^2-b.re^2| ≤ |wedge a b| ∧
    |a.re*a.im-b.re*b.im| ≤ |wedge a b| := by
  have ha2 := unit_sq ha
  have hb2 := unit_sq hb
  have he1 : a.re^2-b.re^2 = wedge a b * dot a (planeSwap b) := by
    simp only [wedge, dot, planeSwap_re, planeSwap_im]
    linear_combination b.re^2*ha2-a.re^2*hb2
  have he2 : a.re*a.im-b.re*b.im = -wedge a b * dot a (star b) := by
    simp only [wedge, dot, Complex.star_def, Complex.conj_re, Complex.conj_im]
    linear_combination (b.re*b.im)*ha2-(a.re*a.im)*hb2
  have hd1 : |dot a (planeSwap b)| ≤ 1 := by
    simpa only [ha, norm_planeSwap, hb, one_mul] using abs_dot_le_norm_mul a (planeSwap b)
  have hd2 : |dot a (star b)| ≤ 1 := by
    simpa only [ha, norm_star, hb, one_mul] using abs_dot_le_norm_mul a (star b)
  rw [he1, he2, abs_mul, abs_mul, abs_neg]
  constructor <;> nlinarith [abs_nonneg (wedge a b)]

lemma norm_tendsto_zero_of_negative_growth (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} {l : ℝ}
    (hg : Growth A v l) (hl : l < 0) : Tendsto (fun n => ‖A n v‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => Real.exp ((l/2)*(n : ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_const_mul_atBot_of_neg (by linarith : l/2 < 0)).2 tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hp
  filter_upwards [(tendsto_order.mp hg.2).2 (l/2) (by linarith), eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnp).mp hn
  calc
    _ = Real.exp (Real.log ‖A n v‖) := (Real.exp_log (image_norm_pos A hA hg.1 n)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hh.le

lemma approxSlow_wedge_tendsto_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ}
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) :
    Tendsto (fun n => wedge (approxSlow (A n) (hA n)) s) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (by simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hs)
  rw [Real.norm_eq_abs, ← hA n]
  calc
    _ ≤ ‖A n (approxSlow (A n) (hA n))‖*‖A n s‖ := abs_wedge_le_norm_mul _ _
    _ ≤ 2*‖A n s‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (approxSlow_bound (A n) (hA n)).le.trans
        (div_le_self (by norm_num) (hA n).singular_pair.choose_spec.2.2.2.2)

lemma approxSlow_projection_tendsto (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ} (hunit : ‖s‖=1)
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) :
    Tendsto (fun n => (approxSlow (A n) (hA n)).re^2) atTop (𝓝 (s.re^2)) ∧
    Tendsto (fun n => (approxSlow (A n) (hA n)).re*(approxSlow (A n) (hA n)).im)
      atTop (𝓝 (s.re*s.im)) := by
  have hw := (approxSlow_wedge_tendsto_zero A hA hs).abs
  simp only [abs_zero] at hw
  constructor
  · have hd : Tendsto (fun n => (approxSlow (A n) (hA n)).re^2-s.re^2) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => ?_) hw
      rw [Real.norm_eq_abs]
      exact (unit_projection_difference (approxSlow_unit _ _) hunit).1
    have hh := hd.add (tendsto_const_nhds (x := s.re^2))
    rw [zero_add] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by dsimp only; ring
  · have hd : Tendsto (fun n => (approxSlow (A n) (hA n)).re*
        (approxSlow (A n) (hA n)).im-s.re*s.im) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => ?_) hw
      rw [Real.norm_eq_abs]
      exact (unit_projection_difference (approxSlow_unit _ _) hunit).2
    simpa only [sub_add_cancel, zero_add] using hd.add (tendsto_const_nhds (x := s.re*s.im))

noncomputable def stableCandidate (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ℂ := by
  let p := liminf (fun n => (approxSlow (A n) (hA n)).re^2) atTop
  let q := liminf (fun n => (approxSlow (A n) (hA n)).re*(approxSlow (A n) (hA n)).im) atTop
  exact if p=0 then Complex.I else ⟨p,q⟩

lemma stableCandidate_ne_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : stableCandidate A hA ≠ 0 := by
  classical
  unfold stableCandidate
  dsimp only
  split_ifs with h
  · exact Complex.I_ne_zero
  · intro he
    exact h (congrArg Complex.re he)

lemma stableCandidate_wedge (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ} (hunit : ‖s‖=1)
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) : wedge s (stableCandidate A hA)=0 := by
  classical
  have hp := approxSlow_projection_tendsto A hA hunit hs
  unfold stableCandidate
  rw [hp.1.liminf_eq, hp.2.liminf_eq]
  dsimp only
  split_ifs with h
  · have hr : s.re=0 := sq_eq_zero_iff.mp h
    simp [wedge, hr]
  · simp only [wedge]
    ring

noncomputable def stableUnit (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ℂ :=
  (‖stableCandidate A hA‖⁻¹ : ℝ) • stableCandidate A hA

lemma norm_stableUnit (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ‖stableUnit A hA‖=1 := by
  rw [stableUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (stableCandidate_ne_zero A hA))

lemma measurable_stableCandidate {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ x n, PlaneAreaPreserving (A x n))
    (hm : ∀ n, Measurable (fun x => A x n)) :
    Measurable (fun x => stableCandidate (A x) (hA x)) := by
  classical
  have hslow (n) := measurable_approxSlow (fun x => A x n) (fun x => hA x n) (hm n)
  have hp : Measurable (fun x => liminf (fun n => (approxSlow (A x n) (hA x n)).re^2) atTop) :=
    Measurable.liminf fun n => (Complex.measurable_re.comp (hslow n)).pow_const 2
  have hq : Measurable (fun x => liminf (fun n =>
      (approxSlow (A x n) (hA x n)).re*(approxSlow (A x n) (hA x n)).im) atTop) :=
    Measurable.liminf fun n => (Complex.measurable_re.comp (hslow n)).mul
      (Complex.measurable_im.comp (hslow n))
  exact Measurable.ite (measurableSet_eq_fun hp measurable_const) measurable_const
    (Complex.equivRealProdCLM.symm.continuous.measurable.comp (hp.prodMk hq))

lemma measurable_stableUnit {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ x n, PlaneAreaPreserving (A x n))
    (hm : ∀ n, Measurable (fun x => A x n)) :
    Measurable (fun x => stableUnit (A x) (hA x)) := by
  have hh := measurable_stableCandidate A hA hm
  exact hh.norm.inv.smul hh

theorem stableUnit_growth (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0<M) (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hpos : 0<l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 l)) :
    Growth A (stableUnit A hA) (-l) := by
  obtain ⟨s,hunit,hbound⟩ := exists_stable_bound A hA M hM hstep hl
  have hg := stable_growth A hA M hM hpos hl s hunit hbound
  have hz := norm_tendsto_zero_of_negative_growth A hA hg (by linarith)
  apply growth_on_line A hA hunit hg _
    (by intro hzero; have hh := norm_stableUnit A hA; rw [hzero, norm_zero] at hh; norm_num at hh)
  rw [stableUnit, wedge_smul_right, stableCandidate_wedge A hA hunit hz, mul_zero]

end PlaneLyapunov
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma continuous_standardDerivativeProduct (k : ℝ) (n : ℕ) :
    Continuous (fun z => standardDerivativeProduct k z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_standardDerivative k).comp ((continuous_standardMap k).iterate n)).clm_comp ih

lemma continuous_standardInverseDerivativeProduct (k : ℝ) (n : ℕ) :
    Continuous (fun z => standardInverseDerivativeProduct k z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_standardInverseDerivative k).comp ((continuous_inverseMap k).iterate n)).clm_comp ih

noncomputable def stableVector (k : ℝ) (z : Torus) : ℂ :=
  PlaneLyapunov.stableUnit (standardDerivativeProduct k z) (standardDerivativeProduct_area k z)
noncomputable def unstableVector (k : ℝ) (z : Torus) : ℂ :=
  PlaneLyapunov.stableUnit (standardInverseDerivativeProduct k z) (standardInverseDerivativeProduct_area k z)

lemma measurable_stableVector (k : ℝ) : Measurable (stableVector k) :=
  PlaneLyapunov.measurable_stableUnit _ _ (fun n => (continuous_standardDerivativeProduct k n).measurable)
lemma measurable_unstableVector (k : ℝ) : Measurable (unstableVector k) :=
  PlaneLyapunov.measurable_stableUnit _ _ (fun n => (continuous_standardInverseDerivativeProduct k n).measurable)
@[simp] lemma norm_stableVector (k : ℝ) (z : Torus) : ‖stableVector k z‖=1 :=
  PlaneLyapunov.norm_stableUnit _ _
@[simp] lemma norm_unstableVector (k : ℝ) (z : Torus) : ‖unstableVector k z‖=1 :=
  PlaneLyapunov.norm_stableUnit _ _
lemma stableVector_ne_zero (k : ℝ) (z : Torus) : stableVector k z ≠ 0 := by
  intro hz; have hh := norm_stableVector k z; rw [hz, norm_zero] at hh; norm_num at hh
lemma unstableVector_ne_zero (k : ℝ) (z : Torus) : unstableVector k z ≠ 0 := by
  intro hz; have hh := norm_unstableVector k z; rw [hz, norm_zero] at hh; norm_num at hh

lemma ae_stableVector_growth (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (stableVector k z)
        (-standardLyapunov k hk z) := by
  filter_upwards [ae_standardLyapunov_rate k hk] with z hz hpos
  exact PlaneLyapunov.stableUnit_growth _ (standardDerivativeProduct_area k z)
    (9*growthBase k) (by have := growthBase_ge_four k hk; positivity)
    (standardDerivativeProduct_step_lower k hk z) hpos hz

lemma ae_unstableVector_growth (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (unstableVector k z)
        (-standardLyapunov k hk z) := by
  filter_upwards [ae_standardInverseLyapunov_rate k hk] with z hz hpos
  exact PlaneLyapunov.stableUnit_growth _ (standardInverseDerivativeProduct_area k z)
    (9*growthBase k) (by have := growthBase_ge_four k hk; positivity)
    (standardInverseDerivativeProduct_step_lower k hk z) hpos hz

lemma standardInverseDerivative_standardDerivative (k : ℝ) (z : Torus) (v : ℂ) :
    standardInverseDerivative k (standardMap k z) (standardDerivative k z v)=v := by
  simp only [standardInverseDerivative, standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_involutive, inverseMap_standardMap, transferStepInv_inv]

lemma standardDerivative_standardInverseDerivative (k : ℝ) (z : Torus) (v : ℂ) :
    standardDerivative k (inverseMap k z) (standardInverseDerivative k z v)=v := by
  simp only [standardInverseDerivative, standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_involutive, transferStep_inv]

lemma standardDerivativeProduct_shift (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardDerivativeProduct k (standardMap k z) n (standardDerivative k z v) =
      standardDerivativeProduct k z (n+1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, ih,
      ← Function.iterate_succ_apply]

lemma standardInverseDerivativeProduct_shift (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k (inverseMap k z) n (standardInverseDerivative k z v) =
      standardInverseDerivativeProduct k z (n+1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, ih,
      ← Function.iterate_succ_apply]

lemma standardInverseDerivativeProduct_forward (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k (standardMap k z) (n+1) (standardDerivative k z v) =
      standardInverseDerivativeProduct k z n v := by
  rw [← standardInverseDerivativeProduct_shift, standardInverseDerivative_standardDerivative,
    inverseMap_standardMap]

lemma contracting_wedge_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s t : ℂ}
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0))
    (ht : Tendsto (fun n => ‖A n t‖) atTop (𝓝 0)) : wedge s t=0 := by
  have hh : Tendsto (fun _ : ℕ => |wedge s t|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hs.mul ht)
    rw [← hA n]
    exact abs_wedge_le_norm_mul _ _
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh)

lemma ae_stableVector_covariant (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z))=0 := by
  have hs := ae_stableVector_growth k hk
  filter_upwards [hs, (measurePreserving_standardMap k).quasiMeasurePreserving.ae hs] with z hz hnext hp
  have hn := hnext (by simpa only [standardLyapunov_invariant] using hp)
  have h0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k z) (hz hp) (by linarith)
  have h1 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k (standardMap k z)) hn
    (by rw [standardLyapunov_invariant]; linarith)
  apply contracting_wedge_zero _ (standardDerivativeProduct_area k (standardMap k z)) h1
  convert h0.comp (tendsto_add_atTop_nat 1) using 1
  funext n
  exact congrArg norm (standardDerivativeProduct_shift k z n (stableVector k z))

lemma ae_unstableVector_covariant (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z))=0 := by
  have hs := ae_unstableVector_growth k hk
  filter_upwards [hs, (measurePreserving_standardMap k).quasiMeasurePreserving.ae hs] with z hz hnext hp
  have hn := hnext (by simpa only [standardLyapunov_invariant] using hp)
  have h0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k z) (hz hp) (by linarith)
  have h1 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k (standardMap k z)) hn
    (by rw [standardLyapunov_invariant]; linarith)
  apply contracting_wedge_zero _ (standardInverseDerivativeProduct_area k (standardMap k z)) h1
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [standardInverseDerivativeProduct_forward] using h0

lemma unit_collinear_eq_smul {s v : ℂ} (hs : ‖s‖=1) (hw : wedge s v=0) :
    v = dot s v • s := by
  simpa only [hw, zero_smul, add_zero] using unit_expansion s v hs

lemma unit_collinear_dot_ne_zero {s v : ℂ} (hs : ‖s‖=1) (hw : wedge s v=0) (hv : v ≠ 0) :
    dot s v ≠ 0 := by
  intro h
  have hh := unit_collinear_eq_smul hs hw
  rw [h, zero_smul] at hh
  exact hv hh

lemma covariant_collinear_iff (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {s u t v : ℂ} (hs : s ≠ 0) (hu : u ≠ 0) (ht : ‖t‖=1) (hv : ‖v‖=1)
    (hst : wedge t (A s)=0) (huv : wedge v (A u)=0) :
    wedge s u=0 ↔ wedge t v=0 := by
  have hAs : A s ≠ 0 := by
    intro h; exact hs (by have hh := hA.norm_lower s; rw [h, norm_zero, mul_zero] at hh; exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hAu : A u ≠ 0 := by
    intro h; exact hu (by have hh := hA.norm_lower u; rw [h, norm_zero, mul_zero] at hh; exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hcs := unit_collinear_dot_ne_zero ht hst hAs
  have hcu := unit_collinear_dot_ne_zero hv huv hAu
  rw [← hA, unit_collinear_eq_smul ht hst, unit_collinear_eq_smul hv huv,
    wedge_smul_left, wedge_smul_right]
  simp only [mul_eq_zero, hcs, hcu, false_or]

def coincidentLines (k : ℝ) (hk : 0 ≤ k) : Set Torus :=
  {z | 0 < standardLyapunov k hk z ∧ wedge (stableVector k z) (unstableVector k z)=0}

lemma measurableSet_coincidentLines (k : ℝ) (hk : 0 ≤ k) :
    MeasurableSet (coincidentLines k hk) := by
  apply (measurableSet_lt measurable_const (measurable_standardLyapunov k hk)).inter
  apply measurableSet_eq_fun _ measurable_const
  exact ((Complex.measurable_re.comp (measurable_stableVector k)).mul
    (Complex.measurable_im.comp (measurable_unstableVector k))).sub
    ((Complex.measurable_im.comp (measurable_stableVector k)).mul
      (Complex.measurable_re.comp (measurable_unstableVector k)))

lemma preimage_coincidentLines_ae (k : ℝ) (hk : 0 ≤ k) :
    standardMap k ⁻¹' coincidentLines k hk =ᵐ[area] coincidentLines k hk := by
  filter_upwards [ae_stableVector_covariant k hk, ae_unstableVector_covariant k hk] with z hs hu
  change (0 < standardLyapunov k hk (standardMap k z) ∧
      wedge (stableVector k (standardMap k z)) (unstableVector k (standardMap k z))=0) =
    (0 < standardLyapunov k hk z ∧ wedge (stableVector k z) (unstableVector k z)=0)
  rw [standardLyapunov_invariant]
  by_cases hp : 0 < standardLyapunov k hk z
  · simp only [hp, true_and]
    exact propext (covariant_collinear_iff _ (standardDerivative_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z)
      (norm_stableVector k _) (norm_unstableVector k _) (hs hp) (hu hp)).symm
  · simp only [hp, false_and]

end StandardMapEntropy

end
end

end OAI
