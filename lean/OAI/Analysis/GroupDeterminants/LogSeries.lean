import OAI.Analysis.GroupDeterminants.FiniteFields

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology
section Analysis
variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A]

lemma trace_power_derivative (τ : A →L[ℝ] ℂ) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (a b : A) (n : ℕ) :
    τ (∑ i ∈ Finset.range (n + 1), a ^ (n - i) * b * a ^ i) =
      (n + 1 : ℝ) • τ (b * a ^ n) := by
  rw [map_sum]
  have hh (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      τ (a ^ (n - i) * b * a ^ i) = τ (b * a ^ n) := by
    rw [mul_assoc, hτ, mul_assoc, ← pow_add]
    rw [Nat.add_sub_of_le]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp_rw [Finset.sum_congr rfl hh]
  simp [← Nat.cast_smul_eq_nsmul ℝ]

lemma hasDerivAt_trace_pow_div (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f : ℝ → A} {f' : A} {x : ℝ} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' * f x ^ n)) x := by
  have h := τ.hasFDerivAt.comp_hasDerivAt x ((hf.fun_pow' (n + 1)).const_smul (n + 1 : ℝ)⁻¹)
  simpa only [Function.comp_def, Pi.smul_def, map_smul, Nat.pred_succ,
    trace_power_derivative τ hτ, smul_smul,
    inv_mul_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity), one_smul] using h

section Complete
variable [CompleteSpace A] [NormOneClass A]

lemma summable_trace_pow_div (τ : A →L[ℝ] ℂ) (a : A) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => τ ((n + 1 : ℝ)⁻¹ • a ^ (n + 1))) := by
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • a ^ (n + 1)) := by
    apply Summable.of_norm_bounded (g := fun n => ‖a‖ ^ (n + 1))
    · simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right ‖a‖
    · intro n
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left (norm_pow_le a (n + 1)) (by positivity)).trans
        (mul_le_of_le_one_left (by positivity)
          (inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))
  exact τ.summable hs

lemma hasDerivAt_trace_logSeries (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {s : Set ℝ} {x ρ B : ℝ}
    (hs : IsOpen s) (hsc : IsPreconnected s) (hx : x ∈ s)
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hρ : ρ < 1) (hρ₀ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hn : ∀ y ∈ s, ‖f y‖ ≤ ρ) (hn' : ∀ y ∈ s, ‖f' y‖ ≤ B) :
    HasDerivAt (fun y => ∑' n : ℕ, τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' x * Ring.inverse (1 - f x))) x := by
  have hsum : HasSum (fun n : ℕ => τ (f' x * f x ^ n))
      (τ (f' x * Ring.inverse (1 - f x))) := by
    exact τ.hasSum ((hasSum_geom_series_inverse (f x) ((hn x hx).trans_lt hρ)).mul_left (f' x))
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hρ₀ hρ).mul_left (‖τ‖ * B)) hs hsc
    (fun n y hy => hasDerivAt_trace_pow_div τ hτ (hf y hy) n)
    (fun n y hy => show ‖τ (f' y * f y ^ n)‖ ≤ ‖τ‖ * B * ρ ^ n from
      (τ.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul (hn' y hy)
          ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hn y hy) n))
          (by positivity) hB)) (norm_nonneg _)).trans (le_of_eq (mul_assoc _ _ _).symm)))
    hx (summable_trace_pow_div τ (f x) ((hn x hx).trans_lt hρ)) hx
  rwa [hsum.tsum_eq] at hd

lemma hasDerivAt_trace_logSeries_local (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {x : ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hc : ContinuousAt f' x) (hn : ‖f x‖ < 1) :
    HasDerivAt (fun y => ∑' n : ℕ, τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' x * Ring.inverse (1 - f x))) x := by
  obtain ⟨ρ, hρx, hρ⟩ := exists_between hn
  let B := ‖f' x‖ + 1
  have he : ∀ᶠ y in 𝓝 x, ‖f y‖ < ρ ∧ ‖f' y‖ < B :=
    ((hf x).continuousAt.norm.eventually (gt_mem_nhds hρx)).and
      (hc.norm.eventually (gt_mem_nhds (show ‖f' x‖ < B by dsimp [B]; linarith)))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  exact hasDerivAt_trace_logSeries τ hτ Metric.isOpen_ball (convex_ball x ε).isPreconnected
    (Metric.mem_ball_self hε) (fun y _ => hf y) hρ ((norm_nonneg _).trans hρx.le)
    (by dsimp [B]; positivity) (fun y hy => (he hy).1.le) (fun y hy => (he hy).2.le)

end Complete

end Analysis
section CFCSeries
variable {A : Type uA} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

omit [StarRing A] [CompleteSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
lemma norm_pow_div_le_geom (W : A) (n : ℕ) :
    ‖(n + 1 : ℝ)⁻¹ • W ^ (n + 1)‖ ≤ ‖W‖ ^ (n + 1) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_pow_le W (n + 1)) (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))

omit [StarRing A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
lemma summable_pow_div (W : A) (hW : ‖W‖ < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • W ^ (n + 1)) := by
  apply Summable.of_norm_bounded (g := fun n => ‖W‖ ^ (n + 1))
  · simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg W) hW).mul_right ‖W‖
  · exact norm_pow_div_le_geom W

lemma hasSum_pow_div_cfc_log [Nontrivial A] (W : A) (hW : IsSelfAdjoint W) (hWn : ‖W‖ < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • W ^ (n + 1)) (-CFC.log (1 - W)) := by
  let : Nonempty (spectrum ℝ W) :=
    (ContinuousFunctionalCalculus.spectrum_nonempty W hW).to_subtype
  let X : C(spectrum ℝ W, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hX : ‖X‖ ≤ ‖W‖ := by
    apply (ContinuousMap.norm_le X (norm_nonneg W)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  have hXs : Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • X ^ (n + 1)) :=
    summable_pow_div X (hX.trans_lt hWn)
  have hc : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (spectrum ℝ W) := by
    intro x hx
    have hxn : |x| < 1 := (spectrum.norm_le_norm_of_mem hx).trans_lt hWn
    have hne : 1 - x ≠ 0 := by have := (abs_lt.mp hxn).2; linarith
    exact ((Real.continuousAt_log hne).comp (continuous_const.sub continuous_id).continuousAt).neg.continuousWithinAt
  let L : C(spectrum ℝ W, ℝ) := ⟨fun x => -Real.log (1 - x.1), hc.domRestrict⟩
  have hs : HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • X ^ (n + 1)) L := by
    rw [hXs.hasSum_iff]
    ext x
    rw [← ContinuousMap.tsum_apply hXs]
    have hh := Real.hasSum_pow_div_log_of_abs_lt_one
      ((spectrum.norm_le_norm_of_mem x.property).trans_lt hWn)
    change (∑' n : ℕ, (n + 1 : ℝ)⁻¹ * (x.1) ^ (n + 1)) = -Real.log (1 - x.1)
    simpa [div_eq_mul_inv, mul_comm] using hh.tsum_eq
  have h := (cfcL hW).hasSum hs
  have hterm (n : ℕ) : (cfcL hW) ((n + 1 : ℝ)⁻¹ • X ^ (n + 1)) =
      (n + 1 : ℝ)⁻¹ • W ^ (n + 1) := by
    rw [map_smul]
    congr 1
    change cfcHom hW (X ^ (n + 1)) = _
    rw [map_pow]
    congr 1
    exact (cfc_apply id W hW).symm.trans (cfc_id ℝ W hW)
  have hL : (cfcL hW) L = -CFC.log (1 - W) := by
    change cfcHom hW L = _
    change cfcHom hW ⟨(spectrum ℝ W).domRestrict (fun x : ℝ => -Real.log (1 - x)), _⟩ = _
    rw [← cfc_apply (fun x : ℝ => -Real.log (1 - x)) W hW hc]
    rw [cfc_neg _ W]
    congr 1
    have he : cfc (fun x : ℝ => 1 - x) W = 1 - W := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun x => x) W (by fun_prop) (by fun_prop),
        cfc_const 1 W hW, cfc_id' ℝ W hW, map_one]
    rw [CFC.log, ← he]
    have hc' : ContinuousOn Real.log ((fun x : ℝ => 1 - x) '' spectrum ℝ W) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply (Real.continuousAt_log _).continuousWithinAt
      have hxn : |x| < 1 := (spectrum.norm_le_norm_of_mem hx).trans_lt hWn
      have := (abs_lt.mp hxn).2
      linarith
    rw [← cfc_comp' Real.log (fun x : ℝ => 1 - x) W hc' (by fun_prop) hW]
  simpa only [hterm, hL] using h

end CFCSeries

end GroupRingDeterminant

end

end OAI
