import OAI.Analysis.IrrationalRotation.Spectral.CFCLogSeries

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra
namespace Invariant233
namespace CFCLogSeries
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma trace_pow_derivative_sum (τ : TracialState A) (a b : A) (n : ℕ) :
    τ (∑ i ∈ Finset.range (n+1), a ^ (n-i) * b * a ^ i) =
      (n+1) • τ (a ^ n * b) := by
  rw [map_sum]
  have hterm : ∀ i ∈ Finset.range (n+1),
      τ (a ^ (n-i) * b * a ^ i) = τ (a ^ n * b) := by
    intro i hi
    have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [τ.tracial (a ^ (n-i) * b) (a ^ i), ← mul_assoc, ← pow_add,
      Nat.add_sub_of_le hin]
  calc
    (∑ i ∈ Finset.range (n+1), τ.toContinuousLinearMap (a ^ (n-i) * b * a ^ i)) =
        ∑ _i ∈ Finset.range (n+1), τ (a ^ n * b) := Finset.sum_congr rfl hterm
    _ = _ := by simp

omit [Nontrivial A] in

theorem hasDerivAt_trace_term (τ : TracialState A) {f : ℝ → A} {f' : A} {x : ℝ}
    (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun t => τ (term (f t) n)) (τ (f x ^ n * f')) x := by
  let L := τ.toContinuousLinearMap.restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt x
    ((hf.fun_pow' (n+1)).const_smul ((n+1 : ℝ)⁻¹))
  have hvalue : L (((n+1 : ℝ)⁻¹) •
      (∑ i ∈ Finset.range (n+1), f x ^ (n-i) * f' * f x ^ i)) =
      τ (f x ^ n * f') := by
    rw [map_smul]
    change ((n+1 : ℝ)⁻¹) • τ (∑ i ∈ Finset.range (n+1),
      f x ^ (n-i) * f' * f x ^ i) = _
    rw [trace_pow_derivative_sum, ← Nat.cast_smul_eq_nsmul ℝ (n+1), smul_smul]
    simp only [Nat.cast_add, Nat.cast_one,
      inv_mul_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity), one_smul]
  change HasDerivAt (fun t => τ (term (f t) n))
    (L (((n+1 : ℝ)⁻¹) • (∑ i ∈ Finset.range (n+1),
      f x ^ (n-i) * f' * f x ^ i))) x at hd
  exact hd.congr_deriv hvalue

theorem hasDerivAt_trace_log_one_sub (τ : TracialState A)
    {f f' : ℝ → A} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (_hC : 0 ≤ C)
    (hsa : ∀ y ∈ s, IsSelfAdjoint (f y))
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ s, ‖f y‖ ≤ r) (hdbound : ∀ y ∈ s, ‖f' y‖ ≤ C)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => τ (CFC.log (1-f y)))
      (-τ (Ring.inverse (1-f x) * f' x)) x := by
  have hu : Summable (fun n : ℕ => ‖τ.toContinuousLinearMap‖ * C * r^n) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hterms : ∀ n y, y ∈ s →
      HasDerivAt (fun t => τ (term (f t) n)) (τ (f y ^ n * f' y)) y :=
    fun n y hy => hasDerivAt_trace_term τ (hf y hy) n
  have hb : ∀ n y, y ∈ s →
      ‖τ (f y ^ n * f' y)‖ ≤ ‖τ.toContinuousLinearMap‖ * C * r^n := by
    intro n y hy
    calc
      ‖τ (f y ^ n * f' y)‖ ≤
          ‖τ.toContinuousLinearMap‖ * ‖f y ^ n * f' y‖ :=
        τ.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖τ.toContinuousLinearMap‖ * (‖f y ^ n‖ * ‖f' y‖) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ ‖τ.toContinuousLinearMap‖ * (r^n * C) := by
        gcongr
        · exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hbound y hy) n)
        · exact hdbound y hy
      _ = _ := by ring
  have hs0 : Summable (fun n => τ (term (f x) n)) :=
    (TracialState_hasSum_log τ (hsa x hx) ((hbound x hx).trans_lt hr)).summable
  have hd := hasDerivAt_tsum_of_isPreconnected hu hs hsc hterms hb hx hs0 hx
  have hgeom : HasSum (fun n : ℕ => τ (f x ^ n * f' x))
      (τ (Ring.inverse (1-f x) * f' x)) :=
    τ.toContinuousLinearMap.hasSum
      ((hasSum_geom_series_inverse (f x) ((hbound x hx).trans_lt hr)).mul_right (f' x))
  have heq : (fun y => τ (CFC.log (1-f y))) =ᶠ[𝓝 x]
      (fun y => -(∑' n, τ (term (f y) n))) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [(TracialState_hasSum_log τ (hsa y hy) ((hbound y hy).trans_lt hr)).tsum_eq,
      neg_neg]
  have hout := hd.neg.congr_of_eventuallyEq heq
  simpa only [hgeom.tsum_eq] using hout

variable [PartialOrder A] [StarOrderedRing A]

theorem hasDerivAt_trace_log_of_scaled_ball (τ : TracialState A)
    {f f' : ℝ → A} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {c r C : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr : r < 1) (hC : 0 ≤ C)
    (hpos : ∀ y ∈ s, IsStrictlyPositive (f y))
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ s, ‖1-c • f y‖ ≤ r) (hdbound : ∀ y ∈ s, ‖f' y‖ ≤ C)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => τ (CFC.log (f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
  have hd := hasDerivAt_trace_log_one_sub τ hs hsc hr0 hr
    (mul_nonneg hc.le hC)
    (f := fun y => 1-c • f y) (f' := fun y => -(c • f' y))
    (fun y hy => (show IsSelfAdjoint (1 : A) by simp).sub ((IsSelfAdjoint.all c).smul (hpos y hy).isSelfAdjoint))
    (fun y hy => ((hf y hy).const_smul c).const_sub 1)
    hbound (fun y hy => by
      simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc] using
        mul_le_mul_of_nonneg_left (hdbound y hy) hc.le) hx
  have hinv : Ring.inverse (c • f x) * (c • f' x) =
      Ring.inverse (f x) * f' x := by
    apply (Ring.inverse_mul_eq_iff_eq_mul (c • f x) (c • f' x)
      (Ring.inverse (f x) * f' x) ((hpos x hx).smul hc).isUnit).mpr
    rw [smul_mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hpos x hx).isUnit,
      one_mul]
  have hd' : HasDerivAt (fun y => τ (CFC.log (c • f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
    simpa only [sub_sub_cancel, mul_neg, map_neg, neg_neg, hinv] using hd
  have heq : (fun y => τ (CFC.log (f y))) =ᶠ[𝓝 x]
      (fun y => τ (CFC.log (c • f y)) - τ (algebraMap ℝ A (Real.log c))) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [CFC.log_smul' (f y) hc (hpos y hy), map_add, add_sub_cancel_left]
  exact (hd'.sub_const (τ (algebraMap ℝ A (Real.log c)))).congr_of_eventuallyEq heq

theorem hasDerivAt_trace_log_of_normalization (τ : TracialState A)
    {f f' : ℝ → A} (hpos : ∀ y, IsStrictlyPositive (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x)
    (hscale : ∃ c : ℝ, 0 < c ∧ ‖1-c • f x‖ < 1) :
    HasDerivAt (fun y => τ (CFC.log (f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
  obtain ⟨c, hc, hcball⟩ := hscale
  let r := (‖1-c • f x‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r < 1 := by dsimp [r]; linarith
  have hrx : ‖1-c • f x‖ < r := by dsimp [r]; linarith
  have hcont : ContinuousAt (fun y => ‖1-c • f y‖) x :=
    (continuousAt_const.sub ((hf x).continuousAt.const_smul c)).norm
  have he1 : ∀ᶠ y in 𝓝 x, ‖1-c • f y‖ < r :=
    hcont.eventually_lt_const hrx
  have he2 : ∀ᶠ y in 𝓝 x, ‖f' y‖ < ‖f' x‖ + 1 :=
    hcf'.norm.eventually_lt_const (by linarith)
  obtain ⟨l, u, hxu, hlu⟩ := (he1.and he2).exists_Ioo_subset
  exact hasDerivAt_trace_log_of_scaled_ball τ isOpen_Ioo (convex_Ioo l u).isPreconnected
    hc hr0 hr (by positivity : 0 ≤ ‖f' x‖+1)
    (fun y _ => hpos y) (fun y _ => hf y)
    (fun y hy => (hlu hy).1.le) (fun y hy => (hlu hy).2.le) hxu

end CFCLogSeries
end Invariant233

end

end OAI
