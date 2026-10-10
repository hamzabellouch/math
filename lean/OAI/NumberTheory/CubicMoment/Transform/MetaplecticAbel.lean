import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinShift
import Mathlib.NumberTheory.LSeries.SumCoeff

namespace OAI

/-! Abel continuation from a bound for the actual cumulative coefficients.
This is the elementary right-strip step; no continuation identity or
pointwise growth estimate is assumed as a published input. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators
namespace CubicFirstMoment

def abelCumulative (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n

def abelContinuation (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (abelCumulative c) (-s)

lemma abelCumulative_zero {c : ℕ → ℂ} {x : ℝ} (hx : x < 1) :
    abelCumulative c x = 0 := by
  have hf : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [abelCumulative,hf]

lemma abelCumulative_locallyIntegrable (c : ℕ → ℂ) :
    LocallyIntegrableOn (abelCumulative c) (Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc c (m := 1) (a := 0) le_rfl
    (g := fun _ => (1:ℂ)) (locallyIntegrableOn_const 1)
  simp only [one_mul] at h
  exact h.mono_set Ioi_subset_Ici_self

lemma abelCumulative_bigO {c : ℕ → ℂ} {B θ : ℝ}
    (hB : ∀ x : ℝ, 1 ≤ x → ‖abelCumulative c x‖ ≤ B*x^θ) :
    abelCumulative c =O[atTop] (fun x : ℝ => x^θ) := by
  apply IsBigO.of_bound B
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hB x hx

lemma abelCumulative_zero_bigO (c : ℕ → ℂ) (b : ℝ) :
    abelCumulative c =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
  apply (isBigO_zero _ _).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with x hx hx1
  exact (abelCumulative_zero hx1).symm

lemma abelContinuation_differentiableOn {c : ℕ → ℂ} {B θ : ℝ}
    (hB : ∀ x : ℝ, 1 ≤ x → ‖abelCumulative c x‖ ≤ B*x^θ) :
    DifferentiableOn ℂ (abelContinuation c) {s : ℂ | θ < s.re} := by
  intro s hs
  have hm : DifferentiableAt ℂ (mellin (abelCumulative c)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow (abelCumulative_locallyIntegrable c)
      (a := -θ) (b := (-s).re-1)
    · simpa only [neg_neg] using abelCumulative_bigO hB
    · simpa using hs
    · exact abelCumulative_zero_bigO c _
    · linarith
  exact (differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)).differentiableWithinAt

lemma abel_mellin_integral (c : ℕ → ℂ) (s : ℂ) :
    mellin (abelCumulative c) (-s) =
      ∫ x in Ioi (1:ℝ), (x:ℂ)^(-(s+1))*abelCumulative c x := by
  unfold mellin
  simp only [smul_eq_mul,neg_add_rev]
  have he : (∫ x in Ici (1:ℝ), (x:ℂ)^(-s-1)*abelCumulative c x ∂volume.restrict (Ioi 0)) =
      ∫ x in Ioi (0:ℝ), (x:ℂ)^(-s-1)*abelCumulative c x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [abelCumulative_zero (lt_of_not_ge hx),mul_zero]
  have hinter : Ici (1:ℝ) ∩ Ioi 0 = Ici 1 := by
    ext x
    exact ⟨And.left,fun hx => ⟨hx,show 0 < x from zero_lt_one.trans_le (show 1 ≤ x from hx)⟩⟩
  rw [Measure.restrict_restrict measurableSet_Ici,hinter,integral_Ici_eq_integral_Ioi] at he
  simpa only [neg_add_rev,sub_eq_add_neg,add_comm (-1:ℂ)] using he.symm

lemma abelContinuation_eq_LSeries {c : ℕ → ℂ} {B θ : ℝ} (hθ : 0 ≤ θ)
    (hB : ∀ x : ℝ, 1 ≤ x → ‖abelCumulative c x‖ ≤ B*x^θ)
    {s : ℂ} (hs : θ < s.re) (hc : LSeriesSummable c s) :
    abelContinuation c s = LSeries c s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, c k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^θ) := by
    have h := (abelCumulative_bigO hB).comp_tendsto tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,abelCumulative,Nat.floor_natCast] using h
  rw [abelContinuation,abel_mellin_integral,LSeries_eq_mul_integral c hθ hs hc hO]
  simp only [abelCumulative,mul_comm]

lemma norm_abelContinuation_le {c : ℕ → ℂ} {B θ : ℝ} (hB : ∀ x : ℝ, 1 ≤ x → ‖abelCumulative c x‖ ≤ B*x^θ)
    {s : ℂ} (hs : θ < s.re) :
    ‖abelContinuation c s‖ ≤ B*‖s‖/(s.re-θ) := by
  have hmajor : IntegrableOn (fun x : ℝ => B*x^(θ-s.re-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul B
  have hpoint : ∀ x ∈ Ioi (1:ℝ),
      ‖(x:ℂ)^(-(s+1))*abelCumulative c x‖ ≤ B*x^(θ-s.re-1) := by
    intro x hx
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    have he : (-(s+1)).re = -s.re-1 := by simp; ring
    rw [he]
    calc
      _ ≤ x^(-s.re-1)*(B*x^θ) := mul_le_mul_of_nonneg_left (hB x hx.le) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
      _ = _ := by rw [mul_left_comm,← Real.rpow_add (zero_lt_one.trans hx)]; congr 1; ring_nf
  rw [abelContinuation,norm_mul,abel_mellin_integral]
  calc
    _ ≤ ‖s‖*(∫ x in Ioi (1:ℝ), B*x^(θ-s.re-1)) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hmajor
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hpoint x hx)) (_root_.norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      simp only [Real.one_rpow]
      have he : θ-s.re = -(s.re-θ) := by ring
      simp only [sub_add_cancel,he,div_neg,neg_div,neg_neg]
      ring

lemma analytic_eq_abelContinuation {c : ℕ → ℂ} {B θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hB : ∀ x : ℝ, 1 ≤ x → ‖abelCumulative c x‖ ≤ B*x^θ)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | θ < s.re})
    (hseries : ∀ s : ℂ, 1 < s.re → F s = LSeries c s)
    (habs : ∀ s : ℂ, 1 < s.re → LSeriesSummable c s) :
    ∀ s : ℂ, θ < s.re → F s = abelContinuation c s := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  apply (hF.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    ((abelContinuation_differentiableOn hB).analyticOnNhd hopen)
    (convex_halfSpace_re_gt θ).isPreconnected (z₀ := (2:ℂ)) (by norm_num; linarith)
  have hn : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by norm_num)
  filter_upwards [hn] with s hs
  rw [hseries s hs,abelContinuation_eq_LSeries hθ0 hB (hθ1.trans hs) (habs s hs)]

end CubicFirstMoment

end

end OAI
