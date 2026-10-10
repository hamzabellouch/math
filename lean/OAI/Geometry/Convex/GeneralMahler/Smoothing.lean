import OAI.Geometry.Convex.GeneralMahler.Density

namespace OAI
/-! Gaussian smoothing and an integration by parts formula. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

theorem hasDeriv_nDensity_shift (x a : Rn m) :
    HasFDerivAt (fun y => nDensity (x-y))
      (nDensity (x-a) • (innerSL ℝ (x-a))) a := by
  let c : ℝ := (√(2 * π))⁻¹ ^ m
  have hf := ((hasFDerivAt_const (𝕜 := ℝ) x a).sub (hasFDerivAt_id a))
  have hg := ((hf.norm_sq.neg.mul_const ((2:ℝ)⁻¹)).exp).const_mul c
  convert hg using 1
  all_goals ext v; simp [nDensity,c,div_eq_mul_inv, two_smul]; ring

theorem nDensity_shift_bound (a B : ℝ) (ha : 0 < a) (_hb : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Rn m, ‖y‖ ≤ B →
      nDensity (x-y) ≤ C * exp (-(a * ‖x‖)) := by
  let c : ℝ := (√(2 * π))⁻¹ ^ m
  refine ⟨c*exp (a*B+a^2/2),by dsimp [c]; positivity,?_⟩
  intro x y hy
  rw [mul_assoc, ← exp_add]
  change c*_ ≤ c*_
  gcongr
  have hh : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa using (norm_add_le (x-y) y)
  nlinarith [sq_nonneg (‖x-y‖-a)]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def smoothG (f : Rn m → F) (a : Rn m) := ∫ x, f (x+a) ∂(normal m)

lemma smoothG_eq (f : Rn m → F) (a : Rn m) :
    smoothG f a = ∫ x, nDensity (x-a) • f x := by
  rw [smoothG, normal_integral]
  rw [← integral_add_right_eq_self (μ := volume) (fun x => nDensity (x-a) • f x) a]
  simp

abbrev G' (f : Rn m → F) (a x : Rn m) : Rn m →L[ℝ] F :=
  (nDensity (x-a) • innerSL ℝ (x-a)).smulRight (f x)

lemma continuous_pair_G' (x : Rn m) :
    Continuous (fun p : Rn m × F =>
      (nDensity (x-p.1) • innerSL ℝ (x-p.1)).smulRight p.2) := by
  change Continuous (fun p : Rn m × F => ContinuousLinearMap.smulRightL ℝ _ _
    (nDensity (x-p.1) • innerSL ℝ (x-p.1)) p.2)
  fun_prop

theorem smooth_domination {f : Rn m → F}
    (hf : PolyBound f) {B : ℝ} (hb : 0 ≤ B) :
    ∃ g : Rn m → ℝ, Integrable g ∧ ∀ a x, ‖a‖ ≤ B →
      ‖nDensity (x-a) • f x‖ ≤ g x ∧ ‖G' f a x‖ ≤ g x := by
  obtain ⟨C,n,hc,h⟩ := hf
  obtain ⟨K,hk,hg⟩ := nDensity_shift_bound (m := m) 1 B zero_lt_one hb
  let g := fun x:Rn m => (K*C)*(1+B) * ((1+‖x‖)^(n+1) * exp (-(1*‖x‖)))
  refine ⟨g,(integrable_polynomial_exp_tail zero_lt_one _).const_mul _ ,?_⟩
  intro a x ha
  have h₁ := h x
  have h₂ := hg x a ha
  have he : 1 ≤ (1+B)*(1+‖x‖) := one_le_mul_of_one_le_of_one_le (by linarith) (by simp)
  have hr : ‖x-a‖ ≤ (1+B)*(1+‖x‖) := by
    apply (norm_sub_le ..).trans
    nlinarith [norm_nonneg x]
  have h₄ : nDensity (x-a) * ‖f x‖ ≤ K * exp (-(1*‖x‖))*(C*(1+‖x‖)^n) :=
    mul_le_mul h₂ h₁ (norm_nonneg _) (by positivity)
  have ge : g x = (K * exp (-(1*‖x‖))*(C*(1+‖x‖)^n))*((1+B)*(1+‖x‖)) := by
    dsimp [g]; rw [pow_succ]; ring
  rw [ge]
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (nDensity_pos _).le]
    exact h₄.trans (le_mul_of_one_le_right (by positivity) he)
  · rw [G',ContinuousLinearMap.norm_smulRight_apply,norm_smul, innerSL_apply_norm,
      Real.norm_of_nonneg (nDensity_pos _).le,mul_right_comm]
    exact mul_le_mul h₄ hr (norm_nonneg _) (by positivity)

theorem strongly_G' {f : Rn m → F} (hm : StronglyMeasurable f) (a : Rn m) :
    StronglyMeasurable (G' f a) := by
  let g (p : Rn m × F) : Rn m →L[ℝ] F :=
    ContinuousLinearMap.smulRightL ℝ _ _
      (nDensity (p.1-a) • innerSL ℝ (p.1-a)) p.2
  have hc : Continuous g := by dsimp only [g]; fun_prop
  have hu : StronglyMeasurable (fun x => (id x,f x)) :=
    (continuous_id (X := Rn m)).stronglyMeasurable.prodMk hm
  have H : StronglyMeasurable (g ∘ (fun x => (id x,f x))) := hc.comp_stronglyMeasurable hu
  let f' := G' f a
  have he : G' f a = g ∘ (fun x => (id x,f x)) := by rfl
  rw [he]
  exact H

theorem smoothG_hasFDeriv {f : Rn m → F} (hf : PolyBound f)
    (hm : StronglyMeasurable f) (a : Rn m) :
    Integrable (G' f a) ∧ HasFDerivAt (smoothG f) (∫ x, G' f a x) a := by
  obtain ⟨g,hg,h⟩ := smooth_domination hf (show 0 ≤ ‖a‖+1 by positivity)
  let s := closedBall a 1
  have hs : s ∈ 𝓝 a := closedBall_mem_nhds _ zero_lt_one
  have h₁ : ‖a‖ ≤ ‖a‖+1 := by linarith
  have h₂ (y) (hy : y ∈ s) : ‖y‖ ≤ ‖a‖+1 := by
    have hh : ‖y‖ ≤ ‖y-a‖+‖a‖ := by simpa using (norm_add_le (y-a) a)
    change dist _ _ ≤ _ at hy
    rw [dist_eq_norm] at hy
    linarith
  have hmeas (y : Rn m) :
      StronglyMeasurable (fun x : Rn m => nDensity (x-y) • f x) :=
    (by fun_prop : Continuous (fun x : Rn m => nDensity (x-y))).stronglyMeasurable.smul hm
  refine ⟨hg.mono' (strongly_G' hm a).aestronglyMeasurable
    (ae_of_all _ fun x => (h _ _ h₁).2), ?_⟩
  rw [funext (smoothG_eq f)]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Eventually.of_forall fun y => (hmeas y).aestronglyMeasurable)
    (hg.mono' (hmeas a).aestronglyMeasurable (ae_of_all _ fun x => (h _ _ h₁).1))
    ((strongly_G' hm a).aestronglyMeasurable)
    (ae_of_all _ fun x y hy => (h y x (h₂ y hy)).2) hg (ae_of_all _ ?_)
  intro x y _
  exact (hasDeriv_nDensity_shift x y).smul_const _

theorem continuous_smoothG {f : Rn m → F} (hf : PolyBound f)
    (hm : StronglyMeasurable f) : Continuous (smoothG f) :=
  continuous_iff_continuousAt.mpr fun x => (smoothG_hasFDeriv hf hm x).2.continuousAt

theorem smoothG_deriv_cont {f : Rn m → F} (hf : PolyBound f)
    (hm : StronglyMeasurable f) : Continuous (fun a => ∫ x, G' f a x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨g,hg,h⟩ := smooth_domination hf (show 0 ≤ ‖a‖+1 by positivity)
  have hv : ∀ᶠ y in 𝓝 a, ‖y‖ ≤ ‖a‖+1 :=
    continuous_norm.continuousAt (Iic_mem_nhds (by linarith))
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => ((strongly_G' hm y).aestronglyMeasurable))
    (hv.mono fun y hy => (ae_of_all _ fun x => (h y x hy).2)) hg
    (ae_of_all _ ?_)
  intro x
  exact ((continuous_pair_G' x).comp (continuous_id.prodMk continuous_const)).continuousAt
end GeneralMahler

end

end OAI
