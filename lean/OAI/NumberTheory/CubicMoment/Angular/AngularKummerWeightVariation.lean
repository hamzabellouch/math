import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularKummerPrime
import OAI.NumberTheory.CubicMoment.Estimates.ScaledPrimeInput

namespace OAI

/-! Dividing a smooth prime weight by log preserves an explicit finite
variation bound above exp(1). This removes the Chebyshev weight without
assuming any weighted prime estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma prime_log_weight_deriv_bound {f : ℝ → ℂ} {Y x M D : ℝ}
    (hY : 0 < Y) (hx : Y ≤ x) (hlog : 1 ≤ Real.log x)
    (hM : 0 ≤ M) (_hD : 0 ≤ D) (hf : DifferentiableAt ℝ f x)
    (hfn : ‖f x‖ ≤ M) (hfd : ‖deriv f x‖ ≤ D/Y) :
    ‖deriv (fun t => f t/(Real.log t:ℂ)) x‖ ≤ (D+M)/Y := by
  have hxp : 0 < x := hY.trans_le hx
  have hLp : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hLc : (Real.log x:ℂ) ≠ 0 := by exact_mod_cast hLp.ne'
  have he : deriv (fun t => f t/(Real.log t:ℂ)) x =
      deriv f x/(Real.log x:ℂ)-f x/((x:ℂ)*(Real.log x:ℂ)^2) := by
    have hd := (hf.hasDerivAt.div (Real.hasDerivAt_log hxp.ne').ofReal_comp hLc).deriv
    change deriv (fun t => f t/(Real.log t:ℂ)) x = _ at hd
    rw [hd]
    push_cast
    field_simp

  rw [he]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖deriv f x/(Real.log x:ℂ)‖ ≤ D/Y := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
    exact (div_le_self (_root_.norm_nonneg _) hlog).trans hfd
  have hden : Y ≤ x*(Real.log x)^2 :=
    hx.trans (le_mul_of_one_le_right hxp.le (one_le_pow₀ hlog))
  have hsecond : ‖f x/((x:ℂ)*(Real.log x:ℂ)^2)‖ ≤ M/Y := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg hxp.le,Real.norm_of_nonneg hLp.le]
    exact div_le_div₀ hM hfn hY hden
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

lemma log_normalized_rescaled_mellin_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {Y R M D : ℝ} (hY : Real.exp 1 ≤ Y) (hR : 1 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w (t/Y)*mellinPhase u t/(Real.log t:ℂ)
    (∀ t ∈ Icc Y (R*Y), DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc Y (R*Y)) ∧
    ‖f Y‖+‖f (R*Y)‖+(∫ t in Ioc Y (R*Y), ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|+M) := by
  dsimp only
  have hYp : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hY1 : 1 < Y := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hY
  have hab : Y ≤ R*Y := by nlinarith
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hY
  let f := fun t => w (t/Y)*mellinPhase u t
  have hsub : Icc Y (R*Y) ⊆ Ioi (1:ℝ) := fun _ ht => hY1.trans_le ht.1
  have hf := contDiffOn_rescaled_mellin hw Y u
  have hf' : ContDiffOn ℝ ∞ f (Ioi 1) :=
    hf.mono (by
      intro t ht
      change (1:ℝ) < t at ht
      change (0:ℝ) < t
      exact zero_lt_one.trans ht)
  have hl : ContDiffOn ℝ ∞ (fun t : ℝ => (Real.log t:ℂ)) (Ioi 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiffOn_log.mono (fun t ht => ne_of_gt (zero_lt_one.trans ht)))
  have hg : ContDiffOn ℝ ∞ (fun t => f t/(Real.log t:ℂ)) (Ioi 1) := by
    have hn : ∀ t ∈ Ioi (1:ℝ), (Real.log t:ℂ) ≠ 0 := by
      intro t ht
      exact_mod_cast (Real.log_pos ht).ne'
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using hf'.mul (hl.inv hn)
  have hd : ContinuousOn (deriv (fun t => f t/(Real.log t:ℂ))) (Icc Y (R*Y)) :=
    (hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hg t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hlog (x : ℝ) (hx : Y ≤ x) : 1 ≤ Real.log x :=
    hlogY.trans (Real.log_le_log hYp hx)
  have hn (x : ℝ) : ‖f x‖ ≤ M := by
    dsimp [f]
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm (x/Y)
  have hnlog (x : ℝ) (hx : Y ≤ x) : ‖f x/(Real.log x:ℂ)‖ ≤ M := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (hlog x hx))]
    exact (div_le_self (_root_.norm_nonneg _) (hlog x hx)).trans (hn x)
  have hb (x : ℝ) (hx : Y ≤ x) :
      ‖deriv (fun t => f t/(Real.log t:ℂ)) x‖ ≤ (D+M*|u|+M)/Y := by
    apply prime_log_weight_deriv_bound hYp hx (hlog x hx) hM (by positivity)
    · exact ((hf x (hYp.trans_le hx)).contDiffAt
        (isOpen_Ioi.mem_nhds (hYp.trans_le hx))).differentiableAt (by norm_num)
    · exact hn x
    · exact rescaled_mellin_deriv_bound hw hYp hx hM hD (hwm _)
        (hwd _ (div_pos (hYp.trans_le hx) hYp)) u
  have hi : (∫ t in Ioc Y (R*Y), ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖) ≤
      (R-1)*(D+M*|u|+M) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hpoint : ∀ t ∈ uIoc Y (R*Y),
        ‖‖deriv (fun t => f t/(Real.log t:ℂ)) t‖‖ ≤ (D+M*|u|+M)/Y := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
      exact hb t ht.1.le
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Y) (b := R*Y)
      (f := fun t => ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖) hpoint
    have hnonneg : 0 ≤ ∫ t in Y..R*Y, ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg,abs_of_nonneg (sub_nonneg.mpr hab)] at he
    convert he using 1
    field_simp
  linarith [hnlog Y le_rfl,hnlog (R*Y) hab]

theorem scaled_angular_kummer_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ (Y R M B : ℝ) (w : ℝ → ℂ),
      X₀ ≤ Y → 1 ≤ R → 0 ≤ M → 0 ≤ B → ContDiff ℝ ∞ w →
      (∀ x, x < 1 → w x = 0) → (∀ x, ‖w x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv w x‖*x ≤ B) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A → ∀ u : ℝ,
      ‖smoothPrimeCharacterSum R Y w (angularKummerCharacter ℓ v) u‖ ≤
        (C*(R*Y)/(Real.log Y)^D)*(2*M+(R-1)*(B+M*|u|+M)) := by
  obtain ⟨C,X₀,hC,hX₀,hb⟩ := weighted_angular_kummer_prime_log_bound hEF ℓ hℓ A D hA hD
  refine ⟨C,max X₀ (Real.exp 1),hC,hX₀.trans_le (le_max_left _ _),?_⟩
  intro Y R M B w hY hR hM hB hw hlo hwm hwd v hv hnc hNv u
  have hYp : 0 < Y := zero_lt_one.trans (hX₀.trans_le ((le_max_left _ _).trans hY))
  have hab : Y ≤ R*Y := by nlinarith
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hd,hi,hv'⟩ := log_normalized_rescaled_mellin_variation hw
    ((le_max_right _ _).trans hY) hR hM hB hwm hwd u
  rw [smoothPrimeCharacterSum_eq_interval hYp hw.continuous hlo]
  have hscalar : 0 ≤ C*(R*Y)/(Real.log Y)^D :=
    div_nonneg (mul_nonneg hC.le (mul_nonneg hRp.le hYp.le))
      (Real.rpow_nonneg (Real.log_nonneg (le_of_lt
        (hX₀.trans_le ((le_max_left _ _).trans hY)))) _)
  exact (hb Y (R*Y) ((le_max_left _ _).trans hY) hab v hv hnc hNv _ hd hi).trans
    (mul_le_mul_of_nonneg_left hv' hscalar)

end CubicFirstMoment

end

end OAI
