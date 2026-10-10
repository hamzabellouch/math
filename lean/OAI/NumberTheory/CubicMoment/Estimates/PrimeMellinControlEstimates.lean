import OAI.NumberTheory.CubicMoment.Estimates.MellinPrimeControl
import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtBoxEdges

namespace OAI

/-! Explicit linear dependence of each prime-contour edge estimate on
its finite Mellin control. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma PrimeMellinControl.scaled_moment_bound {W : ℝ → ℂ} {D : ℝ}
    (hD : PrimeMellinControl W D) {X σ : ℝ} (hX : 0 < X) (hσ : |σ| ≤ 2)
    {A : ℕ} (hA : A=0 ∨ A=2) :
    (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖) ≤ D*X^σ := by
  have he : (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖)=
      X^σ*(∫ t : ℝ, |t|^A*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [mellinScaledWeight_norm W hX]
    ring
  rw [he,mul_comm D]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX.le _)
  rcases hA with rfl | rfl
  · simpa only [pow_zero,one_mul] using hD.mass σ hσ
  · exact hD.moment σ hσ

theorem PrimeMellinControl.left_edge_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {D : ℝ} (hD : PrimeMellinControl W D) :
    ∀ (L : ℂ → ℂ) (X a T B : ℝ),
      0 < X → |a| ≤ 2 → 0 ≤ T → 0 ≤ B →
      (∀ t ∈ Icc (-T) T, ‖logDeriv L (a+(t:ℂ)*Complex.I)‖ ≤ B) →
      ‖∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)‖ ≤
        D*X^a*B := by
  intro L X a T B hX ha hT hB hlog
  have hi := (mellinScaledWeight_integrable W hW hpos hsm hX a).norm.const_mul B
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),←integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Icc (-T) T, B*‖mellinScaledWeight W X a t‖ := by
      apply norm_integral_le_of_norm_le hi.restrict
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change ‖mellinScaledWeight W X a t*(-logDeriv L _)‖ ≤ _
      rw [norm_mul,norm_neg]
      nlinarith [hlog t ht,_root_.norm_nonneg (mellinScaledWeight W X a t)]
    _ ≤ ∫ t : ℝ, B*‖mellinScaledWeight W X a t‖ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => by positivity))
    _ = B*(∫ t : ℝ, |t|^0*‖mellinScaledWeight W X a t‖) := by
      simp only [pow_zero,one_mul,integral_const_mul]
    _ ≤ B*(D*X^a) := mul_le_mul_of_nonneg_left (hD.scaled_moment_bound hX ha (by decide : 0=0 ∨ 0=2)) hB
    _ = _ := by ring


theorem PrimeMellinControl.horizontal_edges_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {D : ℝ} (hD : PrimeMellinControl W D) :
    ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      ∀ (X a b T B : ℝ), 1 ≤ X → 0 ≤ a → a ≤ b → b ≤ 2 → 0 < T → 0 ≤ B →
      (∀ s ∈ finiteMellinBox a b T, L s ≠ 0) →
      (∀ s ∈ finiteMellinBox a b T, ‖logDeriv L s‖ ≤ B) →
      ‖(∫ t in -T..T, idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I))-
        (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))‖ ≤
          4*D*X^b*B/T^2 := by
  have hC := hD.nonneg
  have hdecay := hD.decay
  intro L hL X a b T B hX ha hab hb hT hB hn hlog
  have hXp : 0 < X := by linarith
  have hpoint (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t|=T) :
      ‖idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖ ≤ D*X^b*B/T^2 := by
    have hσabs : |σ| ≤ 2 := by rw [abs_of_nonneg (ha.trans hσ.1)]; exact hσ.2.trans hb
    have hm := hdecay σ hσabs t
    rw [ht] at hm
    have hm' : ‖mellin W (σ+(t:ℂ)*Complex.I)‖ ≤ D/T^2 := by
      apply (le_div_iff₀ (pow_pos hT 2)).mpr
      have hpow : T^2 ≤ (1+T)^2 := by nlinarith
      simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hpow (_root_.norm_nonneg _)).trans hm
    have htmem : t ∈ Icc (-T) T := by
      have hh := abs_le.mp ht.le
      exact hh
    have hl := hlog _ (mem_finiteMellinBox hσ htmem)
    rw [idealMangoldtMellinIntegrand_norm L W hXp]
    calc
      _ ≤ X^b*(D/T^2)*B := by
        gcongr
        exact hσ.2
      _ = _ := by ring
  have hh := idealMangoldt_finite_contour_bound hL W hW hpos hsm hXp hab hT.le hn
    (fun σ hσ => hpoint σ T hσ (abs_of_pos hT)) (fun σ hσ => by
      have he : (σ:ℂ)-(T:ℂ)*Complex.I=(σ:ℂ)+((-T:ℝ):ℂ)*Complex.I := by push_cast; ring
      rw [he]
      exact hpoint σ (-T) hσ (by rw [abs_neg,abs_of_pos hT]))
  apply hh.trans
  have hlen : b-a ≤ 2 := by linarith
  have hc : 0 ≤ D*X^b*B/T^2 := by positivity
  calc
    _ ≤ 2*(D*X^b*B/T^2)*2 := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
