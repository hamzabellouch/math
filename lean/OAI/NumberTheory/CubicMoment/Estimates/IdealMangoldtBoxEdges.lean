import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtTail

namespace OAI

/-! Bounds for the left and horizontal edges of the actual prime contour. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma mem_finiteMellinBox {a b T σ t : ℝ}
    (hσ : σ ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
    (σ:ℂ)+(t:ℂ)*Complex.I ∈ finiteMellinBox a b T := by
  simpa only [finiteMellinBox,Complex.mem_reProdIm,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,mul_zero,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,Complex.I_im,mul_one,zero_add] using And.intro hσ ht

lemma idealMangoldtMellinIntegrand_norm (L : ℂ → ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖=
      X^σ*‖mellin W (σ+(t:ℂ)*Complex.I)‖*‖logDeriv L (σ+(t:ℂ)*Complex.I)‖ := by
  change ‖mellinScaledWeight W X σ t*(-logDeriv L _)‖=_
  rw [norm_mul,norm_neg,mellinScaledWeight_norm W hX]

theorem idealMangoldt_left_edge_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℂ → ℂ) (X a T B : ℝ),
      0 < X → |a| ≤ 2 → 0 ≤ T → 0 ≤ B →
      (∀ t ∈ Icc (-T) T, ‖logDeriv L (a+(t:ℂ)*Complex.I)‖ ≤ B) →
      ‖∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)‖ ≤
        K*X^a*B := by
  obtain ⟨K,hK,hb⟩ := mellinScaledWeight_moment_bound W hW hpos hsm 2 0
  refine ⟨K,hK,?_⟩
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
    _ ≤ B*(K*X^a) := mul_le_mul_of_nonneg_left (hb X a hX ha) hB
    _ = _ := by ring

theorem idealMangoldt_horizontal_edges_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      ∀ (X a b T B : ℝ), 1 ≤ X → 0 ≤ a → a ≤ b → b ≤ 2 → 0 < T → 0 ≤ B →
      (∀ s ∈ finiteMellinBox a b T, L s ≠ 0) →
      (∀ s ∈ finiteMellinBox a b T, ‖logDeriv L s‖ ≤ B) →
      ‖(∫ t in -T..T, idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I))-
        (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))‖ ≤
          K*X^b*B/T^2 := by
  obtain ⟨C,hC,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm 2 2
  refine ⟨4*C,by positivity,?_⟩
  intro L hL X a b T B hX ha hab hb hT hB hn hlog
  have hXp : 0 < X := by linarith
  have hpoint (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t|=T) :
      ‖idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖ ≤ C*X^b*B/T^2 := by
    have hσabs : |σ| ≤ 2 := by rw [abs_of_nonneg (ha.trans hσ.1)]; exact hσ.2.trans hb
    have hm := hdecay σ hσabs t
    rw [ht] at hm
    have hm' : ‖mellin W (σ+(t:ℂ)*Complex.I)‖ ≤ C/T^2 := by
      apply (le_div_iff₀ (pow_pos hT 2)).mpr
      have hpow : T^2 ≤ (1+T)^2 := by nlinarith
      simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hpow (_root_.norm_nonneg _)).trans hm
    have htmem : t ∈ Icc (-T) T := by
      have hh := abs_le.mp ht.le
      exact hh
    have hl := hlog _ (mem_finiteMellinBox hσ htmem)
    rw [idealMangoldtMellinIntegrand_norm L W hXp]
    calc
      _ ≤ X^b*(C/T^2)*B := by
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
  have hc : 0 ≤ C*X^b*B/T^2 := by positivity
  calc
    _ ≤ 2*(C*X^b*B/T^2)*2 := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
