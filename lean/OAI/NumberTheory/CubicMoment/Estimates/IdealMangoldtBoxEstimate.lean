import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtBoxEdges

namespace OAI

/-! The finite zero-free contour gives a quantitative bound on the actual
smoothed von Mangoldt sum, including both horizontal edges and the full tail. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma idealMangoldtMellinIntegrand_integrable_right
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X σ B : ℝ} (hX : 0 < X)
    (hn : ∀ t : ℝ, L ((σ:ℂ)+(t:ℂ)*Complex.I) ≠ 0)
    (hb : ∀ t : ℝ, ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B) :
    Integrable (fun t : ℝ => idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)) := by
  have hc : Continuous (fun t : ℝ => -logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hl := ((hL.analyticAt _).deriv.div (hL.analyticAt _) (hn t)).continuousAt
    have hg : ContinuousAt (fun y : ℝ => (σ:ℂ)+(y:ℂ)*Complex.I) t := by fun_prop
    exact (hl.comp (f := fun y : ℝ => (σ:ℂ)+(y:ℂ)*Complex.I) hg).neg
  have hw := mellinScaledWeight_integrable W hW hpos hsm hX σ
  apply (hw.norm.mul_const B).mono' (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards with t
  change ‖mellinScaledWeight W X σ t*(-logDeriv L _)‖ ≤ _
  rw [norm_mul,norm_neg]
  exact mul_le_mul_of_nonneg_left (hb t) (_root_.norm_nonneg _)

theorem idealMangoldt_smooth_bound_of_box
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ C δ K : ℝ, 0 < C ∧ 0 < δ ∧ 0 < K ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
      ∀ X a b T B : ℝ, 1 ≤ X → 0 ≤ a → a ≤ b → 1 < b → b < 1+δ → b ≤ 2 →
      0 < T → 0 ≤ B →
      (∀ s ∈ finiteMellinBox a b T, L s ≠ 0) →
      (∀ s ∈ finiteMellinBox a b T, ‖logDeriv L s‖ ≤ B) →
      ‖idealMangoldtSmooth χ W X‖ ≤
        K*(X^a*B+X^b*(B+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hline⟩ := idealLogDeriv_uniform_right_line
  obtain ⟨Kl,hKl,hleft⟩ := idealMangoldt_left_edge_bound W hW hpos hsm
  obtain ⟨Ke,hKe,hedges⟩ := idealMangoldt_horizontal_edges_bound W hW hpos hsm
  obtain ⟨Kt,hKt,htail⟩ := mellinScaledWeight_moment_bound W hW hpos hsm 2 2
  let K := Kl+Ke+Kt
  refine ⟨C,δ,K,hC,hδ,by dsimp [K]; positivity,?_⟩
  intro χ hχ hχ0 hχadd L hL hs X a b T B hX ha hab hb hbδ hb2 hT hB hn hlog
  have hXp : 0 < X := by linarith
  have hBa : 0 ≤ 1/(b-1)+C := by positivity
  have hright (t : ℝ) : ‖logDeriv L ((b:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 1/(b-1)+C :=
    hline χ hχ hχ0 hχadd L hs b t hb hbδ
  have hi := idealMangoldtMellinIntegrand_integrable_right hL W hW hpos hsm hXp
    (fun t => heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa using hb)) hright
  have hl := hleft L X a T B hXp (by rw [abs_of_nonneg ha]; linarith) hT.le hB
    (fun t ht => hlog _ (mem_finiteMellinBox ⟨le_rfl,hab⟩ ht))
  have he := hedges L hL X a b T B hX ha hab hb2 hT hB hn hlog
  have ht := bounded_product_height_tail (mellinScaledWeight W X b)
    (fun t => -logDeriv L ((b:ℂ)+(t:ℂ)*Complex.I))
    (mellinScaledWeight_integrable W hW hpos hsm hXp b) 2
    (mellinScaledWeight_moment_integrable W hW hpos hsm hXp b 2) hT hBa
    (fun t => by simpa only [norm_neg] using hright t)
  have ht' : ‖∫ t in (Icc (-T) T)ᶜ,
      idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I)‖ ≤ Kt*(1/(b-1)+C)*X^b/T^2 := by
    calc
      _ ≤ ((1/(b-1)+C)/T^2)*(∫ t : ℝ, |t|^2*‖mellinScaledWeight W X b t‖) := ht
      _ ≤ ((1/(b-1)+C)/T^2)*(Kt*X^b) := by
        apply mul_le_mul_of_nonneg_left (htail X b hXp (by rw [abs_of_pos (by linarith)]; exact hb2))
        positivity
      _ = _ := by ring
  let F := fun t : ℝ => idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I)
  have hcentral : ‖∫ t in Icc (-T) T, F t‖ ≤ Kl*X^a*B+Ke*X^b*B/T^2 := by
    have hiEq : (∫ t in Icc (-T) T, F t)=∫ t in -T..T, F t := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith)]
    rw [hiEq]
    calc
      _ ≤ ‖∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)‖+
        ‖(∫ t in -T..T, F t)-
          (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))‖ := by
        simpa only [add_sub_cancel] using norm_add_le
          (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))
          ((∫ t in -T..T, F t)-
            (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)))
      _ ≤ _ := add_le_add hl he
  have hfull : ‖∫ t : ℝ, F t‖ ≤ Kl*X^a*B+Ke*X^b*B/T^2+Kt*(1/(b-1)+C)*X^b/T^2 := by
    rw [←integral_add_compl measurableSet_Icc hi]
    exact (norm_add_le _ _).trans (add_le_add hcentral ht')
  have hpre : ‖idealMangoldtSmooth χ W X‖ ≤ ‖∫ t : ℝ, F t‖ := by
    rw [idealMangoldt_smooth_mellin χ hχ hχ0 hχadd hs W hW hpos hsm hXp hb]
    change ‖((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ, F t)‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply mul_le_of_le_one_left (_root_.norm_nonneg _)
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  apply hpre.trans (hfull.trans _)
  calc
    _ ≤ K*X^a*B+K*X^b*B/T^2+K*(1/(b-1)+C)*X^b/T^2 := by
      gcongr <;> dsimp [K] <;> linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
