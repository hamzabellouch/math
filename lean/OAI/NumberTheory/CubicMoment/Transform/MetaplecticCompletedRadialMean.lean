import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformAngular
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedPoleBound

namespace OAI

/-! Both signed means of the completed zero-mode sum, with its genuine
pole retained. The remainder uses the proved short/long Voronoi estimates. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_completed_signed_radial_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) (D : ℕ) :
    ∃ (mpos mneg : ℕ) (K E : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ K ∧ 0 ≤ E ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-((mneg:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-((mneg:ℝ)-1/2)) →
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 (W i) X t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 (W i) X t‖))/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
            E*X^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨C,hC,hshort⟩ := h.metaplectic_completed_short_mean hMV hM hη hB
  obtain ⟨mp,P,hmp,hP,hpos⟩ := h.metaplectic_completed_long_mean hV hMV hM 0 hη hB
  obtain ⟨mn,N,hmn,hN,hneg⟩ := h.metaplectic_completed_negative_long_mean hV hMV hM 0 hη hB
  obtain ⟨E,hE,hpole⟩ := h.metaplectic_completed_pole_bound D
  refine ⟨mp,mn,2*C+P+N,2*E,hmp,hmn,by positivity,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hXlo hXhi hgmp hgpp hgmn hgpn
  let Q : ℝ := Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T
  let A : ℝ := E*X^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let f (t : ℝ) := metaplecticHeightCompleted r 0 (W i) X t
  let g (t : ℝ) := mellinPhase t X*
    metaplecticMain r 0 (fun x => W i x*mellinPhase t x) X
  have hf : Continuous f := continuous_metaplectic_height_completed r 0 (W i) (h.compact i) hX
  have hg : Continuous g := continuous_metaplectic_height_main r 0 (W i)
    (h.compact i) (h.positive i) (h.smooth i) X
  have hpositive : (∫ t in T..2*T, ‖f t‖)/T ≤ (C+P)*Q+A := by
    by_cases hs : X ≤ Real.sqrt (norm r)*T^2
    · have hb := hshort i r hr 0 Y X T 0 hY hX hT hXhi hs
      simp only [add_zero] at hb
      exact hb.trans (by dsimp [Q] at *; nlinarith only [mul_nonneg hP hQ,hA])
    · have hc := hpos i r hr hsr Y X T hY hX hT hRY hTY hXlo
        (le_of_lt (lt_of_not_ge hs)) hgmp hgpp
      have hb := interval_mean_norm_le_centered f g hf hg hTp (E := A) (by
        intro t ht
        exact hpole i r hr X hX T hTp t (ht.1.trans (le_abs_self t)))
      exact hb.trans (by dsimp [f,g,Q] at *; nlinarith only [hc,mul_nonneg hC hQ])
  have hnegative : (∫ t in T..2*T, ‖f (-t)‖)/T ≤ (C+N)*Q+A := by
    by_cases hs : X ≤ Real.sqrt (norm r)*T^2
    · have hb := hshort i r hr 0 Y X T (-(3*T)) hY hX hT hXhi hs
      rw [integral_reflected_height (fun t => ‖f t‖) T]
      simp only [sub_eq_add_neg]
      exact hb.trans (by dsimp [f,Q] at *; nlinarith only [mul_nonneg hN hQ,hA])
    · have hc := hneg i r hr hsr Y X T hY hX hT hRY hTY hXlo
        (le_of_lt (lt_of_not_ge hs)) hgmn hgpn
      have hb := interval_mean_norm_le_centered (fun t => f (-t)) (fun t => g (-t))
        (hf.comp continuous_neg) (hg.comp continuous_neg) hTp (E := A) (by
          intro t ht
          apply hpole i r hr X hX T hTp (-t)
          rw [abs_neg]
          exact ht.1.trans (le_abs_self t))
      exact hb.trans (by dsimp [f,g,Q] at *; nlinarith only [hc,mul_nonneg hC hQ])
  have he := intervalIntegral.integral_comp_neg (a := T) (b := 2*T) (fun t => ‖f t‖)
  rw [←he,add_div]
  change (∫ t in T..2*T, ‖f (-t)‖)/T+(∫ t in T..2*T, ‖f t‖)/T ≤ _
  exact (add_le_add hnegative hpositive).trans_eq (by dsimp [Q,A]; ring)

end CubicFirstMoment

end

end OAI
