import OAI.Probability.RadialTransition.SqrtGrid

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma uniform_kac_parameters {t βlo βhi H A : ℝ}
    (ht : 1 ≤ t) (hb : 0 < βlo) (hb' : βlo ≤ βhi) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (htA : 6912*A ≤ t) :
    ∃ κ D F C : ℝ, 0 < κ ∧ 1 ≤ D ∧ D ≤ F ∧ 0 ≤ C ∧
      ∀ β ∈ Icc βlo βhi, ∀ h ∈ Icc (-H) H, ∀ a ∈ Icc (0:ℝ) A,
      (∀ η ∈ Icc (0:ℝ) 1, κ ≤ β*(t^2/3456)-β*t*a*(1+η)/2) ∧
      t*h+β*(t^2/2)+t+1 ≤ κ*D ∧
      Real.exp (β*(t^2/2)+t*(h+β*a*D)+1) ≤ F ∧
      ∀ B ∈ Icc (0:ℝ) A, ∀ v ∈ Icc (0:ℝ) D,
        boxPressureConstant t β (h+β*a*v) B ≤ C := by
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < βhi := hb.trans_le hb'
  let κ := βlo*t^2/6912
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let D := 1+(t*H+βhi*(t^2/2)+t+1)/κ
  have hD : 1 ≤ D := by
    have hn : 0 ≤ (t*H+βhi*(t^2/2)+t+1)/κ := by positivity
    dsimp [D]; linarith
  let F := max D (Real.exp (βhi*(t^2/2)+t*(H+βhi*A*D)+1))
  let C := boxPressureConstant t βhi (H+βhi*A*D) A
  refine ⟨κ, D, F, C, hκ, hD, le_max_left _ _,
    boxPressureConstant_nonneg ht0.le hb0.le hA, ?_⟩
  intro β hβ h hh a ha
  have hβ0 : 0 < β := hb.trans_le hβ.1
  have haA : t*a ≤ t^2/6912 := by
    have h1 := mul_le_mul_of_nonneg_left (ha.2.trans (show A ≤ t/6912 by linarith)) ht0.le
    nlinarith
  have hshift (v : ℝ) (hv : v ∈ Icc (0:ℝ) D) : h+β*a*v ≤ H+βhi*A*D := by
    apply add_le_add hh.2
    exact mul_le_mul (mul_le_mul hβ.2 ha.2 ha.1 hb0.le) hv.2 hv.1 (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro η hη
    have he : t*a*(1+η)/2 ≤ t*a := by
      have hta : 0 ≤ t*a := mul_nonneg ht0.le ha.1
      nlinarith [mul_nonneg hta (show 0 ≤ 1-η by linarith [hη.2])]
    have h1 := mul_le_mul_of_nonneg_left (he.trans haA) hβ0.le
    have h2 := mul_le_mul_of_nonneg_right hβ.1 (show 0 ≤ t^2/6912 by positivity)
    dsimp [κ]
    nlinarith
  · have h1 := add_le_add (mul_le_mul_of_nonneg_left hh.2 ht0.le)
      (mul_le_mul_of_nonneg_right hβ.2 (show 0 ≤ t^2/2 by positivity))
    dsimp [D]
    have heq : κ*((t*H+βhi*(t^2/2)+t+1)/κ) = t*H+βhi*(t^2/2)+t+1 := by field_simp
    nlinarith
  · apply le_trans (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
    have h1 := mul_le_mul_of_nonneg_right hβ.2 (show 0 ≤ t^2/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hshift D ⟨by linarith, le_rfl⟩) ht0.le
    linarith
  · intro B hB v hv
    exact boxPressureConstant_mono ht0 hβ0 hβ.2 (hshift v hv) hB.1 hB.2

lemma kac_grid_error_bound {C F t β a βhi A W R₀ R s q : ℝ}
    (hC : 0 ≤ C) (hF : 0 ≤ F) (ht : 0 < t) (hb : 0 ≤ βhi) (hA : 0 ≤ A)
    (hW : 0 ≤ W) (hpref : β*a/2 ≤ βhi*A/2)
    (hs : 0 < s) (hR₀ : 2 ≤ R₀) (hq : 0 ≤ q/R)
    (hsratio : R₀/s ≤ 2*Real.sqrt (R₀/R)) (hqratio : q/R ≤ 4*Real.sqrt (R₀/R))
    (hlog : Real.log ((F+2)*s^3)/(t*s^3) ≤ (F+5)/(t*s)) :
    2*C*R₀/s+β*a/2*(W*q/R)*F^2+Real.log ((F+2)*s^3)/(t*s^3) ≤
      6*(1+2*C+(F+5)/t+βhi*A/2*W*F^2)*Real.sqrt (R₀/R) := by
  have hfirst : 2*C*R₀/s ≤ 4*C*Real.sqrt (R₀/R) := by
    calc
      _ = 2*C*(R₀/s) := by ring
      _ ≤ 2*C*(2*Real.sqrt (R₀/R)) := mul_le_mul_of_nonneg_left hsratio (by positivity)
      _ = _ := by ring
  have hsecond : β*a/2*(W*q/R)*F^2 ≤ 4*(βhi*A/2*W*F^2)*Real.sqrt (R₀/R) := by
    have hm := mul_le_mul hpref (mul_le_mul_of_nonneg_left hqratio hW)
      (mul_nonneg hW hq) (show 0 ≤ βhi*A/2 by positivity)
    calc
      _ = β*a/2*(W*(q/R))*F^2 := by ring
      _ ≤ βhi*A/2*(W*(4*Real.sqrt (R₀/R)))*F^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg F)
      _ = _ := by ring
  have hn : 1/s ≤ Real.sqrt (R₀/R) := by
    have hm := div_le_div_of_nonneg_right hR₀ hs.le
    have heq : 2/s = 2*(1/s) := by ring
    rw [heq] at hm
    linarith
  have hthird : (F+5)/(t*s) ≤ (F+5)/t*Real.sqrt (R₀/R) := by
    calc
      _ = (F+5)/t*(1/s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  have hz := Real.sqrt_nonneg (R₀/R)
  have h1 := mul_nonneg hC hz
  have h2 := mul_nonneg (show 0 ≤ (F+5)/t by positivity) hz
  have h3 := mul_nonneg (show 0 ≤ βhi*A/2*W*F^2 by positivity) hz
  nlinarith only [hfirst, hsecond, hlog, hthird, hz, h1, h2, h3]

lemma family_kac_uniform {t βlo βhi H A : ℝ}
    (ht : 1 ≤ t) (hb : 0 < βlo) (hb' : βlo ≤ βhi) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (htA : 6912*A ≤ t) :
    ∃ C K : ℝ, 0 < C ∧ 1 ≤ K ∧
    ∀ (b S : ℕ → ℝ) (a R₀ R β h : ℝ),
      (∀ n, 0 ≤ b n) → (∀ n, 1 ≤ S n) → Summable b →
      2 ≤ R₀ → (∀ n, S n ≤ R₀) → 0 ≤ a → a+∑' n, b n ≤ A →
      2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8 →
      K*R₀ ≤ R → β ∈ Icc βlo βhi → h ∈ Icc (-H) H →
      |grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h-
        idealAttraction (grandPressure (familyPotential t b S) t) a β h| ≤
        C*Real.sqrt (R₀/R) := by
  obtain ⟨κ, D, F, C, hκ, hD, hDF, hC0, hc⟩ := uniform_kac_parameters ht hb hb' hH hA htA
  let W := 10000*(bumpLip:ℝ)+bumpIntegral⁻¹
  have hW : 0 ≤ W := by dsimp [W]; have := bumpIntegral_pos; positivity
  let K := 16*(W+1)^2
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg W]
  let E := 1+2*C+(F+5)/t+βhi*A/2*W*F^2
  have ht0 : 0 < t := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 < βhi := hb.trans_le hb'
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨6*E, K, by positivity, hK, ?_⟩
  intro b S a R₀ R β h hbn hS hs hR₀ hrange ha hmass hrow hRR hβ hh
  have hsum : 0 ≤ ∑' n, b n := tsum_nonneg hbn
  have haA : a ∈ Icc (0:ℝ) A := ⟨ha, by linarith⟩
  have hBA : (∑' n, b n) ∈ Icc (0:ℝ) A := ⟨hsum, by linarith⟩
  obtain ⟨hq, hqpos, hq1, hqR, hRq, hqfrac, hη⟩ := sqrt_grid_exists hR₀ hW hRR
  have hR0 : 0 < R := by linarith
  have heq : kernelRowError hq R = W*(hq:ℝ)/R := rfl
  have heta : kernelUpperError hq R ≤ 1 := (kernelUpperError_le_row hR0.le).trans (heq ▸ hη)
  obtain ⟨hcoerc, hcut, hF, hC⟩ := hc β hβ h hh a haA
  have hbound := family_kac_variational_grid hqpos ht (hb.trans_le hβ.1) ha hqR hq1
    hbn hS hs hR₀ hrange hrow hκ (hcoerc _ ⟨kernelUpperError_nonneg hq hR0.le, heta⟩)
    hD hcut hDF hF (hC _ hBA)
  apply hbound.trans
  have hlog := log_volume_error_le hF0 hq1 ht0
  have hbA : β*a/2 ≤ βhi*A/2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul hβ.2 haA.2 ha hb0.le) (by norm_num)
  have hs0 : 0 < (hq:ℝ)/4 := by linarith
  rw [heq]
  exact kac_grid_error_bound hC0 hF0 ht0 hb0.le hA hW hbA hs0 hR₀
    (div_nonneg (Nat.cast_nonneg hq) hR0.le) hRq hqfrac hlog

end RadialTransition
end

end OAI
