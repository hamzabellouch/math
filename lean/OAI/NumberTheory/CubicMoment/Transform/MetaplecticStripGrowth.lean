import OAI.NumberTheory.CubicMoment.Transform.MetaplecticGaussGrowth

namespace OAI

/-! The Gauss series has polynomial growth on the contour strip,
by Heath-Brown's auxiliary and raw-sum estimates and Abel continuation. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators ContDiff
namespace CubicFirstMoment

lemma abelCumulative_norm_le_finite (c : ℕ → ℂ) {x M : ℝ} (hxM : x ≤ M) :
    ‖abelCumulative c x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊M⌋₊, ‖c n‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxM)) (fun _ _ _ => _root_.norm_nonneg _)

lemma heathBrown_partial_sum_bound (hHB : HeathBrownGaussPartialSums)
    {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ U : ℝ, 1 ≤ U →
      ‖metaplecticPartialSum r U‖ ≤ B*U^(5/6:ℝ) := by
  obtain ⟨C,hC,hlarge⟩ := heathBrown_partial_sum_large hr hs hHB
  let M : ℝ := max 1 (norm r)^2
  let D : ℝ := ∑ n ∈ Finset.Icc 1 ⌊M⌋₊, ‖metaplecticNormCoefficient r n‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _)
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro U hU
  by_cases hUM : M ≤ U
  · exact (hlarge U hUM).trans (by gcongr; linarith)
  · have hsmall : ‖metaplecticPartialSum r U‖ ≤ D := by
      rw [← abelCumulative_metaplecticNormCoefficient r (zero_le_one.trans hU)]
      exact abelCumulative_norm_le_finite _ (le_of_not_ge hUM)
    have hp : 1 ≤ U^(5/6:ℝ) := Real.one_le_rpow hU (by norm_num)
    exact hsmall.trans (by nlinarith)

lemma heathBrown_right_strip_polynomial {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hHB : HeathBrownGaussPartialSums)
    {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    MetaplecticStripPolynomial (F r) (9/10) 2 := by
  obtain ⟨B,hB,hbound⟩ := heathBrown_partial_sum_bound hHB hr hs
  have hc (U : ℝ) (hU : 1 ≤ U) :
      ‖abelCumulative (metaplecticNormCoefficient r) U‖ ≤ B*U^(5/6:ℝ) := by
    rw [abelCumulative_metaplecticNormCoefficient r (zero_le_one.trans hU)]
    exact hbound U hU
  refine ⟨30*B,by positivity,1,?_⟩
  intro σ hσ t ht
  have hsre : (5/6:ℝ) < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by
    simp
    linarith [hσ.1]
  rw [metaplectic_right_abel hF hr hs hbound _ hsre]
  have hab := norm_abelContinuation_le hc hsre
  have hn : ‖(σ:ℂ)+(t:ℂ)*Complex.I‖ ≤ 2+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+(t:ℂ)*Complex.I)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,mul_one] at h
    rw [abs_of_nonneg (by linarith [hσ.1])] at h
    linarith [hσ.2]
  have hd : (1/15:ℝ) ≤ ((σ:ℂ)+(t:ℂ)*Complex.I).re-5/6 := by
    simp
    linarith [hσ.1]
  have hratio : B*‖(σ:ℂ)+(t:ℂ)*Complex.I‖ /
      (((σ:ℂ)+(t:ℂ)*Complex.I).re-5/6) ≤ B*(2+|t|)/(1/15:ℝ) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn hB) (by norm_num) hd
  exact hab.trans (hratio.trans (by simp only [pow_one]; nlinarith [abs_nonneg t]))

lemma MetaplecticStripPolynomial.join {F : ℂ → ℂ} {a m b : ℝ}
    (hleft : MetaplecticStripPolynomial F a m)
    (hright : MetaplecticStripPolynomial F m b) :
    MetaplecticStripPolynomial F a b := by
  obtain ⟨C,hC,n,hleft⟩ := hleft
  obtain ⟨D,hD,k,hright⟩ := hright
  refine ⟨C+D,add_nonneg hC hD,n+k,?_⟩
  intro σ hσ t ht
  have hp : 1 ≤ 1+|t| := by linarith [abs_nonneg t]
  by_cases hsm : σ ≤ m
  · exact (hleft σ ⟨hσ.1,hsm⟩ t ht).trans
      (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (Nat.le_add_right n k))
        (by positivity) (by positivity))
  · exact (hright σ ⟨(le_of_not_ge hsm),hσ.2⟩ t ht).trans
      (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (Nat.le_add_left k n))
        (by positivity) (by positivity))

/-- Polynomial growth of the original Gauss series on the precise strip
needed by the contour shift, derived from the published source inputs. -/
lemma metaplectic_strip_polynomial_of_published {F Ψ Z : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZ : HeathBrownZBound Z)
    (hfac : HeathBrownZFactorization Ψ Z) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hHB : HeathBrownGaussPartialSums) {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) {ε : ℝ} (hε : 0 < ε) :
    MetaplecticStripPolynomial (F r) (1/2+ε) 2 :=
  (heathBrown_left_strip_polynomial hZ hfac hdiv hε hr hs).join
    (heathBrown_right_strip_polynomial hF hHB hr hs)

/-- The smooth Gauss sum and its residue after shifting the Mellin
contour using polynomial strip growth. -/
theorem metaplectic_smooth_shift_of_published {F Ψ Z : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZ : HeathBrownZBound Z)
    (hfac : HeathBrownZFactorization Ψ Z) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hHB : HeathBrownGaussPartialSums) {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {U : ℝ} (hU : 1 ≤ U) (t : ℝ) :
    metaplecticSmoothSum r W U t = ((1/(2*Real.pi):ℝ):ℂ)*
      (∫ v : ℝ, mellin W (((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
        (U:ℂ)^(((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
        F r (((1/2+ε:ℝ):ℂ)+((v-t):ℂ)*Complex.I))+
      metaplecticResidue r*(U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*
        mellin W ((5/6:ℝ)+(t:ℂ)*Complex.I) := by
  exact metaplectic_smooth_shift_of_polynomial hF hr hs (by linarith) (by linarith)
    (metaplectic_strip_polynomial_of_published hF hZ hfac hdiv hHB hr hs hε)
    W hW hpos hsm hU t

end CubicFirstMoment

end

end OAI
