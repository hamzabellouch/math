import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedDyads
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductDetector

namespace OAI

/-! Exact prime detection on each original high-height window. The smooth
total-product envelope and the finite squarefree support are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstTailKernel (ℓ : ℤ) (H U X : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*gauss n*primeProductEnvelope (norm n/X)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow U t)
      (Real.log (norm n)-Real.log X)

def scaleFirstTailRoughWindow (ℓ : ℤ) (H U X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*scaleFirstTailKernel ℓ H U X n

def scaleFirstTailSemiprimeWindow (ℓ : ℤ) (H U X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X with (primeFactors n).card = 2,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*scaleFirstTailKernel ℓ H U X n

lemma scaleFirstTailKernel_envelope_zero (ℓ : ℤ) (H U X : ℝ) (n : Eisenstein)
    (hn : primeProductEnvelope (norm n/X) = 0) : scaleFirstTailKernel ℓ H U X n = 0 := by
  simp only [scaleFirstTailKernel,hn,mul_zero,zero_mul]

lemma scaleFirstTailKernel_norm_range (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : scaleFirstTailKernel ℓ H U X n ≠ 0) :
    X/2 < norm n ∧ norm n < 3*X := by
  have henv : primeProductEnvelope (norm n/X) ≠ 0 := by
    intro hz
    exact hn (scaleFirstTailKernel_envelope_zero ℓ H U X n hz)
  constructor
  · by_contra hn
    exact henv (primeProductEnvelope_zero_lower
      ((div_le_iff₀ hX).mpr (by linarith)))
  · by_contra hn
    exact henv (primeProductEnvelope_zero
      ((le_div_iff₀ hX).mpr (by linarith)))

lemma primeProductGaussTail_window_sum (ℓ : ℤ) (H T X : ℝ) :
    primeProductGaussTail ℓ H T X =
      ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ p ∈ primeCutoff (4*X), scaleFirstTailKernel ℓ H (T*(3/2:ℝ)^j) X p := by
  unfold primeProductGaussTail finiteHeightTail
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p hp
  rw [scaleFirstTailKernel,gauss_prime (mem_primeCutoff.mp hp).1]
  ring

lemma scaleFirstTailKernel_prime_support (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X) :
    (∑ p ∈ primeCutoff (4*X), scaleFirstTailKernel ℓ H U X p) =
      ∑ p ∈ (primeProductSupport X).filter Prime, scaleFirstTailKernel ℓ H U X p := by
  have hsub : (primeProductSupport X).filter Prime ⊆ primeCutoff (4*X) := by
    intro p hp
    obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
    have hs := primeProductSupport_spec hp
    exact mem_primeCutoff.mpr ⟨⟨hs.1,hprime⟩,by linarith [hs.2.2.2]⟩
  symm
  apply Finset.sum_subset hsub
  intro p hp hout
  have hprime := (mem_primeCutoff.mp hp).1
  apply scaleFirstTailKernel_envelope_zero
  by_cases hu : norm p ≤ 3*X
  · have hl : norm p < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨mem_primaryElementBall.mpr ⟨hprime.1,hu⟩,hprime.2.squarefree⟩,hl⟩,hprime.2⟩))
    exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
  · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))

theorem scaleFirstTailWindow_detector (ℓ : ℤ) :
    ∀ᶠ X : ℝ in atTop, ∀ H U : ℝ,
      (∑ p ∈ primeCutoff (4*X), scaleFirstTailKernel ℓ H U X p) =
        scaleFirstTailRoughWindow ℓ H U X-scaleFirstTailSemiprimeWindow ℓ H U X := by
  filter_upwards [concrete_prime_detector (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 3),eventually_gt_atTop (0:ℝ)] with X hdet hX
  intro H U
  rw [scaleFirstTailKernel_prime_support ℓ H U hX]
  apply hdet (primeProductSupport X) (scaleFirstTailKernel ℓ H U X)
  · intro n hn
    have hs := primeProductSupport_spec hn
    exact ⟨by linarith [hs.2.2.1],hs.2.2.2⟩
  · intro n hn hns
    exact (hns (primeProductSupport_spec hn).2.1).elim

theorem primeProductGaussTail_detector (ℓ : ℤ) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      primeProductGaussTail ℓ H T X =
        (∑ j ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailRoughWindow ℓ H (T*(3/2:ℝ)^j) X) -
        ∑ j ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailSemiprimeWindow ℓ H (T*(3/2:ℝ)^j) X := by
  filter_upwards [scaleFirstTailWindow_detector ℓ] with X hX
  intro H T
  rw [primeProductGaussTail_window_sum]
  simp_rw [hX]
  rw [Finset.sum_sub_distrib]

lemma scaleFirstTail_envelope_sum (c : Eisenstein → ℂ) (ℓ : ℤ) (H U : ℝ)
    {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ primeProductSupport X, c n*scaleFirstTailKernel ℓ H U X n) =
      ∑ n ∈ centralProductEnvelope X, c n*scaleFirstTailKernel ℓ H U X n := by
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hout
    have hs := primeProductSupport_spec hn
    have hsize : Real.exp primeProductWeights.radius*X < norm n := lt_of_not_ge
      (fun hb => hout (Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hs.1,hb⟩,hs.2.1⟩))
    have hz := primeProductWeights.upper_support () (norm n/X) ((lt_div_iff₀ hX).mpr hsize)
    rw [scaleFirstTailKernel_envelope_zero ℓ H U X n hz,mul_zero]
  · intro n hn hout
    have hs := centralProductEnvelope_spec hn
    have hz : primeProductEnvelope (norm n/X) = 0 := by
      by_cases hu : norm n ≤ 3*X
      · have hl : norm n < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hs.1,hu⟩,hs.2.1⟩,hl⟩))
        exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
      · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))
    rw [scaleFirstTailKernel_envelope_zero ℓ H U X n hz,mul_zero]
  · intro n _ _
    rfl

lemma scaleFirstTailRoughWindow_full (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X) :
    scaleFirstTailRoughWindow ℓ H U X =
      ∑ n ∈ centralProductEnvelope X,
        (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*scaleFirstTailKernel ℓ H U X n :=
  scaleFirstTail_envelope_sum _ ℓ H U hX

end CubicFirstMoment

end

end OAI
