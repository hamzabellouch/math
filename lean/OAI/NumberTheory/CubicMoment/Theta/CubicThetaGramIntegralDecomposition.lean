import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramDenominatorIntegrable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubePrimePart

namespace OAI

/-! Legitimate finite splitting of the full Gram integral. Each summand
is absolutely integrable with its original positive cutoffs. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramIdentityPart (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) (ε : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
    (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k))

def cubicThetaGramPrimeFreePart (p h k : Eisenstein) (W V : C_c(ℝ,ℂ)) (ε δ : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
    ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p∣c),
      cubicThetaGramKloostermanTerm h k V c v

lemma cubicThetaGramIdentity_integrable (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*
      (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k))) (Ioi ε) := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  have hc : ContinuousOn (fun v => star (W v)/(v:ℂ)^3*
      (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k))) (Icc ε B) := by
    intro v hv
    have hz : (v:ℂ)^3≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hε.trans_le hv.1).ne')
    exact ((W.continuous.continuousAt.star.div (Complex.continuous_ofReal.continuousAt.pow 3) hz).mul
      (V.continuous.continuousAt.mul continuousAt_const)).continuousWithinAt
  have hi : IntegrableOn (fun v => star (W v)/(v:ℂ)^3*
      (V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k))) (Icc ε B) :=
    hc.integrableOn_compact isCompact_Icc
  apply hi.of_forall_sdiff_eq_zero measurableSet_Ioi
  rintro v ⟨hv,hvB⟩
  have hz : W v=0 := by
    by_contra hn
    exact hvB ⟨hv.le,hB ⟨v,subset_tsupport _ hn,rfl⟩⟩
  simp only [hz,star_zero,zero_div,zero_mul]

lemma cubicThetaGram_sum_integrable (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) (S : Finset Eisenstein) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*
      ∑ c∈S,cubicThetaGramKloostermanTerm h k V c v) (Ioi ε) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum S (fun c _ => cubicThetaGramDenominator_integrable h k W V c hε hδ hV)

theorem cubicThetaKloostermanGram_finite_integrals (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) :
    cubicThetaKloostermanGram h k W V ε δ=
      cubicThetaGramIdentityPart h k W V ε+
        ∑ c∈cubicThetaGramDenominators ε δ,cubicThetaGramDenominatorIntegral h k W V c ε := by
  unfold cubicThetaKloostermanGram cubicThetaGramIdentityPart cubicThetaGramDenominatorIntegral
  simp_rw [mul_add,Finset.mul_sum]
  rw [integral_add (cubicThetaGramIdentity_integrable h k W V hε)
    (integrable_finsetSum _ (fun c _ => cubicThetaGramDenominator_integrable h k W V c hε hδ hV)),
    integral_finsetSum _ (fun c _ => cubicThetaGramDenominator_integrable h k W V c hε hδ hV)]

theorem cubicThetaGramPrimePart_finite_integrals (p h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) :
    cubicThetaGramPrimePart p h k W V ε δ=
      ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => p∣c),
        cubicThetaGramDenominatorIntegral h k W V c ε := by
  unfold cubicThetaGramPrimePart cubicThetaGramDenominatorIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun c _ => cubicThetaGramDenominator_integrable h k W V c hε hδ hV)

theorem cubicThetaGramPrimeFreePart_finite_integrals (p h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) :
    cubicThetaGramPrimeFreePart p h k W V ε δ=
      ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p∣c),
        cubicThetaGramDenominatorIntegral h k W V c ε := by
  unfold cubicThetaGramPrimeFreePart cubicThetaGramDenominatorIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun c _ => cubicThetaGramDenominator_integrable h k W V c hε hδ hV)

theorem cubicThetaKloostermanGram_prime_split (p h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) :
    cubicThetaKloostermanGram h k W V ε δ=
      cubicThetaGramIdentityPart h k W V ε+cubicThetaGramPrimeFreePart p h k W V ε δ+
        cubicThetaGramPrimePart p h k W V ε δ := by
  rw [cubicThetaKloostermanGram_finite_integrals h k W V hε hδ hV,
    cubicThetaGramPrimeFreePart_finite_integrals p h k W V hε hδ hV,
    cubicThetaGramPrimePart_finite_integrals p h k W V hε hδ hV,add_assoc]
  congr 1
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p∣c <;> simp [hc]

end CubicFirstMoment

end

end OAI
