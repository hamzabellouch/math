import OAI.NumberTheory.CubicMoment.Estimates.CommonVarianceDecomposition

namespace OAI

/-! Separate the coprime term from the exact common-factor expansion.
Only nonunit common factors remain, so roughness shortens every row. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonGramBlock (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) (k : Eisenstein) : ℂ :=
  ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k, if IsCoprime a b then
    u (k*a)*star (u (k*b))*primaryCharacterGram (k*a) (k*b) W Z else 0

lemma commonGramBlock_moebius (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) {k : Eisenstein} (hk : primary k) (hsk : Squarefree k) :
    commonGramBlock S u W Z k = ∑ s ∈ (primaryPrimeFactors k).powerset,
      let m := ∏ p ∈ s, p
      (idealMoebius m:ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m) := by
  have hr := residualRows_primary hk hS
  unfold commonGramBlock
  calc
    _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          let m := ∏ p ∈ s, p
          (idealMoebius m:ℂ)*(if IsCoprime a b then commonBlockCoefficient u k m a*
            star (commonBlockCoefficient u k m b)*primaryCharacterGram a b W (Z/norm m)
            else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : IsCoprime a b
      · simp only [ite_eq_left hab]
        rw [primaryCharacterGram_common_factor hk hsk (hr a ha).1 (hr b hb).1 W hW hW' hZ,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [commonBlockCoefficient,mixedSymbol,star_mul]
        ring
      · simp [hab]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := residualRows S k) (t := (primaryPrimeFactors k).powerset)]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [coprimeGramForm,Finset.mul_sum]

 theorem primaryMass_sub_coprime_common (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primarySmoothedSieveMass S u W Z-coprimeGramForm S u W Z =
      ∑ k ∈ (commonRowFactors S).filter (· ≠ 1), commonGramBlock S u W Z k := by
  let F (a b : Eisenstein) : ℂ := if IsCoprime a b then 0 else
    u a*star (u b)*primaryCharacterGram a b W Z
  have hdiff : primarySmoothedSieveMass S u W Z-coprimeGramForm S u W Z =
      ∑ a ∈ S, ∑ b ∈ S, F a b := by
    rw [primarySmoothedSieveMass_gram S (fun a ha => (hS a ha).1) u W hW hW' hZ]
    unfold coprimeGramForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : IsCoprime a b <;> simp [F,hab]
  rw [hdiff,common_factor_matrix_decomposition S hS F,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hkS
  have hk := commonRowFactors_spec hS hkS
  by_cases hk1 : k = 1
  · subst k
    simp only [ne_eq,not_true_eq_false,ite_false,F,one_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : IsCoprime a b <;> simp [hab]
  · rw [ite_eq_left hk1]
    unfold commonGramBlock
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : IsCoprime a b
    · have hnot : ¬IsCoprime (k*a) (k*b) := by
        intro hc
        exact hk1 (primary_unit_eq_one
          (hc.isUnit_of_dvd' (dvd_mul_right k a) (dvd_mul_right k b)) hk.1)
      simp only [ite_eq_left hab,F,ite_eq_right hnot]
    · simp only [ite_eq_right hab]

lemma divisorCoprimeDispersionGram_eq_coprimeGram (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    divisorCoprimeDispersionGram d S β u W A =
      coprimeGramForm S (divisorGramCoefficient d β u) W (A/(norm d)^2) := by
  unfold divisorCoprimeDispersionGram coprimeDispersionGram coprimeGramForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_left hab.symm,divisorGramCoefficient,
      dispersionAmplitude,divisorTwistedCoefficient,star_mul,star_star]
    ring
  · simp only [ite_eq_right hab,ite_eq_right (show ¬ IsCoprime b a from fun hc => hab hc.symm)]

 theorem divisorVariance_sub_coprime_common {d : Eisenstein} (hd : primary d)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d S β u W A-divisorCoprimeDispersionGram d S β u W A =
      ∑ k ∈ (commonRowFactors S).filter (· ≠ 1),
        commonGramBlock S (divisorGramCoefficient d β u) W (A/(norm d)^2) k := by
  have hdN := norm_pos_of_ne_zero (primary_ne_zero hd)
  rw [divisorDispersionVariance_eq_primaryMass hd S (fun a ha => (hS a ha).1)
    β u W hW hW' hA,divisorCoprimeDispersionGram_eq_coprimeGram]
  exact primaryMass_sub_coprime_common S hS _ W hW hW' (by positivity)

end CubicFirstMoment

end

end OAI
