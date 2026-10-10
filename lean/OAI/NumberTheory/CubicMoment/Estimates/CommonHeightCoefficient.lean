import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoprimeDispersion
import OAI.NumberTheory.CubicMoment.Estimates.CommonGramRemainder

namespace OAI

/-! Remove the normalized Gauss factor without changing coefficient energy.
This permits the proved dispersion estimate to act on the literal
common-factor rows, with their original height dependence. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def gramUntwist (v : Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  star (v a)*star (gauss a)

lemma gramUntwist_norm {a : Eisenstein} (ha : primary a) (hs : Squarefree a)
    (v : Eisenstein → ℂ) : ‖gramUntwist v a‖ = ‖v a‖ := by
  simp only [gramUntwist,norm_mul,norm_star,norm_gauss ha,ite_eq_left hs,mul_one]

lemma gramUntwist_amplitude {a : Eisenstein} (ha : primary a) (hs : Squarefree a)
    (v : Eisenstein → ℂ) (u : ℝ) :
    star (dispersionAmplitude (gramUntwist v) u a) = v a*star (normTwist u a) := by
  have hg : gauss a*star (gauss a) = 1 := by
    simpa only [ite_eq_left hs] using gauss_mul_star_squarefree ha
  simp only [dispersionAmplitude,gramUntwist,star_mul,star_star]
  calc
    _ = (v a*star (normTwist u a))*(gauss a*star (gauss a)) := by ring
    _ = _ := by rw [hg,mul_one]

lemma coprimeGramForm_height_eq (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm S (fun a => v a*star (normTwist u a)) W A =
      coprimeDispersionGram S (gramUntwist v) u W A := by
  unfold coprimeGramForm coprimeDispersionGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_left hab.symm]
    rw [← gramUntwist_amplitude (hS a ha).1 (hS a ha).2,
      ← gramUntwist_amplitude (hS b hb).1 (hS b hb).2,star_star]
    ring
  · simp only [ite_eq_right hab,ite_eq_right (fun h : IsCoprime b a => hab h.symm)]

lemma coprimeGramForm_unit_scalar (S : Finset Eisenstein) (v : Eisenstein → ℂ)
    {c : ℂ} (hc : ‖c‖ = 1) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm S (fun a => c*v a) W A = coprimeGramForm S v W A := by
  have hcc : c*star c = 1 := by
    simpa only [starRingEnd_apply,hc,one_pow,Complex.ofReal_one] using Complex.mul_conj' c
  unfold coprimeGramForm
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · simp only [star_mul]
    calc
      _ = (c*star c)*(v a*star (v b)*primaryCharacterGram a b W A) := by ring
      _ = _ := by rw [hcc,one_mul]
  · rfl

lemma commonBlockCoefficient_height (β : Eisenstein → ℂ) (k m : Eisenstein)
    {a : Eisenstein} (hk : primary k) (ha : primary a) (u : ℝ) :
    commonBlockCoefficient (fun b => star (dispersionAmplitude β u b)) k m a =
      star (normTwist u k)*
        (commonBlockCoefficient (fun b => star (β b*gauss b)) k m a *
          star (normTwist u a)) := by
  simp only [commonBlockCoefficient,dispersionAmplitude,
    normTwist_mul u (primary_ne_zero hk) (primary_ne_zero ha),star_mul]
  ring

lemma common_coprime_height_eq (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (k m : Eisenstein) (hk : primary k)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β u b)) k m) W A =
      coprimeDispersionGram (residualRows S k)
        (gramUntwist (commonBlockCoefficient (fun b => star (β b*gauss b)) k m)) u W A := by
  have hr := residualRows_primary hk hS
  calc
    _ = coprimeGramForm (residualRows S k) (fun a => star (normTwist u k)*
        (commonBlockCoefficient (fun b => star (β b*gauss b)) k m a *
          star (normTwist u a))) W A := by
      unfold coprimeGramForm
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [commonBlockCoefficient_height β k m hk (hr a ha).1,
        commonBlockCoefficient_height β k m hk (hr b hb).1]
    _ = _ := (coprimeGramForm_unit_scalar _ _ (by simp) W A).trans
      (coprimeGramForm_height_eq _ hr _ u W A)

end CubicFirstMoment

end

end OAI
