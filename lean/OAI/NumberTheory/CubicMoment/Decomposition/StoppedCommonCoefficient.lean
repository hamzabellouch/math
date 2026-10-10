import OAI.NumberTheory.CubicMoment.Estimates.CommonHeightCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorRows

namespace OAI

/-! The common-factor coefficient is an actual shortened stopped row
with a fixed cubic numerator. The normalized Gauss factors cancel exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma common_gramUntwist_eq (β : Eisenstein → ℂ) (k m a : Eisenstein)
    (hk : primary k) (ha : primary a) (has : Squarefree a) :
    gramUntwist (commonBlockCoefficient (fun b => star (β b*gauss b)) k m) a =
      gauss k*(β (k*a)*star (cubicSymbol a (k*m))) := by
  have hg : gauss a*star (gauss a) = 1 := by
    simpa only [ite_eq_left has] using gauss_mul_star_squarefree ha
  unfold gramUntwist commonBlockCoefficient
  simp only [star_mul,star_star]
  rw [gauss_mul hk ha,cubicSymbol_mul_upper ha k m,star_mul]
  calc
    _ = (gauss a*star (gauss a))*
        (gauss k*(β (k*a)*(star (cubicSymbol a k)*star (cubicSymbol a m)))) := by ring
    _ = _ := by rw [hg,one_mul]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stopped_residualRows_eq_slice (X l b : ℝ) (e k : Eisenstein) (hk : primary k) :
    residualRows (stoppedIntervalSupport ι X l b e) k = stoppedDivisorSlice ι X l b e k := by
  ext a
  rw [mem_residualRows (primary_ne_zero hk)]
  constructor
  · exact stoppedDivisorSlice_complete X l b e hk a
  · exact fun ha => (Finset.mem_filter.mp ha).2

lemma stopped_common_coefficient_eq (X w z l b : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e k m : Eisenstein) (hk : primary k)
    {a : Eisenstein} (ha : a ∈ residualRows (stoppedIntervalSupport ι X l b e) k) :
    gramUntwist (commonBlockCoefficient (fun n =>
        star (stoppedRowCoefficient X w z 0 W selected n*gauss n)) k m) a =
      gauss k*(stoppedRowCoefficient X w z 0 W selected (k*a)*
        star (cubicSymbol a (k*m))) := by
  have hslice : a ∈ stoppedDivisorSlice ι X l b e k := by
    rwa [stopped_residualRows_eq_slice X l b e k hk] at ha
  have hs := stoppedDivisorSlice_spec X l b e k hslice
  exact common_gramUntwist_eq _ k m a hk hs.1 hs.2.1

lemma stopped_common_character_sum (X w z l b : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e k m v : Eisenstein) (hk : primary k) :
    (∑ a ∈ residualRows (stoppedIntervalSupport ι X l b e) k,
      gramUntwist (commonBlockCoefficient (fun n =>
        star (stoppedRowCoefficient X w z 0 W selected n*gauss n)) k m) a*cubicSymbol a v) =
      gauss k*∑ a ∈ stoppedDivisorSlice ι X l b e k,
        stoppedRowCoefficient X w z 0 W selected (k*a)*cubicSymbol a ((k*m)^2*v) := by
  rw [Finset.mul_sum,←stopped_residualRows_eq_slice X l b e k hk]
  apply Finset.sum_congr rfl
  intro a ha
  have hslice : a ∈ stoppedDivisorSlice ι X l b e k := by
    rwa [←stopped_residualRows_eq_slice X l b e k hk]
  have hs := stoppedDivisorSlice_spec X l b e k hslice
  rw [stopped_common_coefficient_eq X w z l b W selected e k m hk ha,
    cubicSymbol_mul_upper hs.1 ((k*m)^2) v,cubicSymbol_pow_upper hs.1 (k*m) 2,
    cubicSymbol_sq_eq_star hs.1 (k*m)]
  ring


lemma coprimeDispersionGram_congr_coefficients (S : Finset Eisenstein)
    (β γ : Eisenstein → ℂ) (hβ : ∀ a ∈ S, β a = γ a)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeDispersionGram S β u W A = coprimeDispersionGram S γ u W A := by
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [dispersionAmplitude,hβ a ha,hβ b hb]

lemma coprimeDispersionGram_unit_scalar (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {c : ℂ} (hc : ‖c‖ = 1) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    coprimeDispersionGram S (fun a => c*β a) u W A = coprimeDispersionGram S β u W A := by
  have hcc : c*star c = 1 := by
    simpa only [starRingEnd_apply,hc,one_pow,Complex.ofReal_one] using Complex.mul_conj' c
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · simp only [dispersionAmplitude,star_mul]
    calc
      _ = (c*star c)*((β a*normTwist u a*gauss a)*
          (star (β b)*star (normTwist u b)*star (gauss b))*primaryCharacterGram b a W A) := by ring
      _ = _ := by rw [hcc,one_mul]; ring
  · rfl

lemma stopped_common_gram_eq (X w z l b : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e k m : Eisenstein)
    (hk : primary k) (hks : Squarefree k) (u : ℝ) (Φ : ℝ → ℂ) (A : ℝ) :
    let S := stoppedIntervalSupport ι X l b e
    let β := stoppedRowCoefficient X w z 0 W selected
    coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun n => star (dispersionAmplitude β u n)) k m) Φ A =
      coprimeDispersionGram (stoppedDivisorSlice ι X l b e k)
        (fun a => β (k*a)*star (cubicSymbol a (k*m))) u Φ A := by
  dsimp only
  have hS : ∀ a ∈ stoppedIntervalSupport ι X l b e, primary a ∧ Squarefree a := by
    intro a ha
    have hs := stoppedIntervalSupport_spec X l b e ha
    exact ⟨hs.1,hs.2.1⟩
  rw [common_coprime_height_eq _ _ k m hk hS]
  calc
    _ = coprimeDispersionGram (residualRows (stoppedIntervalSupport ι X l b e) k)
        (fun a => gauss k*(stoppedRowCoefficient X w z 0 W selected (k*a)*
          star (cubicSymbol a (k*m)))) u Φ A :=
      coprimeDispersionGram_congr_coefficients _ _ _
        (fun a ha => stopped_common_coefficient_eq X w z l b W selected e k m hk ha) _ _ _
    _ = coprimeDispersionGram (residualRows (stoppedIntervalSupport ι X l b e) k)
        (fun a => stoppedRowCoefficient X w z 0 W selected (k*a)*
          star (cubicSymbol a (k*m))) u Φ A :=
      coprimeDispersionGram_unit_scalar _ _ (by simp only [norm_gauss hk,ite_eq_left hks]) _ _ _
    _ = _ := by rw [stopped_residualRows_eq_slice X l b e k hk]

end CubicFirstMoment

end

end OAI
