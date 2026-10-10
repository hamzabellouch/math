import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCrossData

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

def longRatioData (b₀ : ℝ) : HistoryPolynomialData Bool Unit where
  profile _ := .ratio
  scale _ := b₀
  supports b := if b then Polynomial.X-Polynomial.C (2*b₀) else Polynomial.C b₀-Polynomial.X
  strict _ := false
  arguments _ := Polynomial.X
  denominator _ := 1

theorem longRatioData_support (b₀ x : ℝ) :
    polynomialSupport (longRatioData b₀).supports (longRatioData b₀).strict x ↔
      b₀ ≤ x ∧ x ≤ 2*b₀ := by
  simp only [polynomialSupport,longRatioData,Bool.forall_bool,Bool.false_eq_true,
    ite_false,ite_true,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem longRatioData_weight (ρ : 𝓢(ℝ,ℂ)) (b₀ x : ℝ) :
    (longRatioData b₀).weight ρ x =
      if b₀ ≤ x ∧ x ≤ 2*b₀ then historyRatioProfile (Real.log (b₀/x)) else 0 := by
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  rw [longRatioData_support]
  simp only [historyArchimedeanProduct,longRatioData,
    HistoryProfile.eval,Polynomial.eval_X,div_one,Fintype.prod_unique]
  split_ifs <;> rfl

theorem longRatioData_ranges (ρ : 𝓢(ℝ,ℂ)) {b₀ : ℝ} (hb : 0 < b₀) :
    (longRatioData b₀).Ranges ρ (fun _ => -Real.log 2) (fun _ => 0) 1 := by
  refine ⟨by norm_num,?_,fun _ => hb,?_,?_,?_⟩
  · intro u
    have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx u
    have h := (longRatioData_support b₀ x).mp hx
    simpa only [longRatioData,Polynomial.eval_X,div_one] using hb.trans_le h.1
  · intro x hx u
    simpa only [longRatioData,Polynomial.eval_X,div_one] using
      longReciprocal_log_range hb ((longRatioData_support b₀ x).mp hx)
  · intro u
    simp only [longRatioData,HistoryProfile.bound,Real.exp_zero,le_refl]

def crossHistoryData {σ τ : Type*} (b₀ : ℝ) (d e : HistoryPolynomialData σ τ) :
    HistoryPolynomialData (Bool ⊕ (σ ⊕ σ)) (Unit ⊕ (τ ⊕ τ)) :=
  multiplyData (longRatioData b₀) (multiplyData d (conjugateData e))

theorem crossHistoryData_weight {σ τ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) {b₀ : ℝ} (hb : 0 < b₀) (E : ℝ)
    (d e : HistoryPolynomialData σ τ) (Q a n : ℕ) :
    (longProgressionMajorant E b₀ Q a n:ℂ)*
      d.weight ρ ((Q*n+a:ℕ):ℝ)*conj (e.weight ρ ((Q*n+a:ℕ):ℝ)) =
      (E/b₀:ℂ)*(crossHistoryData b₀ d e).weight ρ ((Q*n+a:ℕ):ℝ) := by
  rw [longProgressionMajorant_normalization hb]
  simp only [crossHistoryData,multiplyData_weight,conjugateData_weight,longRatioData_weight]
  ring

theorem crossHistoryData_ranges {σ τ : Type*} [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) {b₀ : ℝ} (hb : 0 < b₀)
    (d e : HistoryPolynomialData σ τ) {A B : τ → ℝ} {M : ℝ}
    (hd : d.Ranges ρ A B M) (he : e.Ranges ρ A B M) :
    (crossHistoryData b₀ d e).Ranges ρ
      (Sum.elim (fun _ => -Real.log 2) (Sum.elim A A))
      (Sum.elim (fun _ => 0) (Sum.elim B B)) (max 1 M) := by
  exact multiplyData_ranges _ _ ρ
    (ranges_mono_bound _ ρ (longRatioData_ranges ρ hb) (le_max_left _ _))
    (multiplyData_ranges _ _ ρ (ranges_mono_bound _ ρ hd (le_max_right _ _))
      (conjugateData_ranges _ ρ (ranges_mono_bound _ ρ he (le_max_right _ _))))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
