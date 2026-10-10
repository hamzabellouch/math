import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationLongData

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

def gatedData {σ τ : Type*} (b : Bool) (d : HistoryPolynomialData σ τ) :
    HistoryPolynomialData (Option σ) τ where
  profile := d.profile
  scale := d.scale
  supports := Option.elim' (Polynomial.C (if b then 0 else 1)) d.supports
  strict := Option.elim' false d.strict
  arguments := d.arguments
  denominator := d.denominator

theorem gatedData_support {σ τ : Type*} (b : Bool) (d : HistoryPolynomialData σ τ)
    (x : ℝ) :
    polynomialSupport (gatedData b d).supports (gatedData b d).strict x ↔
      b=true ∧ polynomialSupport d.supports d.strict x := by
  cases b <;> simp [polynomialSupport,gatedData,Option.forall]
  rfl

theorem gatedData_weight {σ τ : Type*} [Fintype σ] [Fintype τ]
    (b : Bool) (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (gatedData b d).weight ρ x = if b then d.weight ρ x else 0 := by
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  rw [gatedData_support]
  cases b <;> simp [gatedData,historyArchimedeanProduct]

theorem gatedData_ranges {σ τ : Type*} [Fintype σ] [Fintype τ]
    (b : Bool) (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ))
    {A B : τ → ℝ} {M : ℝ} (h : d.Ranges ρ A B M) :
    (gatedData b d).Ranges ρ A B M := by
  refine ⟨h.nonneg,h.ordered,h.scale_pos,?_,?_,h.bound⟩
  · intro x hx t
    exact h.argument_pos x ((gatedData_support b d x).mp hx).2 t
  · intro x hx t
    exact h.log_range x ((gatedData_support b d x).mp hx).2 t

theorem gatedData_degreeCost {σ τ : Type*} [Fintype σ] [Fintype τ]
    (b : Bool) (d : HistoryPolynomialData σ τ) :
    (gatedData b d).degreeCost=d.degreeCost := by
  cases b <;> simp [HistoryPolynomialData.degreeCost,gatedData,Fintype.sum_option]

theorem conjugateData_degreeCost {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) : (conjugateData d).degreeCost=d.degreeCost := rfl

theorem multiplyData_degreeCost {σ τ σ' τ' : Type*} [Fintype σ] [Fintype τ]
    [Fintype σ'] [Fintype τ'] (d : HistoryPolynomialData σ τ)
    (e : HistoryPolynomialData σ' τ') :
    (multiplyData d e).degreeCost+1=d.degreeCost+e.degreeCost := by
  simp only [HistoryPolynomialData.degreeCost,multiplyData,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  omega

theorem longRatioData_degreeCost (b₀ : ℝ) : (longRatioData b₀).degreeCost ≤ 7 := by
  simp only [HistoryPolynomialData.degreeCost,longRatioData,Fintype.sum_bool,
    Fintype.sum_unique,Bool.false_eq_true,ite_false,ite_true]
  have h1 := Polynomial.natDegree_sub_le (Polynomial.X:Polynomial ℝ) (Polynomial.C (2*b₀))
  have h2 := Polynomial.natDegree_sub_le (Polynomial.C b₀) (Polynomial.X:Polynomial ℝ)
  simp only [Polynomial.natDegree_X,Polynomial.natDegree_C] at *
  omega

theorem crossHistoryData_degreeCost {σ τ : Type*} [Fintype σ] [Fintype τ]
    (b₀ : ℝ) (d e : HistoryPolynomialData σ τ) :
    (crossHistoryData b₀ d e).degreeCost ≤ d.degreeCost+e.degreeCost+5 := by
  have h1 := multiplyData_degreeCost (longRatioData b₀) (multiplyData d (conjugateData e))
  have h2 := multiplyData_degreeCost d (conjugateData e)
  rw [conjugateData_degreeCost] at h2
  have h3 := longRatioData_degreeCost b₀
  change (multiplyData (longRatioData b₀) (multiplyData d (conjugateData e))).degreeCost ≤ _
  omega

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
