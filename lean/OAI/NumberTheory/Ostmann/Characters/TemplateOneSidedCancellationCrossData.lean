import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapMajorant
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfiles

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

def conjugateProfile : HistoryProfile → HistoryProfile
  | .leaf b v => .leaf (!b) v
  | .ratio => .ratio

theorem conjugateProfile_eval (p : HistoryProfile) (ρ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (conjugateProfile p).eval ρ x=conj (p.eval ρ x) := by
  cases p with
  | leaf b v => cases b <;> simp [conjugateProfile,HistoryProfile.eval,historyLeafProfile]
  | ratio =>
    simp only [conjugateProfile,HistoryProfile.eval,historyRatioProfile]
    exact (Complex.conj_ofReal _).symm

theorem conjugateProfile_bound (p : HistoryProfile) (ρ : 𝓢(ℝ,ℂ)) (B : ℝ) :
    (conjugateProfile p).bound ρ B=p.bound ρ B := by cases p <;> rfl

def conjugateData {σ τ : Type*} (d : HistoryPolynomialData σ τ) : HistoryPolynomialData σ τ :=
  { d with profile := fun t => conjugateProfile (d.profile t) }

def multiplyData {σ τ σ' τ' : Type*}
    (d : HistoryPolynomialData σ τ) (e : HistoryPolynomialData σ' τ') :
    HistoryPolynomialData (σ ⊕ σ') (τ ⊕ τ') where
  profile := Sum.elim d.profile e.profile
  scale := Sum.elim d.scale e.scale
  supports := Sum.elim d.supports e.supports
  strict := Sum.elim d.strict e.strict
  arguments := Sum.elim d.arguments e.arguments
  denominator := Sum.elim d.denominator e.denominator

theorem conjugateData_weight {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (conjugateData d).weight ρ x=conj (d.weight ρ x) := by
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  change (if polynomialSupport d.supports d.strict x then _ else 0)=_
  split_ifs <;> simp only [historyArchimedeanProduct,conjugateData,conjugateProfile_eval,map_prod,map_zero]

theorem multiplyData_weight {σ τ σ' τ' : Type*} [Fintype σ] [Fintype τ]
    [Fintype σ'] [Fintype τ'] (d : HistoryPolynomialData σ τ) (e : HistoryPolynomialData σ' τ')
    (ρ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (multiplyData d e).weight ρ x=d.weight ρ x*e.weight ρ x := by
  have hs : polynomialSupport (multiplyData d e).supports (multiplyData d e).strict x ↔
      polynomialSupport d.supports d.strict x ∧ polynomialSupport e.supports e.strict x := by
    simp [polynomialSupport,multiplyData,Sum.forall]
    rfl
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  simp only [hs]
  by_cases hd : polynomialSupport d.supports d.strict x <;>
    by_cases he : polynomialSupport e.supports e.strict x <;>
    simp [hd,he,historyArchimedeanProduct,multiplyData,Fintype.prod_sum_type]

theorem conjugateData_ranges {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {M : ℝ}
    (h : d.Ranges ρ A B M) : (conjugateData d).Ranges ρ A B M := by
  exact ⟨h.nonneg,h.ordered,h.scale_pos,h.argument_pos,h.log_range,
    fun i => by simpa only [conjugateData,conjugateProfile_bound] using h.bound i⟩

theorem ranges_mono_bound {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {M M' : ℝ}
    (h : d.Ranges ρ A B M) (hM : M ≤ M') : d.Ranges ρ A B M' := by
  exact ⟨h.nonneg.trans hM,h.ordered,h.scale_pos,h.argument_pos,h.log_range,
    fun i => (h.bound i).trans hM⟩

theorem multiplyData_ranges {σ τ σ' τ' : Type*} [Fintype σ] [Fintype τ]
    [Fintype σ'] [Fintype τ'] (d : HistoryPolynomialData σ τ) (e : HistoryPolynomialData σ' τ')
    (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {A' B' : τ' → ℝ} {M : ℝ}
    (hd : d.Ranges ρ A B M) (he : e.Ranges ρ A' B' M) :
    (multiplyData d e).Ranges ρ (Sum.elim A A') (Sum.elim B B') M := by
  have hs (x : ℝ) : polynomialSupport (multiplyData d e).supports (multiplyData d e).strict x ↔
      polynomialSupport d.supports d.strict x ∧ polynomialSupport e.supports e.strict x := by
    simp [polynomialSupport,multiplyData,Sum.forall]
    rfl
  refine ⟨hd.nonneg,?_,?_,?_,?_,?_⟩
  · intro i; cases i with | inl i => exact hd.ordered i | inr i => exact he.ordered i
  · intro i; cases i with | inl i => exact hd.scale_pos i | inr i => exact he.scale_pos i
  · intro x hx i
    cases i with
    | inl i => exact hd.argument_pos x (hs x |>.mp hx).1 i
    | inr i => exact he.argument_pos x (hs x |>.mp hx).2 i
  · intro x hx i
    cases i with
    | inl i => exact hd.log_range x (hs x |>.mp hx).1 i
    | inr i => exact he.log_range x (hs x |>.mp hx).2 i
  · intro i; cases i with | inl i => exact hd.bound i | inr i => exact he.bound i

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
