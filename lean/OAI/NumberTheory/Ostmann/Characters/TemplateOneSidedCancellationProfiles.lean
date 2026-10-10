import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationGuards

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval Template Arithmetic
attribute [local instance] Classical.propDecidable
variable {ι σ τ : Type*} [DecidableEq ι] [Fintype σ] [Fintype τ]

def profileGuards (g : σ → Guard ι) (e : τ → Expr ι) (X A B : ℝ) :
    σ ⊕ (τ × Bool) → Guard ι
  | .inl s => g s
  | .inr (t,b) => windowGuards (e t) (X*Real.exp (-B)) (X*Real.exp (-A)) false b

def leafData (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (i : ι) (x : Other i → ℤ) (X A B : ℝ) : HistoryPolynomialData (σ ⊕ (τ × Bool)) τ where
  profile t := .leaf (leaf t).1 ((leaf t).2.1:ℝ)
  scale _ := X
  supports := guardPolynomials (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B) i x
  strict s := (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).strict
  arguments t := argument i x (periodExpression k (leaf t).2.2)
  denominator t := denominator (periodExpression k (leaf t).2.2)

theorem log_ratio_mem_of_window {X v A B : ℝ} (hX : 0 < X)
    (hlo : X*Real.exp (-B) ≤ v) (hhi : v ≤ X*Real.exp (-A)) :
    0 < v ∧ Real.log (X/v) ∈ Set.Icc A B := by
  have hv : 0 < v := (mul_pos hX (Real.exp_pos _)).trans_le hlo
  have hl := Real.log_le_log (mul_pos hX (Real.exp_pos (-B))) hlo
  have hh := Real.log_le_log hv hhi
  rw [Real.log_mul hX.ne' (Real.exp_pos (-B)).ne',Real.log_exp] at hl
  rw [Real.log_mul hX.ne' (Real.exp_pos (-A)).ne',Real.log_exp] at hh
  refine ⟨hv,?_⟩
  rw [Real.log_div hX.ne' hv.ne']
  constructor <;> linarith

omit [Fintype σ] [Fintype τ] in
theorem leafData_ranges [Fintype σ] [Fintype τ] (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (i : ι) (x : Other i → ℤ) {X A B : ℝ} (hX : 0 < X) (hAB : A ≤ B)
    (hg : ∀ s, (g s).expression.Valid)
    (he : ∀ t, (periodExpression k (leaf t).2.2).Valid) (ρ : 𝓢(ℝ,ℂ)) :
    (leafData k g leaf i x X A B).Ranges ρ (fun _ => A) (fun _ => B)
      (Real.exp (B/2)*leafProfileBound ρ) := by
  have hvalid : ∀ s, (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).expression.Valid := by
    intro s
    rcases s with s | ⟨t,b⟩
    · exact hg s
    · cases b <;> exact he t
  have hrange (u : ℝ)
      (hu : polynomialSupport (leafData k g leaf i x X A B).supports
        (leafData k g leaf i x X A B).strict u) (t : τ) :
      0 < ((leafData k g leaf i x X A B).arguments t).eval u /
          (leafData k g leaf i x X A B).denominator t := by
    have hs := (polynomialSupport_iff_realGuards _ i x u hvalid).mp hu
    have hl := hs (.inr (t,false))
    change X*Real.exp (-B) ≤ (argument i x (periodExpression k (leaf t).2.2)).eval u/
      denominator (periodExpression k (leaf t).2.2) at hl
    exact (mul_pos hX (Real.exp_pos _)).trans_le hl
  refine ⟨mul_nonneg (Real.exp_pos _).le (leafProfileBound_pos ρ).le,fun _ => hAB,fun _ => hX,?_,?_,fun _ => le_rfl⟩
  · exact hrange
  · intro u hu t
    have hs := (polynomialSupport_iff_realGuards _ i x u hvalid).mp hu
    have hl := hs (.inr (t,false))
    have hh := hs (.inr (t,true))
    exact (log_ratio_mem_of_window hX hl hh).2

theorem leafData_weight_eq (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (i : ι) (x : Other i → ℤ) (n : ℤ) (X A B : ℝ)
    (hg : ∀ s, HistoryReconstruction.Good (insertCoordinate i x n) (g s).expression)
    (he : ∀ t, HistoryReconstruction.Good (insertCoordinate i x n) (periodExpression k (leaf t).2.2)) :
    (leafData k g leaf i x X A B).weight (𝓕 SchwartzCutoff.psi) (n:ℝ) =
      if ∀ s, (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).holds
          (insertCoordinate i x n) then
        ∏ t, profileValue k X (evalBottom k (insertCoordinate i x n) (leaf t)) else 0 := by
  classical
  have hgood : ∀ s, HistoryReconstruction.Good (insertCoordinate i x n)
      (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).expression := by
    intro s
    rcases s with s | ⟨t,b⟩
    · exact hg s
    · cases b <;> exact he t
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  rw [show polynomialSupport (leafData k g leaf i x X A B).supports
    (leafData k g leaf i x X A B).strict (n:ℝ) ↔ _ from
      polynomialSupport_iff_guards _ i x n hgood]
  split_ifs
  · apply Finset.prod_congr rfl
    intro t ht
    dsimp only [leafData,historyArchimedeanProduct,HistoryProfile.eval,profileValue,evalBottom]
    rw [argument_ratio_eval i x _ n (he t),periodExpression_eval]
  · rfl

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
