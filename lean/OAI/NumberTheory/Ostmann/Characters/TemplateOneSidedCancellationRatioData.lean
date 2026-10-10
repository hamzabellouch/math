import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCoreData

namespace OAI

open Erdos970

noncomputable section
open scoped SchwartzMap BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def ratioExpressionData (i : ι) (x : Other i → ℤ) (e : Expr ι) (T A B : ℝ) :
    HistoryPolynomialData Bool Unit where
  profile _ := .ratio
  scale _ := Real.exp T
  supports := guardPolynomials (windowGuards e (Real.exp T*Real.exp (-B))
    (Real.exp T*Real.exp (-A)) false) i x
  strict b := (windowGuards e (Real.exp T*Real.exp (-B))
    (Real.exp T*Real.exp (-A)) false b).strict
  arguments _ := argument i x e
  denominator _ := denominator e

theorem ratioExpressionData_ranges (i : ι) (x : Other i → ℤ) (e : Expr ι)
    (T A B : ℝ) (hAB : A ≤ B) (he : e.Valid) (ρ : 𝓢(ℝ,ℂ)) :
    (ratioExpressionData i x e T A B).Ranges ρ (fun _=>A) (fun _=>B) (Real.exp B) := by
  have hg : ∀b,(windowGuards e (Real.exp T*Real.exp (-B))
      (Real.exp T*Real.exp (-A)) false b).expression.Valid := by
    intro b; cases b <;> exact he
  have hw (y : ℝ) (hy : polynomialSupport (ratioExpressionData i x e T A B).supports
      (ratioExpressionData i x e T A B).strict y) :
      0 < (argument i x e).eval y/denominator e ∧
      Real.log (Real.exp T/((argument i x e).eval y/denominator e)) ∈ Set.Icc A B := by
    have hh := (polynomialSupport_iff_realGuards _ i x y hg).mp hy
    exact log_ratio_mem_of_window (Real.exp_pos _) (hh false) (hh true)
  exact ⟨(Real.exp_pos _).le,fun _=>hAB,fun _=>Real.exp_pos _,
    fun y hy _=>(hw y hy).1,fun y hy _=>(hw y hy).2,fun _=>le_rfl⟩

theorem ratioExpressionData_weight (i : ι) (x : Other i → ℤ) (e : Expr ι)
    (T A B : ℝ) (n : ℤ) (hg : HistoryReconstruction.Good (insertCoordinate i x n) e)
    (ρ : 𝓢(ℝ,ℂ)) :
    (ratioExpressionData i x e T A B).weight ρ (n:ℝ) =
      if Real.exp T*Real.exp (-B) ≤ (e.integerEval (insertCoordinate i x n):ℝ) ∧
          (e.integerEval (insertCoordinate i x n):ℝ) ≤ Real.exp T*Real.exp (-A)
      then (Real.exp T:ℂ)/(e.integerEval (insertCoordinate i x n):ℂ) else 0 := by
  have hgood : ∀b,HistoryReconstruction.Good (insertCoordinate i x n)
      (windowGuards e (Real.exp T*Real.exp (-B)) (Real.exp T*Real.exp (-A)) false b).expression := by
    intro b; cases b <;> exact hg
  have hs := polynomialSupport_iff_guards (windowGuards e (Real.exp T*Real.exp (-B))
    (Real.exp T*Real.exp (-A)) false) i x n hgood
  have hw := windowGuards_holds e (Real.exp T*Real.exp (-B))
    (Real.exp T*Real.exp (-A)) false (insertCoordinate i x n)
  unfold HistoryPolynomialData.weight polynomialHistoryWeight
  simp only [ratioExpressionData]
  simp only [hs,hw,Bool.false_eq_true,ite_false]
  split_ifs with h
  · have hp : 0 < (e.integerEval (insertCoordinate i x n):ℝ) :=
      (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le h.1
    simp only [historyArchimedeanProduct,HistoryProfile.eval,
      Fintype.prod_unique]
    rw [argument_ratio_eval i x e n hg,historyRatioProfile_eq_ratio T _ hp]
    push_cast
    rfl
  · rfl

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
