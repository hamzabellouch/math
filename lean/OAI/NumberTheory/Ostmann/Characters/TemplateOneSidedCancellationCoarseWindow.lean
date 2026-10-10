import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfiles
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfilesGuards
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularity

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι σ τ : Type*} [DecidableEq ι] [Fintype σ] [Fintype τ]

omit [DecidableEq ι] in
theorem period_upper_from_syntax (k : ℕ) (z : BottomExpression (ι:=ι) k)
    (a : ι → ℤ) {X H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (hs : (periodExpression k z.2.2).syntaxSize ≤ D)
    (hf : (periodExpression k z.2.2).FixedLogBound H)
    (ha : ∀i,|(a i:ℝ)| ≤ Real.exp H)
    (hg : HistoryReconstruction.Good a (periodExpression k z.2.2)) :
    (period k 0 (evalBottom k a z).2.2:ℝ) ≤ X*Real.exp ((D:ℝ)*H) := by
  have hh := (periodExpression k z.2.2).integerEval_abs_le_exp_size hH hf a ha hg
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  have hsize : Real.exp ((periodExpression k z.2.2).syntaxSize*H) ≤ Real.exp ((D:ℝ)*H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hH0)
  have hu := (le_abs_self ((periodExpression k z.2.2).integerEval a:ℝ)).trans (hh.trans hsize)
  simp only [periodExpression_eval,evalBottom] at hu ⊢
  exact hu.trans (le_mul_of_one_le_left (Real.exp_pos _).le hX)

omit [DecidableEq ι] [Fintype σ] [Fintype τ] in
theorem profileGuards_iff_lower (k : ℕ) (g : σ → Guard ι)
    (leaf : τ → BottomExpression (ι:=ι) k) (a : ι → ℤ) {X A Δ W : ℝ}
    (hX : 0 < X)
    (hu : ∀t,(period k 0 (evalBottom k a (leaf t)).2.2:ℝ) ≤ X*Real.exp (-A)) :
    (∀s,(profileGuards g (fun t=>periodExpression k (leaf t).2.2) X A (-Δ+W) s).holds a) ↔
      (∀s,(g s).holds a) ∧ ∀t,(leafLowerGuard k X Δ W (leaf t)).holds a := by
  have hexp : Real.exp (Real.log X+Δ-W)=X*Real.exp (-(-Δ+W)) := by
    rw [show Real.log X+Δ-W=Real.log X+(-(-Δ+W)) by ring,Real.exp_add,Real.exp_log hX]
  constructor
  · intro h
    refine ⟨fun s=>h (.inl s),fun t=>?_⟩
    have hh := h (.inr (t,false))
    change Real.exp (Real.log X+Δ-W) ≤ ((periodExpression k (leaf t).2.2).integerEval a:ℝ)
    rw [hexp]
    exact hh
  · rintro ⟨hg,hl⟩ s
    rcases s with s|⟨t,b⟩
    · exact hg s
    · cases b with
      | false =>
        change X*Real.exp (-(-Δ+W)) ≤ ((periodExpression k (leaf t).2.2).integerEval a:ℝ)
        rw [← hexp]
        exact hl t
      | true =>
        change ((periodExpression k (leaf t).2.2).integerEval a:ℝ) ≤ X*Real.exp (-A)
        simpa only [periodExpression_eval,evalBottom] using hu t

theorem leafData_weight_eq_original_lower (k : ℕ) (g : σ → Guard ι)
    (leaf : τ → BottomExpression (ι:=ι) k) (i : ι) (x : Other i → ℤ) (n : ℤ)
    {X A Δ W : ℝ} (hX : 0 < X)
    (hg : ∀s,HistoryReconstruction.Good (insertCoordinate i x n) (g s).expression)
    (he : ∀t,HistoryReconstruction.Good (insertCoordinate i x n) (periodExpression k (leaf t).2.2))
    (hu : ∀t,(period k 0 (evalBottom k (insertCoordinate i x n) (leaf t)).2.2:ℝ) ≤ X*Real.exp (-A)) :
    (leafData k g leaf i x X A (-Δ+W)).weight (𝓕 SchwartzCutoff.psi) (n:ℝ) =
      if (∀s,(g s).holds (insertCoordinate i x n)) ∧
        (∀t,(leafLowerGuard k X Δ W (leaf t)).holds (insertCoordinate i x n))
      then ∏t,profileValue k X (evalBottom k (insertCoordinate i x n) (leaf t)) else 0 := by
  rw [leafData_weight_eq k g leaf i x n X A (-Δ+W) hg he]
  simp only [profileGuards_iff_lower k g leaf _ hX hu]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
