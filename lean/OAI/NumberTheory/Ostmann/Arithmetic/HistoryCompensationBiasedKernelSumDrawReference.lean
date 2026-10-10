import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumOptional

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
open HistoryPairRepresentatives HistoryPairKernelReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def optionalDrawSymbolicPatternKernel (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(Block p → CommonSample sources origin) →
      Option (PatternReference p V outside l)) :
    ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ :=
  fun p b q => match refs p b with
    | none => 0
    | some r => symbolicKernel mixed r.left r.right r.hs r.ks (r.representative q) (b q).val

omit [DecidableEq ι] in
@[simp] theorem optionalDrawSymbolicPatternKernel_none (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(Block p → CommonSample sources origin) →
      Option (PatternReference p V outside l)) (p : Pattern τ)
    (b : Block p → CommonSample sources origin) (hp : refs p b = none) (q : Block p) :
    optionalDrawSymbolicPatternKernel sources origin τ mixed V outside l refs p b q = 0 := by
  simp only [optionalDrawSymbolicPatternKernel,hp]

omit [DecidableEq ι] in
@[simp] theorem optionalDrawSymbolicPatternKernel_some (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(Block p → CommonSample sources origin) →
      Option (PatternReference p V outside l)) (p : Pattern τ)
    (b : Block p → CommonSample sources origin) (r : PatternReference p V outside l)
    (hp : refs p b = some r) (q : Block p) :
    optionalDrawSymbolicPatternKernel sources origin τ mixed V outside l refs p b q =
      symbolicKernel mixed r.left r.right r.hs r.ks (r.representative q) (b q).val := by
  simp only [optionalDrawSymbolicPatternKernel,hp]

omit [DecidableEq ι] in
theorem optionalDrawSymbolicPatternKernel_bounds [_decidableEqIndex : DecidableEq ι]
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(Block p → CommonSample sources origin) →
      Option (PatternReference p V outside l))
    (p : Pattern τ) (b : Block p → CommonSample sources origin) (q : Block p) :
    0 ≤ optionalDrawSymbolicPatternKernel sources origin τ mixed V outside l refs p b q ∧
      optionalDrawSymbolicPatternKernel sources origin τ mixed V outside l refs p b q ≤
        2/((b q).val:ℝ) := by
  cases hp : refs p b with
  | none =>
    rw [optionalDrawSymbolicPatternKernel_none sources origin τ mixed V outside l refs p b hp]
    exact ⟨le_rfl,div_nonneg (by norm_num) (Nat.cast_nonneg _)⟩
  | some r =>
    rw [optionalDrawSymbolicPatternKernel_some sources origin τ mixed V outside l refs p b r hp]
    exact symbolicKernel_le_two_div mixed r.left r.right r.hs r.ks (r.representative q)
      (b q).val (commonSample_prime sources origin (b q))

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem selected_optionalDrawSymbolicKernelSum_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
      Option (PatternReference p V outside l))
    (mask : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → ℝ)
    (hm : ∀p b,0 ≤ mask p b ∧ mask p b ≤ 1) :
    biasedKernelSum C.sources origin τ
      (optionalDrawSymbolicPatternKernel C.sources origin τ mixed V outside l refs) mask ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (origin i)) q :=
  selected_biasedKernelSum_le C origin τ _ mask
    (optionalDrawSymbolicPatternKernel_bounds C.sources origin τ mixed V outside l refs) hm

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
