import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSymbolic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
open HistoryPairRepresentatives HistoryPairKernelReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure PatternReference {τ : ι → ℕ} (p : Pattern τ) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) where
  left : History l
  right : History l
  hs : left.Supported V outside
  ks : right.Supported V outside
  representative : Block p → Representative left right

def optionalSymbolicPatternKernel (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,Option (PatternReference p V outside l)) :
    ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ :=
  fun p b q => match refs p with
    | none => 0
    | some r => symbolicKernel mixed r.left r.right r.hs r.ks (r.representative q) (b q).val

omit [DecidableEq ι] in
@[simp] theorem optionalSymbolicPatternKernel_none (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,Option (PatternReference p V outside l)) (p : Pattern τ)
    (hp : refs p = none) (b : Block p → CommonSample sources origin) (q : Block p) :
    optionalSymbolicPatternKernel sources origin τ mixed V outside l refs p b q = 0 := by
  simp only [optionalSymbolicPatternKernel,hp]

omit [DecidableEq ι] in
@[simp] theorem optionalSymbolicPatternKernel_some (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,Option (PatternReference p V outside l)) (p : Pattern τ)
    (r : PatternReference p V outside l) (hp : refs p = some r)
    (b : Block p → CommonSample sources origin) (q : Block p) :
    optionalSymbolicPatternKernel sources origin τ mixed V outside l refs p b q =
      symbolicKernel mixed r.left r.right r.hs r.ks (r.representative q) (b q).val := by
  simp only [optionalSymbolicPatternKernel,hp]

omit [DecidableEq ι] in
theorem optionalSymbolicPatternKernel_bounds (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,Option (PatternReference p V outside l))
    (p : Pattern τ) (b : Block p → CommonSample sources origin) (q : Block p) :
    0 ≤ optionalSymbolicPatternKernel sources origin τ mixed V outside l refs p b q ∧
      optionalSymbolicPatternKernel sources origin τ mixed V outside l refs p b q ≤
        2/((b q).val:ℝ) := by
  cases hp : refs p with
  | none =>
    rw [optionalSymbolicPatternKernel_none sources origin τ mixed V outside l refs p hp]
    exact ⟨le_rfl,div_nonneg (by norm_num) (Nat.cast_nonneg _)⟩
  | some r =>
    rw [optionalSymbolicPatternKernel_some sources origin τ mixed V outside l refs p r hp]
    exact symbolicKernel_le_two_div mixed r.left r.right r.hs r.ks (r.representative q)
      (b q).val (commonSample_prime sources origin (b q))

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem selected_optionalSymbolicKernelSum_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,Option (PatternReference p V outside l))
    (mask : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → ℝ)
    (hm : ∀p b,0 ≤ mask p b ∧ mask p b ≤ 1) :
    biasedKernelSum C.sources origin τ
      (optionalSymbolicPatternKernel C.sources origin τ mixed V outside l refs) mask ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (origin i)) q :=
  selected_biasedKernelSum_le C origin τ _ mask
    (optionalSymbolicPatternKernel_bounds C.sources origin τ mixed V outside l refs) hm

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
