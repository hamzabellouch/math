import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
open HistoryPairRepresentatives HistoryPairKernelReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

def symbolicPatternKernel (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (left right : Pattern τ → History l)
    (hs : ∀p,(left p).Supported V outside) (ks : ∀p,(right p).Supported V outside)
    (representative : ∀p,Block p → Representative (left p) (right p)) :
    ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ :=
  fun p b q => symbolicKernel mixed (left p) (right p) (hs p) (ks p) (representative p q) (b q).val

omit [DecidableEq ι] in
theorem symbolicPatternKernel_bounds (sources : SourceFamily) (origin τ : ι → ℕ)
    (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (left right : Pattern τ → History l)
    (hs : ∀p,(left p).Supported V outside) (ks : ∀p,(right p).Supported V outside)
    (representative : ∀p,Block p → Representative (left p) (right p))
    (p : Pattern τ) (b : Block p → CommonSample sources origin) (q : Block p) :
    0 ≤ symbolicPatternKernel sources origin τ mixed V outside l left right hs ks representative p b q ∧
      symbolicPatternKernel sources origin τ mixed V outside l left right hs ks representative p b q ≤
        2/((b q).val:ℝ) :=
  symbolicKernel_le_two_div mixed (left p) (right p) (hs p) (ks p) (representative p q)
    (b q).val (commonSample_prime sources origin (b q))

theorem selected_symbolicKernelSum_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (left right : Pattern τ → History l)
    (hs : ∀p,(left p).Supported V outside) (ks : ∀p,(right p).Supported V outside)
    (representative : ∀p,Block p → Representative (left p) (right p))
    (mask : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → ℝ)
    (hm : ∀p b,0 ≤ mask p b ∧ mask p b ≤ 1) :
    biasedKernelSum C.sources origin τ
      (symbolicPatternKernel C.sources origin τ mixed V outside l left right hs ks representative) mask ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (origin i)) q :=
  selected_biasedKernelSum_le C origin τ _ mask
    (symbolicPatternKernel_bounds C.sources origin τ mixed V outside l left right hs ks representative) hm

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
