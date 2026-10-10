import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumOptional
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPrincipalBudgetBiased
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageNonzero

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedKernel
open Construction CanonicalOccurrenceTransport HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement HistoryCompensationBiasedKernelSum
open CompensationEqualityPatterns HistoryCompensationPrincipalBudget Conclusion Filter
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth : ℕ} {E : Finset ℕ}
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem actualProbability_bounds_of_source_samples
    (mixed : Bool) (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (hv : SmallSourceSamples C.sources h k v)
    (r : Representative h k) (p : ℕ) (hp : p.Prime)
    (hr : v (representativeMap h k r) = (p : ℤ))
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) :
    0 ≤ actualProbability mixed h k hs ks r p v ∧
      actualProbability mixed h k hs ks r p v ≤ 2/(p : ℝ) :=
  actualProbability_le_two_div mixed h k hs ks r p hp v
    (new_sample_family_nonzero C hsep h k hh kh hs ks v hv r p hp hr hV)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure SourcePatternReference (C : InitialSourceChoice d Bs BD Bz depth L E)
    (origin τ : ι → ℕ) (p : Pattern τ)
    (b : Block p → CommonSample C.sources origin) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) extends PatternReference p V outside l where
  sourceLeft : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) left
  sourceRight : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) right
  sample : PairKey left right → ℤ
  sourceSamples : SmallSourceSamples C.sources left right sample
  sampled_representative : ∀ q : Block p,
    sample (representativeMap left right (representative q)) = ((b q).val : ℤ)

def optionalDrawActualPatternKernel (C : InitialSourceChoice d Bs BD Bz depth L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀ p : Pattern τ, (b : Block p → CommonSample C.sources origin) →
      Option (SourcePatternReference C origin τ p b V outside l)) :
    ∀ p : Pattern τ, (Block p → CommonSample C.sources origin) → Block p → ℝ :=
  fun p b q => match refs p b with
    | none => 0
    | some r => actualProbability mixed r.left r.right r.hs r.ks (r.representative q)
        (b q).val r.sample

omit [DecidableEq ι] in
theorem optionalDrawActualPatternKernel_bounds [DecidableEq ι]
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j))
    (refs : ∀ p : Pattern τ, (b : Block p → CommonSample C.sources origin) →
      Option (SourcePatternReference C origin τ p b V outside l))
    (p : Pattern τ) (b : Block p → CommonSample C.sources origin) (q : Block p) :
    0 ≤ optionalDrawActualPatternKernel C origin τ mixed V outside l refs p b q ∧
      optionalDrawActualPatternKernel C origin τ mixed V outside l refs p b q ≤
        2/((b q).val : ℝ) := by
  cases hp : refs p b with
  | none =>
    simp only [optionalDrawActualPatternKernel, hp]
    exact ⟨le_rfl, div_nonneg (by norm_num) (Nat.cast_nonneg _)⟩
  | some r =>
    simp only [optionalDrawActualPatternKernel, hp]
    exact actualProbability_bounds_of_source_samples mixed C hsep r.left r.right
      r.sourceLeft r.sourceRight r.hs r.ks r.sample r.sourceSamples (r.representative q)
      (b q).val (commonSample_prime C.sources origin (b q)) (r.sampled_representative q) hV

local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_optionalDrawActualKernelSum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ)
        {spectator : PrimeSource}, C.CrossRoleSeparation spectator →
      (∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) →
      ∀ (refs : ∀ p : Pattern (pairedHistoryType seed l),
        (b : Block p → CommonSample C.sources (pairedInternalOrigin seed l)) →
        Option (SourcePatternReference C (pairedInternalOrigin seed l)
          (pairedHistoryType seed l) p b V outside l))
        (mask : ∀ p : Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀ p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      biasedKernelSum C.sources (pairedInternalOrigin seed l) (pairedHistoryType seed l)
        (optionalDrawActualPatternKernel C (pairedInternalOrigin seed l)
          (pairedHistoryType seed l) mixed V outside l refs) mask ≤
        Real.exp (2*(2 : ℝ)^l*(bulkSize k L : ℝ)) := by
  filter_upwards [selected_biasedKernelSum_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro mixed V outside spectator hsep hV refs mask hm
  exact hL E C hG hGu hcl hcu hb hd l hl _ mask
    (optionalDrawActualPatternKernel_bounds C hsep _ _ mixed V outside l hV refs) hm

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedKernel

end

end OAI
