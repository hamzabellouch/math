import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagEnvelopeBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairSourceLaws HistoryPairFlags PolynomialFlagReplacementFinite HistorySymbolicEncoding
attribute [local instance] Classical.propDecidable
local instance envelopeInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

section Decoded
variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz depth L E) (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
variable (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
  (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)
variable {outside : List ℕ} (hs : ((blockLeftHistory sources seed V l p b hvalid a f)).Supported V outside) (ks : ((blockRightHistory sources seed V l p b hvalid a' g)).Supported V outside)
  (hperm : a.small.Perm a'.small) (hroot : @RootGiantsAgree l (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g))

open HistoryPairRepresentatives HistoryOccurrenceVariables

theorem decoded_dummy_small_abs_le (giants : Bool → PrimeSource) (q : Block p) (B : ℝ)
    (hcap : ∀ i, ∀ v : (sources i).Sample,
      (sources i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B) :
    (∀ i : Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length ⊕ InternalKey (blockLeftHistory sources seed V l p b hvalid a f), ∀ z : ℤ,
      dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q
        (leftMap (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) (.inr i)) z ≠ 0 → |(z:ℝ)| ≤ B) ∧
    (∀ i : Fin (blockRightHistory sources seed V l p b hvalid a' g).root.small.length ⊕ InternalKey (blockRightHistory sources seed V l p b hvalid a' g), ∀ z : ℤ,
      dummyMass giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q
        (rightMap (blockLeftHistory sources seed V l p b hvalid a f) (blockRightHistory sources seed V l p b hvalid a' g) (.inr i)) z ≠ 0 → |(z:ℝ)| ≤ B) := by
  constructor
  · intro i z hz
    apply dummyMass_non_giant_abs_le giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q B
      (fun i => hcap _) hcap _ ?_ z hz
    intro t he
    have he' := congrArg Subtype.val he
    rcases i with i | i <;>
      change (Sum.inr _ : Bool ⊕ (ℕ × ℤ)) = Sum.inl t at he' <;> cases he'
  · intro i z hz
    apply dummyMass_non_giant_abs_le giants (decodedRootSources sources seed V l p b hvalid a f) sources (pairedInternalOrigin seed l) p (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q B
      (fun i => hcap _) hcap _ ?_ z hz
    intro t he
    have he' := congrArg Subtype.val he
    rcases i with i | i <;>
      change (Sum.inr _ : Bool ⊕ (ℕ × ℤ)) = Sum.inl t at he' <;> cases he'

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
