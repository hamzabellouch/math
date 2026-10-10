import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsFubini
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsPartition
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsUpdate

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows
attribute [local instance] Classical.propDecidable
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

section Decoded
variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
  (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
  (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)
  {outside : List ℕ}
  (hs : (blockLeftHistory sources seed V l p b hvalid a f).Supported V outside)
  (hperm : a.small.Perm a'.small)

def decodedRootSources :
    Fin (blockLeftHistory sources seed V l p b hvalid a f).root.small.length → PrimeSource :=
  fun i => sources (((blockLeftHistory sources seed V l p b hvalid a f).root.small.get i).origin)

theorem decoded_product_sum (giants : Bool → PrimeSource)
    (F : (PairKey (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    let e := decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
    let roots := decodedRootSources sources seed V l p b hvalid a f
    let origin := pairedInternalOrigin seed l
    (∑ x : ∀ i, mixedCarrier giants roots sources origin p i,
      (∏ i, mixedWeight giants roots sources origin p i (x i))*
        F (fun j => mixedValue giants roots sources origin p (e.symm j) (x (e.symm j)))) =
      ∑ y ∈ Fintype.piFinset (fun j => mixedSupport giants roots sources origin p (e.symm j)),
        (∏ j, mixedMass giants roots sources origin p (e.symm j) (y j))*F y := by
  dsimp only
  exact mixed_product_sum_reindex giants _ sources _ p _ F

theorem decoded_product_sum_update (giants : Bool → PrimeSource) (q : Block p)
    (F : (PairKey (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    let e := decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
    let roots := decodedRootSources sources seed V l p b hvalid a f
    let origin := pairedInternalOrigin seed l
    (∑ x : ∀ i, mixedCarrier giants roots sources origin p i,
      (∏ i, mixedWeight giants roots sources origin p i (x i))*
        F (fun j => mixedValue giants roots sources origin p (e.symm j) (x (e.symm j)))) =
      ∑ y ∈ Fintype.piFinset (fun j => mixedSupport giants roots sources origin p (e.symm j)),
        (∏ j, dummyMass giants roots sources origin p e q j (y j))*
          ∑ n ∈ commonCandidates sources origin, blockNaturalWeight sources origin p q n*
            F (Function.update y (e (.inr (.inr q))) (n : ℤ)) := by
  dsimp only
  exact (decoded_product_sum sources seed V l p b hvalid a a' f g ha ha' hs hperm giants F).trans
    (mixed_product_sum_update giants _ sources _ p _ q F)

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
