import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductMixedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSource

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction HistoryBulkSupportConverse HistorySignedSpectatorDiagram HistorySignedSpectatorCRT
open HistorySignedSpectatorDiagramAverage HistoryOccurrenceVariables HistoryCRTIntegration

theorem residuePair_zero_of_nonunit_static {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i:InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (ku : ∀i:InternalKey k,Nat.Coprime (internalSlot k i).value outside.prod)
    (g : (q:ℕ)→ZMod q→ℂ) (hg : ∀q∈outside,g q 0=0)
    (Xp Xm : ZMod outside.prod) (hx : ¬IsUnit Xp) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=0 := by
  classical
  obtain ⟨q,hq,hzero⟩ := exists_cast_zero_of_nonunit outside hp Xp hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hq
  let : Fact (outside.get i).Prime := ⟨hp _ (List.get_mem outside i)⟩
  rw [residuePair_eq_projected_product_static h k hs ks hp hV hu ku]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change primeSpectator (outside.get i) (g (outside.get i)) _ h _ _ *
    conj (primeSpectator (outside.get i) (g (outside.get i)) _ k _ _)=0
  simp only [projectedRingPair,ZMod.castHom_apply]
  rw [primeSpectator_zero_of_giant (outside.get i) (g (outside.get i))
    (hg _ (List.get_mem outside i)) _ h _ _ (Or.inl hzero),zero_mul]

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
