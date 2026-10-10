import OAI.NumberTheory.Ostmann.Construction.HalfSupport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

instance PrimeSource.sampleNeZero (S : PrimeSource) (p : S.Sample) : NeZero p.val :=
  ⟨(S.prime _ p.property).ne_zero⟩

theorem assignedSlots_product_pos (sources : SourceFamily) (T : List SourceSlot)
    (u : SourceAssignment sources T) :
    0<((assignedSlots sources T u).map SmallSlot.value).prod := by
  apply List.prod_pos
  intro q hq
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
  exact (assignedSlots_prime sources T u z hz).pos

instance sourceHalfProductNeZero (sources : SourceFamily) (T : List SourceSlot)
    (u : SourceAssignment sources T) (p : ℕ) [NeZero p] :
    NeZero (halfProduct p (assignedSlots sources T u)) :=
  ⟨(mul_pos (Nat.pos_of_ne_zero (NeZero.ne p)) (assignedSlots_product_pos sources T u)).ne'⟩

end Ostmann.Construction

end

end OAI
