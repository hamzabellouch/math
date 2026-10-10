import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData
import OAI.Analysis.LipschitzHilbert.Estimates.ShearedLatticePeriodization

namespace OAI

/-! The physical sites are exactly the translated sheared lattices used
by the common probability average. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem actualSite_eq_lattice_translate (P : PacketLatticeData N κ Label Item)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.actualX j l a,P.actualZ j l a) =
      PacketRepresentation.latticeHom (P.length j) P.width (P.rowSlope j l) (P.site j l a)+
        (P.originX j l,P.originZ j l) := by
  apply Prod.ext <;>
    simp only [actualX,actualZ,PacketRepresentation.latticeHom,AddMonoidHom.coe_mk,
      ZeroHom.coe_mk,Prod.fst_add,Prod.snd_add] <;> ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
