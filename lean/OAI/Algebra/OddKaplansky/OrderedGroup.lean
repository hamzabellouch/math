import OAI.Algebra.OddKaplansky.GreedyFormula

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.SourceOrders
noncomputable section
open scoped Classical
variable {H : Type portUniverse1} [Group H] [Fintype H] [LinearOrder H]
@[instance_reducible]
def wreathOrder (M : ℕ) [NeZero M] : LinearOrder (WreathFourier.Wreath (H := H) M) := by
  letI : LinearOrder (Fourier.C M) := cyclic M
  letI : LinearOrder (WreathFourier.Base (H := H) M) := FiniteChoice.functionOrder H (Fourier.C M)
  exact LinearOrder.lift' (fun g : WreathFourier.Wreath (H := H) M => toLex (g.left,g.right)) (by
    intro a b h
    have h' : (a.left,a.right)=(b.left,b.right) := h
    exact RegularWreathProduct.ext (congrArg Prod.fst h') (congrArg Prod.snd h'))
instance localGroupOrder (p M : ℕ) [NeZero p] [NeZero M] : LinearOrder (RegularWreathProduct (Fourier.C M) (Multiplicative (Fin 3 → ZMod p))) :=
  by
    letI : LinearOrder (Multiplicative (Fin 3 → ZMod p)) := point p
    exact wreathOrder M
end
end OddKaplansky.SourceOrders

end

end OAI
