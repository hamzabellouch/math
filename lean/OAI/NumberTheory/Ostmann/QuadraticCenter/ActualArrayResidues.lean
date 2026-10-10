import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

def quadraticResidueFamily (d : Decomposition) (p : ℕ) : Finset (ZMod p) :=
  if hp : p ≠ 0 then @Decomposition.residueSupport d p ⟨hp⟩ else ∅

@[simp] theorem quadraticResidueFamily_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    quadraticResidueFamily d p = d.residueSupport p := by
  simp only [quadraticResidueFamily,dite_eq_left (NeZero.ne p)]

end Ostmann.QuadraticCenter

end

end OAI
