import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawReplacementProfiles

namespace OAI

/-! Restrict a raw system to any sublist of its components. -/

namespace CycleClique.Construction.RawPathSystem

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

def restrictChains (S : RawPathSystem G Q) (C : List (List V)) (hC : C.Sublist S.chains) :
    RawPathSystem G Q where
  chains := C
  paths := fun l hl => S.paths l (hC.subset hl)
  disjoint := S.disjoint.sublist hC
  endpoints := fun l hl => S.endpoints l (hC.subset hl)
  no_clique_steps := fun l hl => S.no_clique_steps l (hC.subset hl)

end CycleClique.Construction.RawPathSystem

end OAI
