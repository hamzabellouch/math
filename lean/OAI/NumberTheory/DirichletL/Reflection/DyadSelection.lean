import OAI.NumberTheory.DirichletL.Reflection.TupleDyads
import OAI.NumberTheory.DirichletL.Reflection.TupleMembers

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] [DecidableEq σ] {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

omit [DecidableEq σ] in
lemma activeTupleDyad_subset (i : Fin (columnDyadicLength Hslot+1)) : activeTupleDyad tuples Hslot i⊆tuples :=
  Finset.filter_subset _ _

lemma divisorDyadicBin_subset (i : Fin (columnDyadicLength Hrow+1)) : divisorDyadicBin rows Hrow i⊆rows :=
  Finset.filter_subset _ _

variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)

def dyadicTupleControlled (K : rows) (p : tuples) (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
      (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  C (divisorDyadicLabel Hrow K.val) (divisorDyadicLabel Hslot (slotTupleProduct p.val))
    ⟨K.val,Finset.mem_filter.mpr ⟨K.property,rfl⟩⟩ ⟨p.val,Finset.mem_filter.mpr ⟨p.property,rfl⟩⟩ hp

omit [DecidableEq σ] in
lemma dyadicTupleControlled_at (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j)
    (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩ hp=C i j K p hp := by
  rcases K with ⟨K,hK⟩
  rcases p with ⟨p,hpT⟩
  have hi := (Finset.mem_filter.mp hK).2
  have hj := (Finset.mem_filter.mp hpT).2
  subst i
  subst j
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
