import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeExposure

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open FrequencyExposure
attribute [local instance] Classical.propDecidable

def ContextMatches (k R j:ℕ) (h:KnownStates k R) (C:(schedule k j).Slot→ℤ) : Prop :=
  ∀i,h j i=(C i:ZMod (R^(j+2)))

theorem knownCoefficient_matches (k R j:ℕ) (b:Bool) (s:ℤ) (hs:s.natAbs∣R)
    (h:KnownStates k R) (C:(schedule k (j+1)).Slot→ℤ) (hc:ContextMatches k R (j+1) h C) :
    knownCoefficient k R j b s hs h=nodeCoefficient k j b s C := by
  unfold knownCoefficient
  have he : h (j+1)=fun i=>(C i:ZMod (R^((j+1)+2))) := funext hc
  rw [he]
  exact nodeCoefficient_of_residues _ k j b s _ C

theorem chosen_product_residue (Q N k j:ℕ) (hNQ:N∣Q)
    (z:WordSlot k j→ℤ) (ξ:WordSlot k j→(ZMod Q)ˣ)
    (hξ:∀i,(z i:ZMod Q)=ξ i) :
    ((∏i,z i:ℤ):ZMod N)=
      (ZMod.unitsMap hNQ (BinaryHaar.product (G:=(ZMod Q)ˣ) (wordTreeEquiv (G:=(ZMod Q)ˣ) k j ξ)):ZMod N) := by
  rw [wordTreeEquiv_product,ZMod.unitsMap_def,Units.coe_map]
  have ht : ((∏i,z i:ℤ):ZMod Q)=(∏i,ξ i:(ZMod Q)ˣ) := by
    simp only [Int.cast_prod,Units.coe_prod]
    exact Finset.prod_congr rfl (fun i _=>hξ i)
  rw [← ht]
  exact (map_intCast (ZMod.castHom hNQ (ZMod N)) _).symm

theorem realized_node_constraint (k K R j:ℕ) (d:List Bool→Data R) (p:List Bool)
    (h:PairedKnownStates k R)
    (C C':(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ)
    (ξ:WordSlot k (j+1)→(ZMod (R^(K+2)))ˣ)
    (hξ:∀i,(z i:ZMod (R^(K+2)))=ξ i)
    (hc:ContextMatches k R (j+1) h.1 C) (hc':ContextMatches k R (j+1) h.2 C')
    (hCL:IsUnit (blockProduct k j true (fun i=>(C i:ZMod (d p).s.natAbs))))
    (hCR:IsUnit (blockProduct k j false (fun i=>(C i:ZMod (d p).s.natAbs))))
    (hCL':IsUnit (blockProduct k j true (fun i=>(C' i:ZMod (d p).s'.natAbs))))
    (hCR':IsUnit (blockProduct k j false (fun i=>(C' i:ZMod (d p).s'.natAbs))))
    (hint:(d p).s∣(d p).v*copiedProduct k j false (installWords k (j+1) C z)-
      (d p).w*copiedProduct k j true (installWords k (j+1) C z))
    (hint':(d p).s'∣(d p).v'*copiedProduct k j false (installWords k (j+1) C' z)-
      (d p).w'*copiedProduct k j true (installWords k (j+1) C' z)) :
    exposureConstraint k K R d j (p,h)
      (BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k (j+1) ξ))
      (BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j true ξ))) := by
  have hrep (b:Bool) (i:WordSlot k j) :
      ((splitWords (R:=ℤ) k j b z i:ℤ):ZMod (R^(K+2)))=splitWords k j b ξ i := hξ _
  have hprod : BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k (j+1) ξ)=
      BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j true ξ))*
      BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j false ξ)) := rfl
  unfold exposureConstraint
  rw [knownCoefficient_matches k R j true _ _ h.1 C hc,
    knownCoefficient_matches k R j false _ _ h.1 C hc,
    knownCoefficient_matches k R j true _ _ h.2 C' hc',
    knownCoefficient_matches k R j false _ _ h.2 C' hc',hprod,map_mul,map_mul]
  constructor
  · exact actual_integrality_rawSplit k j (d p).s (d p).v (d p).w C z _ _
      (chosen_product_residue _ _ k j _ _ _ (hrep true))
      (chosen_product_residue _ _ k j _ _ _ (hrep false)) hCL hCR hint
  · exact actual_integrality_rawSplit k j (d p).s' (d p).v' (d p).w' C' z _ _
      (chosen_product_residue _ _ k j _ _ _ (hrep true))
      (chosen_product_residue _ _ k j _ _ _ (hrep false)) hCL' hCR' hint'

end Ostmann.Characters.Template

end

end OAI
