import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPLabelTransport

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E A B : Type} [Fintype E] [DecidableEq A] [DecidableEq B]
variable (C : BinaryCSP V E A) (e : A ≃ B)
def mapLabels : BinaryCSP V E B where
  left := C.left
  right := C.right
  allowed t := (C.allowed t).map (e.prodCongr e).toEmbedding

omit [Fintype E] [DecidableEq A] [DecidableEq B] in
@[simp] lemma mapLabels_allowed (t : E) (a b : B) :
    (a,b) ∈ (C.mapLabels e).allowed t ↔ (e.symm a,e.symm b) ∈ C.allowed t := by
  simp [mapLabels,Finset.mem_map_equiv]

omit [Fintype E] [DecidableEq A] [DecidableEq B] in
lemma mapLabels_complete (a : V → A) (ha : C.Satisfies a) :
    (C.mapLabels e).Satisfies (e ∘ a) := by
  intro t
  apply (mapLabels_allowed C e t _ _).mpr
  simpa only [Function.comp_def,Equiv.symm_apply_apply,mapLabels] using ha t

omit [DecidableEq A] [DecidableEq B] in
lemma mapLabels_rejection (a : V → B) :
    (C.mapLabels e).rejection a=C.rejection (e.symm ∘ a) := by
  apply testRate_congr
  intro t
  exact not_congr (mapLabels_allowed C e t _ _)
end BinaryCSP

namespace Advice
abbrev BitIndex (D K : Type) (cap : ℕ) := (n : Fin (cap+1)) × ((Fin n.val → D) × K)
def bitsEquiv (D K : Type) (cap : ℕ) :
    Advice D (BitVector K) cap ≃ BitVector (BitIndex D K cap) where
  toFun a p := a p.1 p.2.1 p.2.2
  invFun b n w k := b ⟨n,w,k⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Advice
end MetricKMedian.PCP

end Inline_PCPLabelTransport

end OAI
