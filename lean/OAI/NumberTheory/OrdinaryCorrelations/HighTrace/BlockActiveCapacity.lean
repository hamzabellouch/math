import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LitEdgesSubsetTree

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal OrdinaryCorrelations.Rerooting
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ : ℕ}

lemma block_active_capacity {α : Type*} [Fintype α] [DecidableEq α]
    (w : NumericalLine D h ℓ) (hh : 0<h) (a : S.FixedResidues w.line)
    {H : Finset (Fin ℓ)} (b : Block (edgeGraph w.line hh (w.line.treeSteps\H)))
    (p : α↪S.FixedIndex w.line) (hph : ∀ i,¬((p i).val:ℕ) ∣ h)
    (x y : ℤ) (hxy : (edgeGraph w.line hh w.line.treeSteps).Adj x y) :
    (univ.filter (fun i => x ∈ blockActiveSet w.line hh a b (p i) ∧
      y ∈ blockActiveSet w.line hh a b (p i))).card ≤ ⌈C₀*Real.log B⌉₊ := by
  obtain ⟨e,_,hor⟩ := hxy
  let s := univ.filter (fun i => x ∈ blockActiveSet w.line hh a b (p i) ∧ y ∈ blockActiveSet w.line hh a b (p i))
  let f : α→S.Index := fun i => (p i).val
  have hinj : Function.Injective f := fun i j hij => p.injective (Subtype.ext hij)
  calc
    s.card=(s.image f).card := (card_image_of_injective _ hinj).symm
    _  ≤  (labelPrimeSet (w.line.label e) (w.labels e)).card := by
      apply card_le_card
      intro r hr
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
      obtain ⟨_,hix,hiy⟩ := mem_filter.mp hi
      have hx := (mem_filter.mp hix).2.2
      have hy := (mem_filter.mp hiy).2.2
      have hends : a (p i)+(w.line.offset e.castSucc:ZMod ((p i).val:ℕ))=0 ∧
          a (p i)+(w.line.offset e.succ:ZMod ((p i).val:ℕ))=0 := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨hx,hy⟩
        · exact ⟨hy,hx⟩
      have hd := ((active_endpoints_iff w.line (p i).val (hph i) (a (p i)) e).mp hends).1
      apply (mem_labelPrimeSet _ _ _).mpr
      exact Nat.mem_primeFactors.mpr ⟨S.prime_mem (p i).val (p i).val.property,hd,(w.line.label_pos e).ne'⟩
    _  ≤  ⌈C₀*Real.log B⌉₊ := by rw [labelPrimeSet_card]; exact D.omega _ (w.labels e)

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
