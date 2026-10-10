import OAI.NumberTheory.Jacobsthal.Partitions.BoundedEdgeBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentCofactorChoices
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections AssembleAtBin SingletonBinSelection SingletonBinProduct
open BinCutPrefixGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

noncomputable def parentCofactorMultiplicity {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  eraseMultiplicity (aboveMultiplicity m j) i
noncomputable def completeParent {n : ℕ} (anchor f : Fin n → Finset ℕ) (i j : Fin n) (p u : ℕ) : Fin n → Finset ℕ :=
  assemble anchor (fillSelection f i p) j u

theorem cofactor_slots_zero {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) :
    parentCofactorMultiplicity m i j i=0 ∧ parentCofactorMultiplicity m i j j=0 := by
  simp [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity]

theorem cofactor_total_le {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) :
    (∑ k,parentCofactorMultiplicity m i j k) ≤ ∑ k,m k := by
  apply Finset.sum_le_sum
  intro k _
  simp only [parentCofactorMultiplicity,eraseMultiplicity,aboveMultiplicity]
  split_ifs <;> omega

theorem complete_parent_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1)
    (anchor f : Fin n → Finset ℕ) (ha : anchor ∈ selections P m)
    (hf : f ∈ selections P (parentCofactorMultiplicity m i j)) (p u : ℕ) (hp : p ∈ P i) (hu : u ∈ P j) :
    completeParent anchor f i j p u ∈ selections P m := by
  have hmi : aboveMultiplicity m j i=1 := by simp [aboveMultiplicity,hji,hi]
  exact assembled_mem P m anchor _ j u ha (fill_selection_mem P _ i hmi f hf p hp) hj hu

theorem complete_parent_product {w top xi : ℝ} (_hw : 1 < w) (_htop : w < top) (_hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (anchor f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (parentCofactorMultiplicity m i j))
    (p u : ℕ) (hp : p ∈ globalBins w top xi i) :
    selectionProduct (aboveSelection (completeParent anchor f i j p u) j)=p*selectionProduct f := by
  have hmi : aboveMultiplicity m j i=1 := by simp [aboveMultiplicity,hji,hi]
  have hfill := fill_selection_mem (globalBins w top xi) _ i hmi f hf p hp
  rw [completeParent,assembled_above _ m anchor _ j u hfill]
  exact filled_product f i p (erased_coordinate_empty _ (aboveMultiplicity m j) i f hf)
end NumberTheoryLean.ParentCofactorChoices



namespace NumberTheoryLean.CofactorAllChoiceBounds
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections AssembleAtBin ParentCofactorChoices
open FullBoxLengthBounds BoundedEdgeBins SafeSubsetBoxGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem cofactor_all_choice_lengths {w top xi B C K a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (i j : Fin (binCount w top xi)) (hji : j < i) (hi : m i=1)
    (hj : boundedEdgeBin w top xi Y m M X j) :
    (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log w ≤ M+2*C*xi) ∧
    (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
        a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)*(u:ℝ)))/Real.log w) := by
  have hmj := bounded_edge_singleton m j hj
  obtain ⟨g,hgmem,u₀,hgju,hparent,_hx⟩ := hj
  have hu₀ : u₀ ∈ globalBins w top xi j := ((mem_selections _ _ _).mp hgmem j).1 (by rw [hgju]; simp)
  have hlen := anchor_total_length hw htop hxi z m ha
  have hall : ∀ f ∈ selections (globalBins w top xi) (parentCofactorMultiplicity m i j),
      ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
      Real.log ((Y:ℝ)/((p:ℝ)*(selectionProduct f:ℝ)))/Real.log w ≤ M+2*C*xi ∧
      a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(selectionProduct f:ℝ)*(u:ℝ)))/Real.log w := by
    intro f hf p hp u hu
    let F := completeParent g f i j p u
    have hF : F ∈ selections (globalBins w top xi) m := complete_parent_mem _ m i j hji hi hmj g f hgmem hf p u hp hu
    have hFu : F j={u} := assembled_edge _ _ j u
    have hprod : selectionProduct (aboveSelection F j)=p*selectionProduct f := complete_parent_product hw htop hxi m i j hji hi g f hf p u hp
    have hmove := parent_length_movement hw htop hxi hC hcomp Y hY z hroot m hlen F g hF hgmem j
    have hupper : parentLength w Y F j ≤ M+2*C*xi := by linarith [(abs_le.mp hmove).2]
    have hlower := full_box_child_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m ha F hF j u hFu
    simpa only [parentLength,childLength,hprod,Nat.cast_mul] using And.intro hupper hlower
  constructor
  · intro q hq p hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
    exact (hall f hf p hp u₀ hu₀).1
  · intro q hq p hp u hu
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
    exact (hall f hf p hp u hu).2
end NumberTheoryLean.CofactorAllChoiceBounds


end Erdos970

end OAI
