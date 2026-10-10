import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CoordinateSubspace01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace PairTail
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d r : ℕ} (c : RealCoordinates G (t+d))
variable (K : Subgroup G) [K.Normal]
variable (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)
variable (hr : r ≤ t+d) (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)
variable (hcent : N ≤ Subgroup.center G) [(diagonal K N).Normal]

 
def pairLevel (A B : Subgroup G) [B.Normal] : Subgroup (square K) :=
  (A.comap (first K)) ⊓ (square B).comap (square K).subtype

def reducedLevel (A B : Subgroup G) [B.Normal] : Subgroup (square K ⧸ diagonal K N) :=
  (pairLevel K A B).map (QuotientGroup.mk' (diagonal K N))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma mem_pairLevel (A B : Subgroup G) [B.Normal] (x : square K) :
    x ∈ pairLevel K A B ↔ x.val.1 ∈ A ∧ x.val.1⁻¹*x.val.2 ∈ B := Iff.rfl

variable {a b : ℕ} (ha : a ≤ r)
variable (A B : Subgroup G) [B.Normal]
variable (hA : ∀ g : G, g ∈ A ↔ ∀ i : Fin (t+d), i.val < a → c.coord g i = 0)
variable (hB : ∀ g : G, g ∈ B ↔ ∀ i : Fin (t+d), i.val < b → c.coord g i = 0)

include ha hA hB in
 

omit [N.Normal] in
theorem reducedLevel_coordinates (x : square K ⧸ diagonal K N) :
    x ∈ reducedLevel K N A B ↔
      (∀ i : Fin r, i.val < a →
        (reducedCoordinates c K hK hr N hN hcent).coord x (i.castAdd d) = 0) ∧
      (∀ j : Fin d, t+j.val < b →
        (reducedCoordinates c K hK hr N hN hcent).coord x (j.natAdd r) = 0) := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    change y.val.1 ∈ A ∧ y.val.1⁻¹*y.val.2 ∈ B at hy
    constructor
    · intro i hi
      change chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk y) _ = 0
      rw [chart_base]
      exact (hA y.val.1).mp hy.1 _ hi
    · intro j hj
      change chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk y) _ = 0
      rw [chart_tail]
      exact (hB _).mp hy.2 _ hj
  · induction x using Quotient.inductionOn with | h x =>
      intro hx
      refine ⟨x,?_,rfl⟩
      change x.val.1 ∈ A ∧ x.val.1⁻¹*x.val.2 ∈ B
      constructor
      · apply (hA _).mpr
        intro i hi
        have hir : i.val < r := lt_of_lt_of_le hi ha
        have he := hx.1 ⟨i.val,hir⟩ hi
        change chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk x) _ = 0 at he
        rw [chart_base] at he
        exact he
      · apply (hB _).mpr
        intro i hi
        by_cases hit : i.val < t
        · exact (hK _).mp x.property i hit
        · have hid : i.val-t < d := by have := i.isLt; omega
          have he := hx.2 ⟨i.val-t,hid⟩ (by dsimp; omega)
          change chartHomeomorph c K hK hr N hN hcent (QuotientGroup.mk x) _ = 0 at he
          rw [chart_tail] at he
          have hiEq : RationalTailCoordinates.embed t (⟨i.val-t,hid⟩ : Fin d) = i :=
            Fin.ext (by dsimp [RationalTailCoordinates.embed]; omega)
          simpa only [hiEq] using he

 
def levelIndices (r d t a b : ℕ) : Finset (Fin (r+d)) :=
  Finset.univ.filter (fun i => (i.val < r → a ≤ i.val) ∧ (r ≤ i.val → b ≤ t+(i.val-r)))

def levelEmbedding (r d t a b : ℕ) :
    Fin (levelIndices r d t a b).card ↪o Fin (r+d) :=
  (levelIndices r d t a b).orderEmbOfFin rfl

lemma mem_range_levelEmbedding (i : Fin (r+d)) :
    i ∈ Set.range (levelEmbedding r d t a b) ↔
      (i.val < r → a ≤ i.val) ∧ (r ≤ i.val → b ≤ t+(i.val-r)) := by
  rw [levelEmbedding,Finset.range_orderEmbOfFin]
  simp only [Finset.mem_coe,levelIndices,Finset.mem_filter,Finset.mem_univ,true_and]

include ha hA hB in
omit [N.Normal] in
lemma reducedLevel_subspace (x : square K ⧸ diagonal K N) :
    x ∈ reducedLevel K N A B ↔ ∀ i,
      i ∉ Set.range (levelEmbedding r d t a b) →
        (reducedCoordinates c K hK hr N hN hcent).coord x i = 0 := by
  rw [reducedLevel_coordinates c K hK hr N hN hcent ha A B hA hB]
  constructor
  · rintro ⟨hbase,htail⟩ i hi
    rw [mem_range_levelEmbedding] at hi
    by_cases hir : i.val < r
    · have hia : i.val < a := by omega
      exact hbase ⟨i.val,hir⟩ hia
    · have hid : i.val-r < d := by have := i.isLt; omega
      have hib : t+(i.val-r) < b := by omega
      have hiEq : Fin.natAdd r (⟨i.val-r,hid⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
      simpa only [hiEq] using htail ⟨i.val-r,hid⟩ hib
  · intro hx
    constructor
    · intro i hi
      apply hx
      rw [mem_range_levelEmbedding]
      simp only [Fin.val_castAdd]
      omega
    · intro j hj
      apply hx
      rw [mem_range_levelEmbedding]
      simp only [Fin.val_natAdd]
      omega

 

def reducedLevelCoordinates : RealCoordinates (reducedLevel K N A B)
    (levelIndices r d t a b).card :=
  CoordinateSubspace.restrictedCoordinates
    (reducedCoordinates c K hK hr N hN hcent) (levelEmbedding r d t a b)
    (reducedLevel K N A B) (reducedLevel_subspace c K hK hr N hN hcent ha A B hA hB)

omit [N.Normal] in
lemma reducedLevel_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (x : reducedLevel K N A B) :
    x ∈ (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype ↔
      ∀ i, ∃ z : ℤ, (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB).coord x i = z :=
  CoordinateSubspace.restricted_lattice _ _ _ _ (reducedLattice K N Γ)
    (reducedLattice_iff c K hK hr N hN hcent Γ hΓ) x

end PairTail
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

include c in
lemma coordinates_connected : ConnectedSpace G :=
  c.coord.connectedSpace_iff.mpr inferInstance

include c in
lemma coordinates_simplyConnected : SimplyConnectedSpace G :=
  c.coord.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

include c in
lemma coordinates_locallyCompact : LocallyCompactSpace G :=
  c.coord.locallyCompactSpace_iff.mpr inferInstance

include c in
lemma coordinates_secondCountable : SecondCountableTopology G :=
  c.coord.secondCountableTopology

end RationalLattice

namespace PairTail
open RationalLattice MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d r : ℕ} (c : RealCoordinates G (t+d))
variable (K : Subgroup G) [K.Normal]
variable (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)
variable (hr : r ≤ t+d) (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)
variable (hcent : N ≤ Subgroup.center G) [(diagonal K N).Normal]
variable {a b : ℕ} (ha : a ≤ r)
variable (A B : Subgroup G) [B.Normal]
variable (hA : ∀ g : G, g ∈ A ↔ ∀ i : Fin (t+d), i.val < a → c.coord g i = 0)
variable (hB : ∀ g : G, g ∈ B ↔ ∀ i : Fin (t+d), i.val < b → c.coord g i = 0)

include ha hA hB hK hN hcent hr in
omit [N.Normal] in
lemma reducedLevel_connected : ConnectedSpace (reducedLevel K N A B) :=
  coordinates_connected (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB)

include ha hA hB hK hN hcent hr in
omit [N.Normal] in
lemma reducedLevel_simplyConnected : SimplyConnectedSpace (reducedLevel K N A B) :=
  coordinates_simplyConnected (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB)

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)

include ha hA hB hK hN hcent hr hΓ in
omit [N.Normal] in
lemma reducedLevel_compact_reps :
    ∃ C : Set (reducedLevel K N A B), IsCompact C ∧ ∀ g : reducedLevel K N A B,
      ∃ x ∈ C, x⁻¹*g ∈ (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype :=
  compact_reps_of_integerCoordinates
    (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB)
    ((reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)
    (reducedLevel_lattice c K hK hr N hN hcent ha A B hA hB Γ hΓ)

include ha hA hB hK hN hcent hr hΓ in
omit [N.Normal] in
lemma reducedLevel_discrete :
    DiscreteTopology ((reducedLattice K N Γ).comap (reducedLevel K N A B).subtype) :=
  integerCoordinates_discrete
    (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB)
    ((reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)
    (reducedLevel_lattice c K hK hr N hN hcent ha A B hA hB Γ hΓ)

include ha hA hB hK hN hcent hr hΓ in
 

omit [N.Normal] in
lemma reducedLevelHaar_existsUnique
    [MeasurableSpace ((reducedLevel K N A B) ⧸
      (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)]
    [BorelSpace ((reducedLevel K N A B) ⧸
      (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)] :
    ∃! μ : ProbabilityMeasure ((reducedLevel K N A B) ⧸
      (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype),
      SMulInvariantMeasure (reducedLevel K N A B)
        ((reducedLevel K N A B) ⧸
          (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)
        (μ : Measure ((reducedLevel K N A B) ⧸
          (reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)) :=
  existsUnique_coordinateHaar
    (reducedLevelCoordinates c K hK hr N hN hcent ha A B hA hB)
    ((reducedLattice K N Γ).comap (reducedLevel K N A B).subtype)
    (reducedLevel_lattice c K hK hr N hN hcent ha A B hA hB Γ hΓ)

end PairTail
end
end
 

 
section

 

open scoped commutatorElement

namespace CubeFaces
 

end CubeFaces

end
end
end
end

end OAI
