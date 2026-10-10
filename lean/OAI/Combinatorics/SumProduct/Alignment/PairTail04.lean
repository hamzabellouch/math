import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevWeighted02
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
open scoped commutatorElement
namespace PairTail
open RationalLattice CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ k : ℕ, (H.level k).Normal]

 

def squareFiltration : Filtration (square (H.level 2)) where
  level k := (LeibmanSquare.level H h0 (max 1 k)).comap (square (H.level 2)).subtype
  antitone := by
    intro i j hij
    exact Subgroup.comap_mono (LeibmanSquare.level_antitone H h0 (max_le_max_left 1 hij))
  commutator_le i j := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    change (↑⁅x,y⁆ : G × G)∈LeibmanSquare.level H h0 (max 1 (i+j))
    have hc := LeibmanSquare.commutator_mem_level H h0 (max 1 i) (max 1 j) hx hy
    exact LeibmanSquare.level_antitone H h0 (by omega) hc

include h1 in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma squareFiltration_zero : (squareFiltration H h0).level 0=⊤ := by
  ext x
  change (x.val.1∈H.level 1 ∧ x.val.2∈H.level 1 ∧
    x.val.1⁻¹*x.val.2∈H.level 2) ↔ True
  simp only [h1,Subgroup.mem_top,true_and,iff_true]
  exact x.property

include h1 in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma squareFiltration_one : (squareFiltration H h0).level 1=⊤ := by
  change (squareFiltration H h0).level 0=⊤
  exact squareFiltration_zero H h0 h1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma squareFiltration_eq_pairLevel (k : ℕ) :
    (squareFiltration H h0).level k=
      pairLevel (H.level 2) (H.level (max 1 k)) (H.level (max 1 k+1)) := by
  ext x
  change (x.val.1∈H.level (max 1 k) ∧ x.val.2∈H.level (max 1 k) ∧
    x.val.1⁻¹*x.val.2∈H.level (max 1 k+1)) ↔
    (x.val.1∈H.level (max 1 k) ∧ x.val.1⁻¹*x.val.2∈H.level (max 1 k+1))
  constructor
  · exact fun hx => ⟨hx.1,hx.2.2⟩
  · rintro ⟨hx,hd⟩
    refine ⟨hx,?_,hd⟩
    have hh := (H.level (max 1 k)).mul_mem hx (H.antitone (by omega : max 1 k ≤ max 1 k+1) hd)
    simpa using hh

variable (s : ℕ) (hs1 : 1 ≤ s) (hs : H.level (s+1)=⊥)
include hs1 hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma squareFiltration_last : (squareFiltration H h0).level s=diagonal (H.level 2) (H.level s) := by
  ext x
  change x.val∈LeibmanSquare.level H h0 (max 1 s) ↔ _
  rw [max_eq_right hs1,LeibmanSquare.last_level H h0 s hs]
  change (x.val.1∈H.level s ∧ x.val.1=x.val.2) ↔ (x.val.1∈H.level s ∧ x.val.2=x.val.1)
  exact and_congr_right fun _ => eq_comm

include h1 hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] [∀ levelIndex : ℕ, (H.level levelIndex).Normal] in
lemma level_last_central : H.level s ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hy : y∈H.level 1 := by rw [h1]; trivial
  have hh := H.commutator_le 1 s (Subgroup.commutator_mem_commutator hy hx)
  rw [Nat.add_comm,hs] at hh
  exact hh

variable [(diagonal (H.level 2) (H.level s)).Normal]

 
def reducedSquareFiltration : Filtration (square (H.level 2) ⧸ diagonal (H.level 2) (H.level s)) :=
  LeibmanSquare.mapFiltration (squareFiltration H h0)
    (QuotientGroup.mk' (diagonal (H.level 2) (H.level s)))

include h1 in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedSquareFiltration_zero : (reducedSquareFiltration H h0 s).level 0=⊤ := by
  change ((squareFiltration H h0).level 0).map _=⊤
  rw [squareFiltration_zero H h0 h1,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

include h1 in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedSquareFiltration_one : (reducedSquareFiltration H h0 s).level 1=⊤ := by
  change ((squareFiltration H h0).level 1).map _=⊤
  rw [squareFiltration_one H h0 h1,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

include hs1 hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedSquareFiltration_last : (reducedSquareFiltration H h0 s).level s=⊥ := by
  change ((squareFiltration H h0).level s).map _=⊥
  rw [squareFiltration_last H h0 s hs1 hs,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedSquareFiltration_level (k : ℕ) :
    (reducedSquareFiltration H h0 s).level k=
      reducedLevel (H.level 2) (H.level s) (H.level (max 1 k)) (H.level (max 1 k+1)) := by
  change ((squareFiltration H h0).level k).map _=_
  rw [squareFiltration_eq_pairLevel]
  rfl

end PairTail
end
end
 

 
section
noncomputable section
namespace PairTail
open RationalLattice MalcevCharacters MalcevWeightedCoordinates CubeFaces
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
lemma filtration_cutoff_monotone {n : ℕ} (c : RealCoordinates G n)
    (H : Filtration G) (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ n)
    (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin n, i.val < q k → c.coord g i=0) :
    Monotone q := by
  classical
  intro a b hab
  by_contra hn
  have hba : q b < q a := Nat.lt_of_not_ge hn
  let i : Fin n := ⟨q b,lt_of_lt_of_le hba (hqbound a)⟩
  have hm : axis c i 1∈H.level b := by
    apply (hq b _).mpr
    intro j hj
    have hji : j≠i := by intro he; subst j; exact (lt_irrefl _ hj)
    simp [hji]
  have hz := (hq a _).mp (H.antitone hab hm) i hba
  simp at hz

variable {t d : ℕ} (c : RealCoordinates G (t+d))
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ k : ℕ, (H.level k).Normal]
variable (s : ℕ) (hs1 : 1 ≤ s) (hs : H.level (s+1)=⊥)
variable [(diagonal (H.level 2) (H.level s)).Normal]
variable (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)

include hq hq2 in
omit [IsTopologicalGroup G] [∀ levelIndex : ℕ, (H.level levelIndex).Normal] in
lemma square_tail_equation (g : G) :
    g∈H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 := by
  rw [hq,hq2]

include h1 hs1 hs hqbound hq2 hq in
 

theorem exists_adapted_reducedCoordinates (Γ : Subgroup G)
    (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z) :
    ∃ c' : RealCoordinates (square (H.level 2) ⧸ diagonal (H.level 2) (H.level s)) (q s+d),
      SecondKind c' ∧
      (∀ g, g∈reducedLattice (H.level 2) (H.level s) Γ ↔ ∀ i, ∃ z : ℤ, c'.coord g i=z) ∧
      ∀ k : ℕ, ∃ r : ℕ, r ≤ q s+d ∧ ∀ g,
        g∈(reducedSquareFiltration H h0 s).level k ↔
          ∀ i : Fin (q s+d), i.val < r → c'.coord g i=0 := by
  classical
  have hK := square_tail_equation c H q hq2 hq
  have hcent := level_last_central H h1 s hs
  let cR := reducedCoordinates c (H.level 2) hK (hqbound s) (H.level s) (hq s) hcent
  let Q:=reducedSquareFiltration H h0 s
  have hQ0 : Q.level 0=⊤ := reducedSquareFiltration_zero H h0 h1 s
  have hQ1 : Q.level 1=⊤ := reducedSquareFiltration_one H h0 h1 s
  have hQs : Q.level s=⊥ := reducedSquareFiltration_last H h0 s hs1 hs
  have hQdeg : Q.level (s+1)=⊥ := le_antisymm (by
    rw [← hQs]
    exact Q.antitone (by omega)) bot_le
  have hsub : ∀ k : ℕ, ∃ I : Set (Fin (q s+d)), ∀ x,
      x∈Q.level k ↔ ∀ i∈I, cR.coord x i=0 := by
    intro k
    by_cases hk : k < s
    · have hks : max 1 k ≤ s := by omega
      have ha : q (max 1 k) ≤ q s := filtration_cutoff_monotone c H q hqbound hq hks
      refine ⟨(Set.range (levelEmbedding (q s) d t (q (max 1 k)) (q (max 1 k+1))))ᶜ,?_⟩
      intro x
      change x∈(reducedSquareFiltration H h0 s).level k ↔ _
      rw [reducedSquareFiltration_level]
      exact reducedLevel_subspace c (H.level 2) hK (hqbound s) (H.level s) (hq s)
        hcent ha (H.level (max 1 k)) (H.level (max 1 k+1)) (hq (max 1 k)) (hq (max 1 k+1)) x
    · have hbot : Q.level k=⊥ := le_antisymm (by
        rw [← hQs]
        exact Q.antitone (by omega)) bot_le
      refine ⟨Set.univ,?_⟩
      intro x
      rw [hbot,Subgroup.mem_bot]
      constructor
      · intro hx i _
        rw [hx]
        exact cR.one_coord i
      · intro hx
        apply cR.coord.injective
        funext i
        rw [hx i (Set.mem_univ i),cR.one_coord]
  apply exists_adapted_secondKind_coordinates cR Q hQ0 hQ1 s hQdeg hsub
  exact reducedLattice_iff c (H.level 2) hK (hqbound s) (H.level s) (hq s) hcent Γ hΓ

end PairTail
end
end
 

 
section
noncomputable section
namespace RationalLattice
open MalcevCharacters
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
    [IsTopologicalGroup G] [IsTopologicalGroup K] {n : ℕ}
variable (c : RealCoordinates K n) (e : G ≃* K)
    (hc : Continuous e) (hci : Continuous e.symm)

omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
@[simp] lemma pullCoordinates_axis (i : Fin n) (t : ℝ) :
    e (axis (pullCoordinates c e hc hci) i t)=axis c i t := by
  change e (e.symm (c.coord.symm (Pi.single i t)))=c.coord.symm (Pi.single i t)
  exact e.apply_symm_apply _

omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
lemma pullCoordinates_secondKind (hsk : SecondKind c) :
    SecondKind (pullCoordinates c e hc hci) where
  axis_add i s t := by
    apply e.injective
    simp only [map_mul,pullCoordinates_axis,hsk.axis_add]
  ordered g := by
    apply e.injective
    rw [map_list_prod,List.map_ofFn]
    simp only [Function.comp_def,pullCoordinates_axis]
    exact hsk.ordered (e g)
end RationalLattice

namespace LeibmanSquare
open CubeFaces RationalLattice MalcevCharacters PairTail
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs0 : 1 ≤ s) (hs : H.level (s+1)=⊥)
variable [((restricted H h0).level s).Normal]
variable [(PairTail.diagonal (H.level 2) (H.level s)).Normal]
variable {t d : ℕ} (c : RealCoordinates G (t+d))
variable (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)

include h1 hs0 hs hqbound hq2 hq in
 

theorem exists_adapted_sourceReducedCoordinates (Γ : Subgroup G)
    (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z) :
    ∃ c' : RealCoordinates ((level H h0 1) ⧸ (restricted H h0).level s) (q s+d),
      SecondKind c' ∧
      (∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
        (QuotientGroup.mk' ((restricted H h0).level s)) ↔ ∀ i, ∃ z : ℤ, c'.coord g i=z) ∧
      ∀ k : ℕ, ∃ r : ℕ, r ≤ q s+d ∧ ∀ g,
        g∈(mapFiltration (restricted H h0) (QuotientGroup.mk' ((restricted H h0).level s))).level k ↔
          ∀ i : Fin (q s+d), i.val < r → c'.coord g i=0 := by
  obtain ⟨cR,hsk,hRL,hRF⟩ := exists_adapted_reducedCoordinates c H h0 h1 s hs0 hs q hqbound hq2 hq Γ hΓ
  let e:=reducedPairEquiv H h0 h1 s hs0 hs
  have hc : Continuous e := reducedPairEquiv_continuous H h0 h1 s hs0 hs
  have hci : Continuous e.symm := reducedPairEquiv_symm_continuous H h0 h1 s hs0 hs
  refine ⟨pullCoordinates cR e hc hci,pullCoordinates_secondKind cR e hc hci hsk,?_,?_⟩
  · intro g
    change g∈_ ↔ ∀ i, ∃ z : ℤ, cR.coord (e g) i=z
    rw [← hRL,← reducedLattice_map H h0 h1 s hs0 hs Γ]
    simp only [Subgroup.mem_map_equiv,e,MulEquiv.symm_apply_apply]
  · intro k
    obtain ⟨r,hr,hrg⟩ := hRF k
    refine ⟨r,hr,fun g => ?_⟩
    change g∈((restricted H h0).level k).map _ ↔ ∀ i : Fin (q s+d), i.val < r → cR.coord (e g) i=0
    rw [← hrg,PairTail.reducedSquareFiltration_level,← reducedLevel_map H h0 h1 s hs0 hs k]
    simp only [Subgroup.mem_map_equiv,e,MulEquiv.symm_apply_apply]

end LeibmanSquare

end
end
end
end
end

end OAI
