import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LowReuseOrder

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

def DisjointRoots (A : ι → Finset α) (R : Finset ι) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (A i) (A j)

theorem exists_maximal_roots (A : ι → Finset α) (s : Finset ι) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R → (A i ∩ R.biUnion A).Nonempty := by
  classical
  let candidates := s.powerset.filter (DisjointRoots A)
  have hempty : ∅ ∈ candidates := by simp [candidates, DisjointRoots]
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  obtain ⟨hRs, hdisj⟩ := Finset.mem_filter.mp hR
  have hsub : R ⊆ s := Finset.mem_powerset.mp hRs
  refine ⟨R, hsub, hdisj, ?_⟩
  intro i hi hin
  by_contra hnone
  have hdisjnew : DisjointRoots A (insert i R) := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hjk.symm
      apply Finset.disjoint_left.mpr
      intro a hai hak
      exact hnone ⟨a, Finset.mem_inter.mpr
        ⟨hai, Finset.mem_biUnion.mpr ⟨k, hkR, hak⟩⟩⟩
    · have hjR : j ∈ R := (Finset.mem_insert.mp hj).resolve_left hji
      by_cases hki : k = i
      · subst k
        apply Finset.disjoint_left.mpr
        intro a haj hai
        exact hnone ⟨a, Finset.mem_inter.mpr
          ⟨hai, Finset.mem_biUnion.mpr ⟨j, hjR, haj⟩⟩⟩
      · have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hki
        exact hdisj j hjR k hkR hjk
  have hnew : insert i R ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), hdisjnew⟩
  have hc := hmax (insert i R) hnew
  rw [Finset.card_insert_of_notMem hin] at hc
  omega

theorem exists_roots_of_small_shared (A : ι → Finset α) (s : Finset ι)
    (hsmall : ∀ i ∈ s, (A i ∩ (s.erase i).biUnion A).card ≤ 1) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  obtain ⟨R, hRs, hdisj, hmeet⟩ := exists_maximal_roots A s
  refine ⟨R, hRs, hdisj, ?_⟩
  intro i hi hin
  have hRerase : R ⊆ s.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji => hin (hji ▸ hj), hRs hj⟩
  have hinter : A i ∩ R.biUnion A ⊆ A i ∩ (s.erase i).biUnion A := by
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hcard : (A i ∩ R.biUnion A).card = 1 := by
    have hpos := Finset.card_pos.mpr (hmeet i hi hin)
    have hle := (Finset.card_le_card hinter).trans (hsmall i hi)
    omega
  refine ⟨hcard, ?_⟩
  obtain ⟨a, ha⟩ := hmeet i hi hin
  intro x hx
  have hxa : x = a := Finset.card_le_one.mp (hsmall i hi) x hx a (hinter ha)
  exact hxa ▸ (Finset.mem_inter.mp ha).2

theorem disjointRoots_of_zero_reuse (A : ι → Finset α) (s : Finset ι)
    (hz : (∑ i ∈ s, (A i).card) - (s.biUnion A).card = 0) :
    DisjointRoots A s := by
  intro i hi j hj hij
  have hd := Balanced.family_reuse_erase A s i hi
  have hc : (A i ∩ (s.erase i).biUnion A).card = 0 := by omega
  have he := Finset.card_eq_zero.mp hc
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have ha : a ∈ A i ∩ (s.erase i).biUnion A :=
    Finset.mem_inter.mpr ⟨hai, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hij.symm, hj⟩, haj⟩⟩
  simp only [he, Finset.notMem_empty] at ha

theorem exists_roots_of_large_shared (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2)
    (i : ι) (hi : i ∈ s) (hbig : 2 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ j ∈ s, j ∉ R →
        (A j ∩ R.biUnion A).card = 1 ∧
        A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
  classical
  have hd := Balanced.family_reuse_erase A s i hi
  have hz : (∑ j ∈ s.erase i, (A j).card) - ((s.erase i).biUnion A).card = 0 := by
    omega
  have hrest := disjointRoots_of_zero_reuse A (s.erase i) hz
  let R := insert i ((s.erase i).filter fun j => Disjoint (A j) (A i))
  have hiR : i ∈ R := Finset.mem_insert_self _ _
  have hRs : R ⊆ s := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
  have hroot : DisjointRoots A R := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hjk.symm)
      exact hkf.2.symm
    · have hjf := Finset.mem_filter.mp ((Finset.mem_insert.mp hj).resolve_left hji)
      by_cases hki : k = i
      · subst k
        exact hjf.2
      · have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hki)
        exact hrest j hjf.1 k hkf.1 hjk
  refine ⟨R, hRs, hroot, ?_⟩
  intro j hj hjR
  have hji : j ≠ i := fun h => hjR (h ▸ hiR)
  have hjrest : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
  have hnD : ¬ Disjoint (A j) (A i) := by
    intro hD
    exact hjR (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hjrest, hD⟩))
  have hshared : A j ∩ (s.erase j).biUnion A = A j ∩ A i := by
    ext a
    constructor
    · intro ha
      obtain ⟨haj, har⟩ := Finset.mem_inter.mp ha
      obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp har
      by_cases hki : k = i
      · exact Finset.mem_inter.mpr ⟨haj, hki ▸ hak⟩
      · have hkrest : k ∈ s.erase i :=
          Finset.mem_erase.mpr ⟨hki, (Finset.mem_erase.mp hk).2⟩
        exact (Finset.disjoint_left.mp
          (hrest j hjrest k hkrest (Finset.mem_erase.mp hk).1.symm) haj hak).elim
    · intro ha
      obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨haj, Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hji.symm, hi⟩, hai⟩⟩
  have hsharedRoots : A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
    rw [hshared]
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, hiR, (Finset.mem_inter.mp ha).2⟩
  refine ⟨?_, hsharedRoots⟩
  have hRerase : R ⊆ s.erase j := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun h => hjR (h ▸ hk), hRs hk⟩
  have hinter : A j ∩ R.biUnion A ⊆ A j ∩ A i := by
    rw [← hshared]
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hle := (Finset.card_le_card hinter).trans (hpair j hj i hi hji)
  have hnon : (A j ∩ A i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hnD (Finset.disjoint_iff_inter_eq_empty.mpr he)
  obtain ⟨a, ha⟩ := hnon
  obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
  have hpos : 0 < (A j ∩ R.biUnion A).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr
      ⟨haj, Finset.mem_biUnion.mpr ⟨i, hiR, hai⟩⟩⟩
  omega

theorem exists_root_child_partition (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  by_cases hbig : ∃ i ∈ s, 2 ≤ (A i ∩ (s.erase i).biUnion A).card
  · obtain ⟨i, hi, hbig⟩ := hbig
    exact exists_roots_of_large_shared A s hpair hr i hi hbig
  · apply exists_roots_of_small_shared A s
    intro i hi
    have hn : ¬ 2 ≤ (A i ∩ (s.erase i).biUnion A).card := fun h => hbig ⟨i, hi, h⟩
    omega

theorem partition_image {β : Type*} [DecidableEq β]
    (A : ι → Finset α) (s R : Finset ι) (f : α → β) (hf : Function.Injective f)
    (hroots : DisjointRoots A R)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A) :
    DisjointRoots (fun i => (A i).image f) R ∧
      ∀ i ∈ s, i ∉ R →
        ((A i).image f ∩ R.biUnion (fun j => (A j).image f)).card = 1 ∧
        (A i).image f ∩ (s.erase i).biUnion (fun j => (A j).image f) ⊆
          R.biUnion (fun j => (A j).image f) := by
  constructor
  · intro i hi j hj hij
    exact (Finset.disjoint_image hf).mpr (hroots i hi j hj hij)
  · intro i hi hin
    obtain ⟨hc, hs⟩ := hchildren i hi hin
    constructor
    · rw [← Finset.biUnion_image, ← Finset.image_inter _ _ hf,
        Finset.card_image_of_injective _ hf]
      exact hc
    · rw [← Finset.biUnion_image, ← Finset.biUnion_image,
        ← Finset.image_inter _ _ hf]
      exact Finset.image_subset_image hs

theorem exists_pattern_roots {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b),
      DisjointRoots (fun i => Finset.univ.image (P.classOf i)) R ∧
      ∀ i, i ∉ R →
        ((Finset.univ.image (P.classOf i)) ∩
          R.biUnion (fun j => Finset.univ.image (P.classOf j))).card = 1 ∧
        (Finset.univ.image (P.classOf i)) ∩
          (Finset.univ.erase i).biUnion (fun j => Finset.univ.image (P.classOf j)) ⊆
          R.biUnion (fun j => Finset.univ.image (P.classOf j)) := by
  let A : Fin b → Finset (Fin (4 * b - κ)) := fun i => Finset.univ.image (P.classOf i)
  have hcard (i : Fin b) : (A i).card = 4 := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ (P.withinTuple i)]
    simp
  have hUnion : Finset.univ.biUnion A = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨⟨i, j⟩, h⟩ := P.everyClass c
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩⟩
  have hreuse : (∑ i : Fin b, (A i).card) - (Finset.univ.biUnion A).card ≤ 2 := by
    simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hUnion]
    omega
  obtain ⟨R, hRs, hroots, hchildren⟩ := exists_root_child_partition A Finset.univ
    (fun i _ j _ hij => P.pairOverlap i j hij) hreuse
  exact ⟨R, hroots, fun i hin => hchildren i (Finset.mem_univ _) hin⟩

theorem exists_uniform_prescribed_roots {F : Type*} [DecidableEq F] {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), ∀ (a : Local.DirectionAssignment F b κ),
      Local.Eligible P a → ∀ bits : Local.Bits b,
      DisjointRoots (fun i => generatorSet (Local.prescribedTuple P a bits i)) R ∧
      ∀ i, i ∉ R →
        (generatorSet (Local.prescribedTuple P a bits i) ∩
          R.biUnion (fun j => generatorSet (Local.prescribedTuple P a bits j))).card = 1 ∧
        generatorSet (Local.prescribedTuple P a bits i) ∩
          (Finset.univ.erase i).biUnion
            (fun j => generatorSet (Local.prescribedTuple P a bits j)) ⊆
          R.biUnion (fun j => generatorSet (Local.prescribedTuple P a bits j)) := by
  obtain ⟨R, hroots, hchildren⟩ := exists_pattern_roots P hκ
  refine ⟨R, ?_⟩
  intro a ha bits
  have heq (i : Fin b) : generatorSet (Local.prescribedTuple P a bits i) =
      (Finset.univ.image (P.classOf i)).image a.2 := by
    simp only [generatorSet, Local.prescribedTuple, Finset.image_image]
    rfl
  simp_rw [heq]
  obtain ⟨hr, hc⟩ := partition_image (fun i => Finset.univ.image (P.classOf i))
    Finset.univ R a.2 ha.2.1 hroots (fun i _ hin => hchildren i hin)
  exact ⟨hr, fun i hin => hc i (Finset.mem_univ _) hin⟩

end Balanced.RootChildPartition

end OAI
