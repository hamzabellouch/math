import Mathlib
import OAI.Combinatorics.SharpRamsey.Model
import OAI.Combinatorics.SharpRamsey.Geometry.SpanPairLine

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey

namespace Foundation
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
theorem indepNum_lt_of_cliqueFree_compl {t : ℕ} (ht : Gᶜ.CliqueFree t) :
    G.indepNum < t := by
  by_contra! h
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  exact (ht.mono h) A (G.isNClique_compl.mpr hA)

omit [DecidableEq V] in
theorem maximum_indep_dominates {A : Finset V} (hA : G.IsMaximumIndepSet A)
    (x : V) : x ∈ A ∨ ∃ y ∈ A, G.Adj x y := by
  by_contra! hn
  have hi : G.IsIndepSet ((insert x A : Finset V) : Set V) := by
    intro u hu v hv huv
    simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · simp
    · exact hn.2 v hv
    · exact fun h => hn.2 u hu h.symm
    · exact hA.1 hu hv huv
  have hc := hA.2 (insert x A) hi
  rw [card_insert_of_notMem hn.1] at hc
  omega

theorem card_le_mul_indepNum {B : ℕ} (hdeg : ∀ x, G.degree x + 1 ≤ B) :
    Fintype.card V ≤ B * G.indepNum := by
  obtain ⟨A, hA⟩ := G.maximumIndepSet_exists
  have hcover : (univ : Finset V) ⊆ A.biUnion (fun x => insert x (G.neighborFinset x)) := by
    intro v _
    obtain hv | ⟨x, hx, hadj⟩ := maximum_indep_dominates G hA v
    · exact mem_biUnion.mpr ⟨v, hv, by simp⟩
    · exact mem_biUnion.mpr ⟨x, hx, by simp [hadj.symm]⟩
  calc
    Fintype.card V = (univ : Finset V).card := (card_univ).symm
    _ ≤ (A.biUnion (fun x => insert x (G.neighborFinset x))).card := card_le_card hcover
    _ ≤ ∑ x ∈ A, (insert x (G.neighborFinset x)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ A, B := by
      apply sum_le_sum
      intro x _
      simpa using hdeg x
    _ = B * G.indepNum := by
      simp [G.maximumIndepSet_card_eq_indepNum A hA, mul_comm]

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_neighbor {s : ℕ} (hs : G.CliqueFree (s+1)) (x : V) :
    (G.induce (G.neighborSet x)).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  have hc : G.CliqueFreeOn Set.univ (s+1) := (G.cliqueFreeOn_univ).mpr hs
  simpa using SimpleGraph.CliqueFreeOn.of_succ G hc (a := x) (Set.mem_univ x)

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_induce {s : ℕ} (hs : G.CliqueFree s) (U : Set V) :
    (G.induce U).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  intro A _ hA
  exact hs A hA
omit [Fintype V] [DecidableEq V] in

theorem compl_cliqueFree_induce {t : ℕ} (ht : Gᶜ.CliqueFree t) (U : Set V) :
    (G.induce U)ᶜ.CliqueFree t := by
  have he : (G.induce U)ᶜ = Gᶜ.induce U := by ext u v; simp [Subtype.val_inj]
  rw [he]
  exact cliqueFree_induce Gᶜ ht U

theorem order_avoiding_lt_pow (n : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.CliqueFree (n+2) → Gᶜ.CliqueFree t → Fintype.card V < t^(n+1) := by
  induction n with
  | zero =>
    intro V _ _ G hs hi
    have hg : G = ⊥ := G.cliqueFree_two.mp hs
    have hn := card_le_mul_indepNum G (B := 1) (by intro x; simp [hg])
    have hh := indepNum_lt_of_cliqueFree_compl G hi
    simpa using hn.trans_lt (by simpa using hh)
  | succ n ih =>
    intro V _ _ G hs hi
    have hd : ∀ x, G.degree x + 1 ≤ t^(n+1) := by
      intro x
      have hc := cliqueFree_neighbor G (s := n+2) (by simpa [Nat.add_assoc] using hs) x
      have hci := compl_cliqueFree_induce G hi (G.neighborSet x)
      have hh := ih (G.induce (G.neighborSet x)) hc hci
      rw [G.card_neighborSet_eq_degree] at hh
      omega
    have hn := card_le_mul_indepNum G hd
    have hi' := indepNum_lt_of_cliqueFree_compl G hi
    have hp : 0 < t^(n+1) := pow_pos (by omega) _
    have hm := Nat.mul_lt_mul_of_pos_left hi' hp
    calc
      Fintype.card V ≤ t^(n+1) * G.indepNum := hn
      _ < t^(n+1) * t := hm
      _ = t^(n+1+1) := (pow_succ _ _).symm

theorem ramseyProperty_pow (n : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    RamseyProperty (n+2) t (t^(n+1)) := by
  intro G
  by_cases hs : G.CliqueFree (n+2)
  · right
    by_contra! hi
    have hh := order_avoiding_lt_pow n ht G hs hi
    simp at hh
  · left
    simpa only [SimpleGraph.CliqueFree, not_forall, not_not] using hs

theorem ramseyProperty_nonempty {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    {N | RamseyProperty s t N}.Nonempty := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact ⟨t^(n+1), by simpa [Nat.add_comm] using ramseyProperty_pow n ht⟩

theorem ramsey_has_property {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    RamseyProperty s t (ramsey s t) := Nat.sInf_mem (ramseyProperty_nonempty hs ht)

omit [Fintype V] [DecidableEq V] in
 theorem clique_map_embedding {U : Type*} (f : U ↪ V) {n : ℕ} {A : Finset U}
    (hA : (G.comap f).IsNClique n A) : G.IsNClique n (A.map f) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hv
    exact hA.1 ha hb (fun h => huv (congrArg f h))
  · simpa using hA.2

omit [Fintype V] [DecidableEq V] in
 theorem compl_comap_embedding {U : Type*} (f : U ↪ V) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext u v
  simp [SimpleGraph.comap_adj, f.injective.eq_iff]

omit [DecidableEq V] in
theorem property_for_finite_type {s t N : ℕ} (hN : RamseyProperty s t N)
    (hcard : N ≤ Fintype.card V) :
    (∃ A, G.IsNClique s A) ∨ (∃ B, Gᶜ.IsNClique t B) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin N) (β := V) (by simpa using hcard)
  obtain ⟨A, hA⟩ | ⟨B, hB⟩ := hN (G.comap f)
  · exact Or.inl ⟨A.map f, clique_map_embedding G f hA⟩
  · rw [compl_comap_embedding G f] at hB
    exact Or.inr ⟨B.map f, clique_map_embedding Gᶜ f hB⟩
omit [DecidableEq V] in

theorem order_lt_ramsey {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hGs : G.CliqueFree s) (hGt : Gᶜ.CliqueFree t) :
    Fintype.card V < ramsey s t := by
  by_contra! h
  obtain ⟨A, hA⟩ | ⟨B, hB⟩ := property_for_finite_type G (ramsey_has_property hs ht) h
  · exact hGs A hA
  · exact hGt B hB

theorem ramsey_le_of_property {s t N : ℕ} (hN : RamseyProperty s t N) :
    ramsey s t ≤ N := Nat.sInf_le hN

theorem property_mono {s t N M : ℕ} (hN : RamseyProperty s t N) (hNM : N ≤ M) :
    RamseyProperty s t M := by
  intro G
  exact property_for_finite_type G hN (by simpa using hNM)

theorem ramsey_le_pow {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    ramsey s t ≤ t^(s-1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hh := ramsey_le_of_property (ramseyProperty_pow n ht)
  simpa [Nat.add_comm] using hh

theorem le_ramsey {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) : t ≤ ramsey s t := by
  obtain ⟨A,hA⟩ | ⟨B,hB⟩ := ramsey_has_property hs ht (⊥ : SimpleGraph (Fin (ramsey s t)))
  · exact False.elim ((SimpleGraph.cliqueFree_bot (by omega : 1 < s)) A hA)
  · have hb := card_le_card (subset_univ B)
    simpa [hB.2] using hb

theorem ramsey_two {t : ℕ} (ht : 1 ≤ t) : ramsey 2 t = t := by
  apply Nat.le_antisymm
  · simpa using ramsey_le_pow (s := 2) (by omega) ht
  · exact le_ramsey (by omega) ht

omit [Fintype V] [DecidableEq V] in
theorem cliqueFree_common {s : ℕ} (hs : G.CliqueFree (s+2))
    {x y : V} (hxy : G.Adj x y) :
    (G.induce (G.commonNeighbors x y)).CliqueFree s := by
  rw [G.cliqueFree_induce_iff]
  have hc : G.CliqueFreeOn Set.univ (s+2) := (G.cliqueFreeOn_univ).mpr hs
  have hn : G.CliqueFreeOn (G.neighborSet x) (s+1) := by
    simpa using SimpleGraph.CliqueFreeOn.of_succ G hc (a := x) (Set.mem_univ x)
  exact SimpleGraph.CliqueFreeOn.of_succ G hn hxy

theorem exists_avoiding_pred {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ G : SimpleGraph (Fin (ramsey s t - 1)), G.CliqueFree s ∧ Gᶜ.CliqueFree t := by
  have hr : 2 ≤ ramsey s t := ht.trans (le_ramsey hs (by omega))
  have hn : ¬ RamseyProperty s t (ramsey s t - 1) := by
    intro h
    have hh := ramsey_le_of_property h
    omega
  simp only [RamseyProperty, not_forall, not_or, not_exists] at hn
  exact hn

end Foundation
end SharpLogRamsey

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def independentSets : Finset (Finset V) :=
  univ.filter (fun S => G.IsIndepSet (S : Set V))

@[simp] theorem mem_independentSets (S : Finset V) :
    S ∈ independentSets G ↔ G.IsIndepSet (S : Set V) := by
  simp [independentSets]

theorem independentSets_nonempty : (independentSets G).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [SimpleGraph.IsIndepSet]

noncomputable def closed (x : V) : Finset V := insert x (G.neighborFinset x)
noncomputable def outside (x : V) (S : Finset V) : Finset V := S \ closed G x
noncomputable def available (x : V) (J : Finset V) : Finset V :=
  (G.neighborFinset x).filter (fun u => ∀ v ∈ J, ¬G.Adj u v)
noncomputable def fiber (x : V) (J : Finset V) : Finset (Finset V) :=
  (independentSets G).filter (fun S => outside G x S = J)

def Admissible (x : V) (J : Finset V) : Prop :=
  G.IsIndepSet (J : Set V) ∧ Disjoint J (closed G x)

@[simp] theorem mem_closed (x u : V) : u ∈ closed G x ↔ u = x ∨ G.Adj x u := by
  simp [closed]
@[simp] theorem mem_outside (x u : V) (S : Finset V) :
    u ∈ outside G x S ↔ u ∈ S ∧ u ≠ x ∧ ¬G.Adj x u := by
  simp [outside]
@[simp] theorem mem_available (x u : V) (J : Finset V) :
    u ∈ available G x J ↔ G.Adj x u ∧ ∀ v ∈ J, ¬G.Adj u v := by
  simp [available]

@[simp] theorem center_not_available (x : V) (J : Finset V) : x ∉ available G x J := by
  simp

theorem admissible_outside (x : V) {S : Finset V}
    (hS : S ∈ independentSets G) : Admissible G x (outside G x S) := by
  constructor
  · exact (mem_independentSets G S |>.mp hS).mono (by
      intro u hu; exact (mem_outside G x u S |>.mp hu).1)
  · exact disjoint_left.mpr (fun u hu hc => (Finset.mem_sdiff.mp hu).2 hc)

theorem admissible_not_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : x ∉ J := by
  intro hx
  exact disjoint_left.mp hJ.2 hx (by simp)

theorem admissible_not_adj {x u : V} {J : Finset V}
    (hJ : Admissible G x J) (hu : u ∈ J) : ¬G.Adj x u := by
  intro h
  exact disjoint_left.mp hJ.2 hu (by simp [h])

theorem available_disjoint {x : V} {J : Finset V}
    (hJ : Admissible G x J) : Disjoint J (available G x J) := by
  apply disjoint_left.mpr
  intro u hJ' hu
  exact admissible_not_adj G hJ hJ' (mem_available G x u J |>.mp hu).1

theorem independent_insert_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : G.IsIndepSet ((insert x J : Finset V) : Set V) := by
  intro u hu v hv huv
  simp only [mem_coe, mem_insert] at hu hv
  rcases hu with rfl | hu
  · rcases hv with rfl | hv
    · simp
    · exact admissible_not_adj G hJ hv
  · rcases hv with rfl | hv
    · exact fun h => admissible_not_adj G hJ hu h.symm
    · exact hJ.1 hu hv huv

theorem independent_extend (htri : G.CliqueFree 3) {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    G.IsIndepSet ((J ∪ K : Finset V) : Set V) := by
  intro u hu v hv huv
  simp only [mem_coe, mem_union] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hJ.1 hu hv huv
  · exact fun h => (mem_available G x v J |>.mp (hK hv)).2 u hu h.symm
  · exact (mem_available G x u J |>.mp (hK hu)).2 v hv
  · exact (G.isIndepSet_neighborSet_of_triangleFree htri x)
      (mem_available G x u J |>.mp (hK hu)).1
      (mem_available G x v J |>.mp (hK hv)).1 huv

theorem outside_insert_center {x : V} {J : Finset V}
    (hJ : Admissible G x J) : outside G x (insert x J) = J := by
  ext u
  simp only [mem_outside, mem_insert]
  constructor
  · rintro ⟨h, hne, _⟩
    exact h.resolve_left hne
  · intro hu
    exact ⟨Or.inr hu, fun h => admissible_not_center G hJ (h ▸ hu),
      admissible_not_adj G hJ hu⟩

theorem outside_extend {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    outside G x (J ∪ K) = J := by
  ext u
  simp only [mem_outside, mem_union]
  constructor
  · rintro ⟨hu | hu, _, hna⟩
    · exact hu
    · exact False.elim (hna (mem_available G x u J |>.mp (hK hu)).1)
  · intro hu
    exact ⟨Or.inl hu, fun h => admissible_not_center G hJ (h ▸ hu),
      admissible_not_adj G hJ hu⟩

theorem fiber_eq (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) :
    fiber G x J = insert (insert x J)
      ((available G x J).powerset.image (fun K => J ∪ K)) := by
  ext S
  simp only [fiber, mem_filter, mem_independentSets, mem_insert, mem_image,
    mem_powerset]
  constructor
  · rintro ⟨hS, hout⟩
    by_cases hx : x ∈ S
    · left
      ext u
      simp only [mem_insert]
      constructor
      · intro hu
        by_cases hux : u = x
        · exact Or.inl hux
        · right
          rw [← hout, mem_outside]
          exact ⟨hu, hux, hS hx hu (Ne.symm hux)⟩
      · rintro (rfl | hu)
        · exact hx
        · rw [← hout, mem_outside] at hu
          exact hu.1
    · right
      refine ⟨S ∩ G.neighborFinset x, ?_, ?_⟩
      · intro u hu
        simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hu
        apply (mem_available G x u J).mpr
        refine ⟨hu.2, ?_⟩
        intro v hv hadj
        have hvS : v ∈ S := by rw [← hout, mem_outside] at hv; exact hv.1
        exact hS hu.1 hvS hadj.ne hadj
      · ext u
        simp only [mem_union, mem_inter, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro (hu | hu)
          · rw [← hout, mem_outside] at hu; exact hu.1
          · exact hu.1
        · intro hu
          by_cases hax : G.Adj x u
          · exact Or.inr ⟨hu, hax⟩
          · left
            rw [← hout, mem_outside]
            exact ⟨hu, fun h => hx (h ▸ hu), hax⟩
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact ⟨independent_insert_center G hJ, outside_insert_center G hJ⟩
    · exact ⟨independent_extend G htri hJ hK, outside_extend G hJ hK⟩

theorem extend_injective {x : V} {J : Finset V} (hJ : Admissible G x J) :
    Set.InjOn (fun K => J ∪ K) ((available G x J).powerset : Set (Finset V)) := by
  intro K hK L hL heq
  have hdK : Disjoint J K := (available_disjoint G hJ).mono_right (mem_powerset.mp hK)
  have hdL : Disjoint J L := (available_disjoint G hJ).mono_right (mem_powerset.mp hL)
  simpa [union_sdiff_cancel_left hdK, union_sdiff_cancel_left hdL] using
    congrArg (fun S => S \ J) heq

theorem center_choice_not_image {x : V} {J : Finset V} (hJ : Admissible G x J) :
    insert x J ∉ (available G x J).powerset.image (fun K => J ∪ K) := by
  rintro h
  obtain ⟨K, hK, heq⟩ := mem_image.mp h
  have hx : x ∈ J ∪ K := heq ▸ mem_insert_self x J
  rcases mem_union.mp hx with hx | hx
  · exact admissible_not_center G hJ hx
  · exact center_not_available G x J (mem_powerset.mp hK hx)

theorem card_fiber (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) : (fiber G x J).card = 1 + 2^(available G x J).card := by
  rw [fiber_eq G htri hJ, card_insert_of_notMem (center_choice_not_image G hJ),
    card_image_of_injOn (extend_injective G hJ), card_powerset]
  omega

theorem sum_fiber (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) (f : Finset V → ℝ) :
    ∑ S ∈ fiber G x J, f S = f (insert x J) +
      ∑ K ∈ (available G x J).powerset, f (J ∪ K) := by
  rw [fiber_eq G htri hJ, sum_insert (center_choice_not_image G hJ),
    sum_image (extend_injective G hJ)]

omit [Fintype V] in

theorem twice_sum_powerset_card (A : Finset V) :
    2 * (∑ K ∈ A.powerset, (K.card : ℝ)) = A.card * (2:ℝ)^A.card := by
  have hc : ∑ K ∈ A.powerset, ((A \ K).card : ℝ) =
      ∑ K ∈ A.powerset, (K.card : ℝ) := by
    apply sum_bij (fun K _ => A \ K)
    · intro K _; exact mem_powerset.mpr sdiff_subset
    · intro K hK L hL heq
      have := congrArg (fun X => A \ X) heq
      simpa [Finset.sdiff_sdiff_eq_self (mem_powerset.mp hK),
        Finset.sdiff_sdiff_eq_self (mem_powerset.mp hL)] using this
    · intro K hK
      exact ⟨A \ K, mem_powerset.mpr sdiff_subset,
        Finset.sdiff_sdiff_eq_self (mem_powerset.mp hK)⟩
    · intro K _; rfl
  have hsum : ∑ K ∈ A.powerset, (((A \ K).card : ℝ) + K.card) =
      A.card * (2:ℝ)^A.card := by
    calc
      _ = ∑ _K ∈ A.powerset, (A.card : ℝ) := by
        apply sum_congr rfl
        intro K hK
        exact_mod_cast card_sdiff_add_card_eq_card (mem_powerset.mp hK)
      _ = _ := by simp [card_powerset]; ring
  rw [sum_add_distrib, hc] at hsum
  linarith

theorem center_neighbor_inter {x : V} {J : Finset V}
    (hJ : Admissible G x J) : insert x J ∩ G.neighborFinset x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  simp only [mem_inter, mem_insert, SimpleGraph.mem_neighborFinset] at hu
  rcases hu.1 with rfl | huJ
  · exact G.irrefl hu.2
  · exact admissible_not_adj G hJ huJ hu.2

theorem extend_neighbor_inter {x : V} {J K : Finset V}
    (hJ : Admissible G x J) (hK : K ⊆ available G x J) :
    (J ∪ K) ∩ G.neighborFinset x = K := by
  ext u
  simp only [mem_inter, mem_union, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hu | hu, hadj⟩
    · exact False.elim (admissible_not_adj G hJ hu hadj)
    · exact hu
  · intro hu
    exact ⟨Or.inr hu, (mem_available G x u J |>.mp (hK hu)).1⟩

end SharpLogRamsey.TriangleFree
end

end OAI
