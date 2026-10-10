import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths
import OAI.Combinatorics.Ramsey.CycleClique.Density
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem ncard_union_layers {V : Type*} [Fintype V] {ι : Type*}
    (D : ι → Set V) (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (F : Finset ι) : (⋃ i ∈ F, D i).ncard = ∑ i ∈ F, (D i).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    rw [hu, Set.ncard_union_eq, Finset.sum_insert hi, ih]
    apply Set.disjoint_left.mpr
    intro v hvi hvF
    obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
    exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj

 
theorem sum_independence_layers {V : Type*} [Fintype V] {ι : Type*}
    (G : SimpleGraph V) (D : ι → Set V)
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (F : Finset ι)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      ∀ x ∈ D i, ∀ y ∈ D j, ¬ G.Adj x y) :
    ∑ i ∈ F, independence G (D i) ≤ independence G (⋃ i ∈ F, D i) := by
  classical
  revert hsep
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    intro hsep
    have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    rw [hu, Finset.sum_insert hi]
    have hD : Disjoint (D i) (⋃ j ∈ F, D j) := by
      apply Set.disjoint_left.mpr
      intro v hvi hvF
      obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
      exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj
    calc
      _ ≤ independence G (D i) + independence G (⋃ j ∈ F, D j) := by
        exact Nat.add_le_add_left (ih (fun j hj l hl hne =>
          hsep j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) hne)) _
      _ ≤ _ := independence_add_le Set.subset_union_left Set.subset_union_right hD (by
        intro x hx y hy
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
        exact hsep i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj) x hx y hyj)

 
def distanceLayer {V : Type*} (G : SimpleGraph V) (r : V) (i : ℕ) : Set V :=
  {v | G.Reachable r v ∧ G.dist r v = i}

@[simp] theorem distanceLayer_zero {V : Type*} (G : SimpleGraph V) (r : V) :
    distanceLayer G r 0 = {r} := by
  ext v
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.mp hd).symm
  · rintro rfl
    exact ⟨.refl _, G.dist_self⟩

theorem distanceLayer_disjoint {V : Type*} (G : SimpleGraph V) (r : V) :
    Pairwise (fun i j => Disjoint (distanceLayer G r i) (distanceLayer G r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hv₁ hv₂
  exact hij (hv₁.2.symm.trans hv₂.2)

theorem distanceLayer_no_edge {V : Type*} {G : SimpleGraph V} {r : V}
    {i j : ℕ} (hne : i ≠ j) (hpar : i % 2 = j % 2)
    {x y : V} (hx : x ∈ distanceLayer G r i) (hy : y ∈ distanceLayer G r j) :
    ¬ G.Adj x y := by
  intro hxy
  have hd := hxy.diff_dist_adj (u := r)
  rw [hx.2, hy.2] at hd
  omega

 
def parityIndices (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)

 
def paritySum (α : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ parityIndices i, α j

@[simp] theorem paritySum_zero (α : ℕ → ℕ) : paritySum α 0 = α 0 := by
  simp [paritySum, parityIndices, Finset.sum_filter]

theorem paritySum_add_prev (α : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    paritySum α i + paritySum α (i - 1) = ∑ j ∈ Finset.range (i + 1), α j := by
  unfold paritySum parityIndices
  rw [Finset.sum_filter, Finset.sum_filter]
  have hip : i - 1 + 1 = i := by omega
  rw [hip]
  have hpar : i % 2 ≠ (i - 1) % 2 := by omega
  have hex : (∑ j ∈ Finset.range i, if j % 2 = (i - 1) % 2 then α j else 0) =
      ∑ j ∈ Finset.range (i + 1), if j % 2 = (i - 1) % 2 then α j else 0 := by
    rw [Finset.sum_range_succ, ite_eq_right hpar, Nat.add_zero]
  rw [hex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : j % 2 = i % 2
  · have hne : j % 2 ≠ (i - 1) % 2 := by omega
    simp only [ite_eq_left he, ite_eq_right hne, Nat.add_zero]
  · have he' : j % 2 = (i - 1) % 2 := by omega
    simp only [ite_eq_right he, ite_eq_left he', Nat.zero_add]

 
theorem parity_independence_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V) (i : ℕ) :
    paritySum (fun j => independence G (distanceLayer G r j)) i ≤ G.indepNum := by
  apply le_trans (sum_independence_layers G (distanceLayer G r)
    (distanceLayer_disjoint G r) (parityIndices i) ?_)
  · simpa [independence_univ] using
      (independence_mono (G := G) (Set.subset_univ (⋃ j ∈ parityIndices i, distanceLayer G r j)))
  · intro j hj l hl hne x hx y hy
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range] at hj hl
    exact distanceLayer_no_edge hne (hj.2.trans hl.2.symm) hx hy

@[simp] theorem independence_singleton {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) : independence G {v} = 1 := by
  have hp := independence_pos (G := G) (Set.singleton_nonempty v)
  have hc := independence_le_card G {v}
  simp only [Set.ncard_singleton] at hc
  omega

 
theorem distanceLayer_one_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 1 ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    (distanceLayer G r 1).Nonempty := by
  classical
  have h := hexp {r} (Set.pairwise_singleton _ _) (Set.singleton_nonempty r)
  simp only [Set.ncard_singleton, Nat.mul_one, closedNeighborhood_singleton_card] at h
  have hpos : 0 < (G.neighborSet r).ncard := by
    rw [ncard_neighborSet]
    omega
  obtain ⟨v, hv⟩ := (Set.ncard_pos).mp hpos
  have hr : G.Adj r v := hv
  exact ⟨v, hr.reachable, G.dist_eq_one_iff_adj.mpr hr⟩

 
theorem parity_layer_union_nonempty {V : Type*} {G : SimpleGraph V} {r : V}
    (hD : (distanceLayer G r 1).Nonempty) (i : ℕ) :
    (⋃ j ∈ parityIndices i, distanceLayer G r j).Nonempty := by
  by_cases hi : i % 2 = 0
  · refine ⟨r, Set.mem_iUnion₂.mpr ⟨0, ?_, ?_⟩⟩
    · simp [parityIndices, hi]
    · simp
  · obtain ⟨v, hv⟩ := hD
    refine ⟨v, Set.mem_iUnion₂.mpr ⟨1, ?_, hv⟩⟩
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range]
    omega

 
theorem closedNeighborhood_parity_layers {V : Type*} {G : SimpleGraph V}
    {r : V} {i : ℕ} {I : Set V}
    (hI : I ⊆ ⋃ j ∈ parityIndices i, distanceLayer G r j) :
    closedNeighborhood G I ⊆ ⋃ j ∈ Finset.range (i + 2), distanceLayer G r j := by
  intro v hv
  rcases hv with hv | ⟨w, hw, hwv⟩
  · obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp (hI hv)
    have hji : j < i + 1 := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hvj⟩
  · obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp (hI hw)
    have hji : j < i + 1 := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    have hd := hwv.diff_dist_adj (u := r)
    rw [hwj.2] at hd
    exact Set.mem_iUnion₂.mpr ⟨G.dist r v, Finset.mem_range.mpr (by omega),
      hwj.1.trans hwv.reachable, rfl⟩

 
theorem distance_layer_sum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 1 ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (r : V) {i : ℕ} (hi : 1 ≤ i) :
    k * paritySum (fun j => independence G (distanceLayer G r j)) (i - 1) ≤
      ∑ j ∈ Finset.range i, (distanceLayer G r (j + 1)).ncard := by
  classical
  let U := ⋃ j ∈ parityIndices (i - 1), distanceLayer G r j
  have hUne := parity_layer_union_nonempty (distanceLayer_one_nonempty hk hexp r) (i - 1)
  obtain ⟨I, hIU, hI, hcI⟩ := exists_indep_of_independence G U
  have hneI : I.Nonempty := (Set.ncard_pos).mp (by
    rw [hcI]
    exact independence_pos hUne)
  have hp : paritySum (fun j => independence G (distanceLayer G r j)) (i - 1) ≤
      independence G U := by
    apply sum_independence_layers G (distanceLayer G r) (distanceLayer_disjoint G r)
    intro j hj l hl hne x hx y hy
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range] at hj hl
    exact distanceLayer_no_edge hne (hj.2.trans hl.2.symm) hx hy
  have hN := closedNeighborhood_parity_layers hIU
  have hcard := Set.ncard_le_ncard hN
  rw [ncard_union_layers _ (distanceLayer_disjoint G r)] at hcard
  have hii : i - 1 + 2 = i + 1 := by omega
  rw [hii, Finset.sum_range_succ', distanceLayer_zero, Set.ncard_singleton] at hcard
  have he := hexp I hI hneI
  have hm := Nat.mul_le_mul_left k hp
  rw [← hcI] at hm
  omega

 

theorem exists_dense_layer_numeric (α n : ℕ → ℕ) {s ε : ℕ}
    (hs : 4 ≤ s) (hε : ε ≤ 1) (hα₀ : α 0 = 1) (hn₁ : 0 < n 1)
    (hpbound : ∀ i, paritySum α i ≤ 2 * s + ε)
    (hlayer : ∀ i, 1 ≤ i → i ≤ s →
      (2 * s + ε) * paritySum α (i - 1) ≤ ∑ j ∈ Finset.range i, n (j + 1)) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ 0 < n i ∧ s * α i + ε ≤ n i := by
  classical
  by_contra hn
  push Not at hn
  have hweak : ∀ i, 1 ≤ i → i ≤ s → n i ≤ s * α i := by
    intro i hi his
    by_cases hni : 0 < n i
    · have := hn i hi his hni
      omega
    · omega
  have hsum : ∀ i, 1 ≤ i → i ≤ s →
      (∑ j ∈ Finset.range i, n (j + 1)) ≤ s * ∑ j ∈ Finset.range i, α (j + 1) := by
    intro i hi his
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact hweak (j + 1) (by omega) (by omega)
  have hstrict : ε = 0 → ∀ i, 1 ≤ i → i ≤ s →
      (∑ j ∈ Finset.range i, n (j + 1)) < s * ∑ j ∈ Finset.range i, α (j + 1) := by
    intro he i hi his
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      exact hweak (j + 1) (by omega) (by omega)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have := hn 1 (by omega) (by omega) hn₁
      simpa [he] using this
  have hid : ∀ i, 1 ≤ i →
      (∑ j ∈ Finset.range i, α (j + 1)) + 1 = paritySum α i + paritySum α (i - 1) := by
    intro i hi
    have h := paritySum_add_prev α hi
    rw [Finset.sum_range_succ', hα₀] at h
    exact h.symm
  have hstep : ∀ i, 1 ≤ i → i ≤ s → 0 < paritySum α (i - 1) →
      paritySum α (i - 1) + 2 ≤ paritySum α i := by
    intro i hi his hp
    have hl := hlayer i hi his
    have hw := hsum i hi his
    have heq := hid i hi
    by_contra hbad
    have hcomp := Nat.mul_le_mul_left s
      (show paritySum α i ≤ paritySum α (i - 1) + 1 by omega)
    by_cases he : ε = 0
    · have hst := hstrict he i hi his
      rw [he, Nat.add_zero] at hl
      nlinarith
    · have he₁ : ε = 1 := by omega
      rw [he₁] at hl
      nlinarith
  have hgrowth : ∀ i, i ≤ s → 2 * i + 1 ≤ paritySum α i := by
    intro i
    induction i with
    | zero => simp [hα₀]
    | succ i ih =>
      intro his
      have hi := ih (by omega)
      have hst := hstep (i + 1) (by omega) his (by simpa using (show 0 < paritySum α i by omega))
      simp only [Nat.add_sub_cancel] at hst
      omega
  have hupper := hpbound s
  by_cases he : ε = 0
  · have := hgrowth s (by omega)
    omega
  · have he₁ : ε = 1 := by omega
    have hprev := hgrowth (s - 1) (by omega)
    have hppos : s < paritySum α (s - 1) := by omega
    have hlast : paritySum α (s - 1) + 3 ≤ paritySum α s := by
      have hl := hlayer s (by omega) (by omega)
      rw [he₁] at hl
      have hw := hsum s (by omega) (by omega)
      have heq := hid s (by omega)
      by_contra hbad
      have hcomp := Nat.mul_le_mul_left s
        (show paritySum α s ≤ paritySum α (s - 1) + 2 by omega)
      nlinarith
    omega

 
theorem exists_dense_distance_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    ∃ i, 1 ≤ i ∧ i ≤ k / 2 ∧ (distanceLayer G r i).Nonempty ∧
      (k / 2) * independence G (distanceLayer G r i) + k % 2 ≤
        (distanceLayer G r i).ncard := by
  classical
  have hmod : 2 * (k / 2) + k % 2 = k := by omega
  obtain ⟨i, hi, his, hpos, hd⟩ := exists_dense_layer_numeric
    (fun j => independence G (distanceLayer G r j))
    (fun j => (distanceLayer G r j).ncard)
    (s := k / 2) (ε := k % 2) (by omega) (by omega) (by simp)
    ((Set.ncard_pos).mpr (distanceLayer_one_nonempty (by omega) hexp r))
    (by intro i; rw [hmod]; exact (parity_independence_bound G r i).trans hα)
    (by intro i hi his; rw [hmod]; exact distance_layer_sum (by omega) hexp r hi)
  exact ⟨i, hi, his, (Set.ncard_pos).mp hpos, hd⟩

 
theorem exists_minimal_dense_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    ∃ i, 1 ≤ i ∧ i ≤ k / 2 ∧ ∃ S ⊆ distanceLayer G r i,
      S.Nonempty ∧ MinimalDensity (G.induce S) (k / 2) (k % 2) := by
  obtain ⟨i, hi, his, hD, hd⟩ := exists_dense_distance_layer hk hα hexp r
  obtain ⟨S, hSD, hS, hmin⟩ := exists_minimal_density G (k / 2) (k % 2) hD hd
  exact ⟨i, hi, his, S, hSD, hS, hmin⟩

end CycleClique

end OAI
