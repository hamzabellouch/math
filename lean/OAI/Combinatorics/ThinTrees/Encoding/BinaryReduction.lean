import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.Specification

namespace OAI

/-! Binary reduction. -/

section

namespace AlgorithmicThinTrees
open StrongThinTree Finset

lemma sum_min_capacity {ι : Type*} (s : Finset ι) (c : ι → ℕ) (k : ℕ)
    (hk : k ≤ ∑ i ∈ s, c i) : k ≤ ∑ i ∈ s, min (c i) k := by
  classical
  by_cases h : ∃ i ∈ s, k ≤ c i
  · obtain ⟨i, hi, hc⟩ := h
    calc
      k = min (c i) k := (min_eq_right hc).symm
      _ ≤ ∑ j ∈ s, min (c j) k := single_le_sum (fun j _ => show 0 ≤ min (c j) k from Nat.zero_le _) hi
  · have hc : ∀ i ∈ s, c i ≤ k := by
      intro i hi
      have h' : ¬ k ≤ c i := fun h' => h ⟨i, hi, h'⟩
      omega
    simpa only [sum_congr rfl (fun i hi => min_eq_left (hc i hi))] using hk

lemma sum_div_rounding {ι : Type*} (s : Finset ι) (c : ι → ℕ) {k : ℕ}
    (hk : 0 < k) (b : ℕ) (hc : k ≤ ∑ i ∈ s, c i) :
    b ≤ (∑ i ∈ s, b * c i / k) + s.card := by
  have hi (i : ι) : b * c i ≤ k * (b * c i / k + 1) := by
    have hmod := Nat.mod_lt (b * c i) hk
    have hid := Nat.mod_add_div (b * c i) k
    nlinarith
  have hs := sum_le_sum (fun i (_ : i ∈ s) => hi i)
  have hleft : b * k ≤ ∑ i ∈ s, b * c i := by
    rw [← mul_sum]
    exact Nat.mul_le_mul_left b hc
  have hright : (∑ i ∈ s, k * (b * c i / k + 1)) =
      k * ((∑ i ∈ s, b * c i / k) + s.card) := by
    simp [mul_add, sum_add_distrib, mul_sum, Nat.mul_comm]
  rw [hright] at hs
  have hfinal : k * b ≤ k * ((∑ i ∈ s, b * c i / k) + s.card) := by
    simpa only [Nat.mul_comm b k] using hleft.trans hs
  exact Nat.le_of_mul_le_mul_left hfinal hk

namespace BinaryInput

def crossing (x : BinaryInput) (S : Finset (Fin x.n)) : Finset (Fin x.p) :=
  univ.filter fun i => (x.left i ∈ S ∧ x.right i ∉ S) ∨
    (x.right i ∈ S ∧ x.left i ∉ S)

lemma cut_card (x : BinaryInput) (S : Finset (Fin x.n)) :
    (x.graph.cut univ S).card = ∑ i ∈ x.crossing S, x.multiplicity i := by
  classical
  rw [MultiGraph.cut, card_filter]
  rw [← x.edgeEquiv.sum_comp]
  simp only [graph, Equiv.symm_apply_apply]
  rw [Fintype.sum_sigma]
  simp [crossing, sum_filter]
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp

lemma pairs_bound (x : BinaryInput) (hn : 0 < x.n) : 2 * x.p < x.n ^ 2 := by
  classical
  let P : Finset (Fin x.n × Fin x.n) := univ.image (fun i => (x.left i, x.right i))
  let Q : Finset (Fin x.n × Fin x.n) := univ.image (fun i => (x.right i, x.left i))
  have hP : P.card = x.p := by simp [P, card_image_of_injective _ x.distinct]
  have hinj : Function.Injective (fun i : Fin x.p => (x.right i, x.left i)) := by
    intro i j hij
    apply x.distinct
    exact Prod.ext (congrArg Prod.snd hij) (congrArg Prod.fst hij)
  have hQ : Q.card = x.p := by simp [Q, card_image_of_injective _ hinj]
  have hdis : Disjoint P Q := by
    rw [disjoint_left]
    rintro a ha hb
    obtain ⟨i, _, hi⟩ := mem_image.mp ha
    obtain ⟨j, _, hj⟩ := mem_image.mp hb
    have he : (x.left i, x.right i) = (x.right j, x.left j) := hi.trans hj.symm
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    have hli := x.ordered i
    have hlj := x.ordered j
    simp only at he₁ he₂
    rw [he₁, he₂] at hli
    exact (not_lt_of_gt hlj) hli
  have hmiss : ((⟨0, hn⟩ : Fin x.n), (⟨0, hn⟩ : Fin x.n)) ∉ P ∪ Q := by
    intro h
    rcases mem_union.mp h with h | h
    · obtain ⟨i, _, he⟩ := mem_image.mp h
      have hl := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      have ho := x.ordered i
      simp only at hl hr
      rw [hl, hr] at ho
      exact (lt_irrefl _) ho
    · obtain ⟨i, _, he⟩ := mem_image.mp h
      have hl := congrArg Prod.snd he
      have hr := congrArg Prod.fst he
      have ho := x.ordered i
      simp only at hl hr
      rw [hl, hr] at ho
      exact (lt_irrefl _) ho
  have hproper : P ∪ Q ⊂ univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
    intro he
    exact hmiss (he.symm ▸ mem_univ _)
  have hcard := card_lt_card hproper
  rw [card_union_of_disjoint hdis, hP, hQ] at hcard
  simpa [sq, two_mul] using hcard

abbrev reduced (x : BinaryInput) : BinaryInput where
  n := x.n
  p := x.p
  k := x.n ^ 2
  left := x.left
  right := x.right
  ordered := x.ordered
  distinct := x.distinct
  multiplicity i := 2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k

lemma reduced_crossing (x : BinaryInput) (S : Finset (Fin x.n)) :
    x.reduced.crossing S = x.crossing S := rfl

lemma reduced_multiplicity_le (x : BinaryInput) (hk : 0 < x.k) (i : Fin x.p) :
    x.reduced.multiplicity i ≤ 2 * x.n ^ 2 := by
  change 2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k ≤ _
  have h := Nat.div_le_div_right (c := x.k) (Nat.mul_le_mul_left (2 * x.n ^ 2)
    (min_le_right (x.multiplicity i) x.k))
  simpa [Nat.ne_of_gt hk] using h

lemma reduced_edgeConnected (x : BinaryInput) (hn : 0 < x.n) (hk : 0 < x.k)
    (hc : x.graph.EdgeConnected x.k) : x.reduced.graph.EdgeConnected (x.n ^ 2) := by
  intro S hS hS'
  have hc' := hc S hS hS'
  rw [cut_card] at hc'
  have hmin := sum_min_capacity (x.crossing S) x.multiplicity x.k hc'
  have hround := sum_div_rounding (x.crossing S)
    (fun i => min (x.multiplicity i) x.k) hk (2 * x.n ^ 2) hmin
  rw [cut_card, reduced_crossing]
  have hcard : (x.crossing S).card ≤ x.n ^ 2 := by
    have hle := card_le_card (filter_subset (fun i =>
      (x.left i ∈ S ∧ x.right i ∉ S) ∨ (x.right i ∈ S ∧ x.left i ∉ S)) univ)
    change (x.crossing S).card ≤ (univ : Finset (Fin x.p)).card at hle
    simp only [card_univ, Fintype.card_fin] at hle
    have hp := x.pairs_bound hn
    omega
  change x.n ^ 2 ≤ ∑ i ∈ x.crossing S, 2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k
  omega

lemma reduced_size (x : BinaryInput) (hn : 0 < x.n) (hk : 0 < x.k) :
    Fintype.card x.reduced.Edge < x.n ^ 4 := by
  have hsize : Fintype.card x.reduced.Edge ≤ x.p * (2 * x.n ^ 2) := by
    simp only [Edge, Fintype.card_sigma, Fintype.card_fin]
    calc
      ∑ i : Fin x.p, x.reduced.multiplicity i ≤ ∑ _ : Fin x.p, 2 * x.n ^ 2 :=
        sum_le_sum (fun i _ => reduced_multiplicity_le x hk i)
      _ = _ := by simp
  have hp := x.pairs_bound hn
  have hn2 : 0 < x.n ^ 2 := pow_pos hn 2
  have hlt := Nat.mul_lt_mul_of_pos_right hp hn2
  nlinarith

lemma reduced_cut_upper (x : BinaryInput) (hk : 0 < x.k) (S : Finset (Fin x.n)) :
    ((x.reduced.graph.cut univ S).card : ℝ) ≤
      (2 * (x.n : ℝ) ^ 2 / (x.k : ℝ)) * (x.graph.cut univ S).card := by
  have hkR : (0 : ℝ) < x.k := Nat.cast_pos.mpr hk
  have hterm (i : Fin x.p) :
      (x.reduced.multiplicity i : ℝ) ≤
        2 * (x.n : ℝ) ^ 2 / (x.k : ℝ) * x.multiplicity i := by
    have hnat : x.k * x.reduced.multiplicity i ≤
        2 * x.n ^ 2 * x.multiplicity i := by
      have h₁ := Nat.div_mul_le_self (2 * x.n ^ 2 * min (x.multiplicity i) x.k) x.k
      have h₂ := Nat.mul_le_mul_left (2 * x.n ^ 2) (min_le_left (x.multiplicity i) x.k)
      change x.k * (2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k) ≤ _
      simpa [Nat.mul_comm] using h₁.trans h₂
    have hreal : (x.k : ℝ) * x.reduced.multiplicity i ≤
        2 * (x.n : ℝ) ^ 2 * x.multiplicity i := by exact_mod_cast hnat
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hkR).mpr
    simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using hreal
  rw [x.reduced.cut_card S, x.cut_card S, reduced_crossing, Nat.cast_sum, Nat.cast_sum, mul_sum]
  exact sum_le_sum (fun i _ => hterm i)

end BinaryInput
end AlgorithmicThinTrees

namespace StrongThinTree.MultiGraph
open Finset

lemma cut_image {n m m' : ℕ} (G : MultiGraph n m) (H : MultiGraph n m')
    (f : Fin m → Fin m') (hl : ∀ e, H.left (f e) = G.left e)
    (hr : ∀ e, H.right (f e) = G.right e) (T : Finset (Fin m))
    (S : Finset (Fin n)) : H.cut (T.image f) S = (G.cut T S).image f := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨a, ha, rfl⟩, hcross⟩ := mem_filter.mp he |>.imp_left mem_image.mp
    refine mem_image.mpr ⟨a, ?_, rfl⟩
    exact mem_filter.mpr ⟨ha, by simpa [hl, hr] using hcross⟩
  · intro he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨ha, hcross⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_image.mpr ⟨a, ha, rfl⟩, by simpa [hl, hr] using hcross⟩

lemma spanningTree_image {n m m' : ℕ} (G : MultiGraph n m) (H : MultiGraph n m')
    (f : Fin m → Fin m') (hl : ∀ e, H.left (f e) = G.left e)
    (hr : ∀ e, H.right (f e) = G.right e) {T : Finset (Fin m)}
    (hT : G.SpanningTree T) : H.SpanningTree (T.image f) := by
  classical
  refine ⟨?_, ?_⟩
  · intro S hS hS'
    rw [cut_image G H f hl hr]
    exact (hT.1 S hS hS').image f
  · intro e he hc
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    apply hT.2 a ha
    intro S hS hS'
    obtain ⟨b, hb⟩ := hc S hS hS'
    obtain ⟨hb, hcross⟩ := mem_filter.mp hb
    obtain ⟨hne, hb⟩ := mem_erase.mp hb
    obtain ⟨c, hc, heq⟩ := mem_image.mp hb
    refine ⟨c, mem_filter.mpr ⟨mem_erase.mpr ⟨?_, hc⟩, ?_⟩⟩
    · intro he
      subst c
      exact hne heq.symm
    · simpa only [← heq, hl, hr] using hcross

lemma cut_image_card_le {n m m' : ℕ} (G : MultiGraph n m) (H : MultiGraph n m')
    (f : Fin m → Fin m') (hl : ∀ e, H.left (f e) = G.left e)
    (hr : ∀ e, H.right (f e) = G.right e) (T : Finset (Fin m))
    (S : Finset (Fin n)) : (H.cut (T.image f) S).card ≤ (G.cut T S).card := by
  rw [cut_image G H f hl hr]
  exact card_image_le

end StrongThinTree.MultiGraph

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

lemma original_copy_exists (x : BinaryInput) (e : x.reduced.Edge) :
    0 < x.multiplicity e.1 := by
  by_contra h
  have hzero : x.multiplicity e.1 = 0 := Nat.eq_zero_of_not_pos h
  have := e.2.isLt
  simp [reduced, hzero] at this

def liftCopy (x : BinaryInput) (e : x.reduced.Edge) : x.Edge :=
  ⟨e.1, ⟨0, x.original_copy_exists e⟩⟩

noncomputable def liftLabel (x : BinaryInput) (e : Fin (Fintype.card x.reduced.Edge)) :
    Fin (Fintype.card x.Edge) :=
  x.edgeEquiv (x.liftCopy (x.reduced.edgeEquiv.symm e))

lemma liftLabel_left (x : BinaryInput) (e : Fin (Fintype.card x.reduced.Edge)) :
    x.graph.left (x.liftLabel e) = x.reduced.graph.left e := by
  simp [graph, liftLabel, liftCopy]

lemma liftLabel_right (x : BinaryInput) (e : Fin (Fintype.card x.reduced.Edge)) :
    x.graph.right (x.liftLabel e) = x.reduced.graph.right e := by
  simp [graph, liftLabel, liftCopy]

lemma lift_thinTree (x : BinaryInput) (hn : 0 < x.n) (hk : 0 < x.k)
    {C : ℝ} (hC : 0 ≤ C) {T : Finset (Fin (Fintype.card x.reduced.Edge))}
    (hT : ThinTree C (x.n ^ 2) x.reduced.graph T) :
    ThinTree (2 * C) x.k x.graph (T.image x.liftLabel) := by
  refine ⟨x.reduced.graph.spanningTree_image x.graph x.liftLabel x.liftLabel_left
    x.liftLabel_right hT.1, ?_⟩
  intro S hS hS'
  have hnR : (0 : ℝ) < x.n := Nat.cast_pos.mpr hn
  have hkR : (0 : ℝ) < x.k := Nat.cast_pos.mpr hk
  have hcoef : 0 ≤ C / (x.n ^ 2 : ℕ) := div_nonneg hC (Nat.cast_nonneg _)
  calc
    ((x.graph.cut (T.image x.liftLabel) S).card : ℝ) ≤
        (x.reduced.graph.cut T S).card := by
      exact_mod_cast x.reduced.graph.cut_image_card_le x.graph x.liftLabel
        x.liftLabel_left x.liftLabel_right T S
    _ ≤ C / (x.n ^ 2 : ℕ) * (x.reduced.graph.cut univ S).card := hT.2 S hS hS'
    _ ≤ C / (x.n ^ 2 : ℕ) *
        ((2 * (x.n : ℝ) ^ 2 / (x.k : ℝ)) * (x.graph.cut univ S).card) :=
      mul_le_mul_of_nonneg_left (x.reduced_cut_upper hk S) hcoef
    _ = 2 * C / (x.k : ℝ) * (x.graph.cut univ S).card := by
      push_cast
      field_simp

theorem reduction_correct (x : BinaryInput) (hn : 2 ≤ x.n) (hk : 1 ≤ x.k)
    (hc : x.graph.EdgeConnected x.k) :
    x.reduced.graph.EdgeConnected (x.n ^ 2) ∧
    Fintype.card x.reduced.Edge < x.n ^ 4 ∧
    (∀ S : Finset (Fin x.n), ((x.reduced.graph.cut univ S).card : ℝ) ≤
      2 * (x.n : ℝ) ^ 2 / (x.k : ℝ) * (x.graph.cut univ S).card) ∧
    (∀ C : ℝ, 0 ≤ C → ∀ T : Finset (Fin (Fintype.card x.reduced.Edge)),
      ThinTree C (x.n ^ 2) x.reduced.graph T →
      ThinTree (2 * C) x.k x.graph (T.image x.liftLabel)) := by
  have hn' : 0 < x.n := by omega
  exact ⟨x.reduced_edgeConnected hn' hk hc, x.reduced_size hn' hk,
    x.reduced_cut_upper hk, fun _ hC _ hT => x.lift_thinTree hn' hk hC hT⟩

end AlgorithmicThinTrees.BinaryInput

namespace AlgorithmicThinTrees
open StrongThinTree Finset

lemma framed_nat_length_pos (v : ℕ) : 0 < (CurrentKS.encodeNat v).length := by
  unfold CurrentKS.encodeNat
  cases Computability.encodeNat v <;> simp [CurrentKS.frame]

lemma record_count_le_bits (records : List (List Bool))
    (h : ∀ bits ∈ records, 0 < bits.length) : records.length ≤ records.flatten.length := by
  induction records with
  | nil => simp
  | cons bits records ih =>
    have hb := h bits (List.mem_cons_self ..)
    have hr := ih (fun bs hbs => h bs (List.mem_cons_of_mem _ hbs))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

namespace BinaryInput

lemma vertices_le_twice_records (x : BinaryInput) (hn : 2 ≤ x.n) (hk : 0 < x.k)
    (hc : x.graph.EdgeConnected x.k) : x.n ≤ 2 * x.p := by
  classical
  let L : Finset (Fin x.n) := univ.image x.left
  let R : Finset (Fin x.n) := univ.image x.right
  have hcover : univ ⊆ L ∪ R := by
    intro v _
    have hproper : ({v} : Finset (Fin x.n)) ≠ univ := by
      intro he
      have hcard := congrArg Finset.card he
      simp only [card_singleton, card_univ, Fintype.card_fin] at hcard
      omega
    have hcut := hc {v} (singleton_nonempty v) hproper
    obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le hk hcut)
    have hcross := (mem_filter.mp he).2
    change (x.left (x.edgeEquiv.symm e).1 ∈ {v} ∧
        x.right (x.edgeEquiv.symm e).1 ∉ {v}) ∨
      (x.right (x.edgeEquiv.symm e).1 ∈ {v} ∧
        x.left (x.edgeEquiv.symm e).1 ∉ {v}) at hcross
    rcases hcross with h | h
    · exact mem_union_left R (mem_image.mpr
        ⟨(x.edgeEquiv.symm e).1, mem_univ _, mem_singleton.mp h.1⟩)
    · exact mem_union_right L (mem_image.mpr
        ⟨(x.edgeEquiv.symm e).1, mem_univ _, mem_singleton.mp h.1⟩)
  have hL : L.card ≤ x.p := by simpa [L] using card_image_le (f := x.left) (s := univ)
  have hR : R.card ≤ x.p := by simpa [R] using card_image_le (f := x.right) (s := univ)
  have hcard := (card_le_card hcover).trans (card_union_le L R)
  simp only [card_univ, Fintype.card_fin] at hcard
  omega

lemma records_le_encoding (x : BinaryInput) : x.p ≤ x.encode.length := by
  let records := List.ofFn (fun i : Fin x.p =>
    CurrentKS.encodeNat (x.left i).val ++ CurrentKS.encodeNat (x.right i).val ++
      CurrentKS.encodeNat (x.multiplicity i))
  have h := record_count_le_bits records (by
    intro bits hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    have h := framed_nat_length_pos (x.left i).val
    simp only [List.length_append]
    omega)
  simp only [records, List.length_ofFn] at h
  unfold encode
  simp only [List.length_append]
  omega

lemma vertices_le_binary_length (x : BinaryInput) (hn : 2 ≤ x.n) (hk : 0 < x.k)
    (hc : x.graph.EdgeConnected x.k) : x.n ≤ 2 * (Input.binary x).length := by
  have hv := x.vertices_le_twice_records hn hk hc
  have hr := x.records_le_encoding
  simp only [Input.length, Input.encode, List.length_cons]
  omega

theorem reduced_size_binary_bound (x : BinaryInput) (hn : 2 ≤ x.n) (hk : 1 ≤ x.k)
    (hc : x.graph.EdgeConnected x.k) :
    Fintype.card x.reduced.Edge < 16 * (Input.binary x).length ^ 4 := by
  have hsize := x.reduced_size (by omega) hk
  have hn' := x.vertices_le_binary_length hn hk hc
  calc
    Fintype.card x.reduced.Edge < x.n ^ 4 := hsize
    _ ≤ (2 * (Input.binary x).length) ^ 4 := Nat.pow_le_pow_left hn' 4
    _ = 16 * (Input.binary x).length ^ 4 := by norm_num [mul_pow]

end BinaryInput
end AlgorithmicThinTrees
end

end OAI
