import Mathlib
import OAI.Combinatorics.UniformKServer.EpochShadow
import OAI.Combinatorics.UniformKServer.RawBlockCharge

namespace OAI

namespace UniformKServer.RawPartition
open EpochShadow

def pack {n : ℕ} (k : ℕ) : List (Fin n) → List (Fin n) → List (List (Fin n))
  | acc, [] => if acc = [] then [] else [acc]
  | acc, r::w => if k < (acc++[r]).toFinset.card then
      (acc++[r]) :: pack k [] w else pack k (acc++[r]) w

def GoodBlock {n : ℕ} (k : ℕ) (b : List (Fin n)) : Prop :=
  ∃ p r, b = p++[r] ∧ p.toFinset.card ≤ k

theorem flatten_pack {n : ℕ} (k : ℕ) (acc w : List (Fin n)) :
    (pack k acc w).flatten = acc++w := by
  induction w generalizing acc with
  | nil => by_cases h : acc = []; simp [pack,h]; simp [pack,h]
  | cons r w ih =>
    simp only [pack]
    split
    · simp only [List.flatten_cons, ih, List.nil_append, List.append_assoc,
        List.singleton_append]
    · simpa only [List.append_assoc, List.singleton_append] using ih (acc++[r])

theorem pack_good {n : ℕ} (k : ℕ) (acc w : List (Fin n))
    (ha : acc.toFinset.card ≤ k) : ∀ b ∈ pack k acc w, GoodBlock k b := by
  induction w generalizing acc with
  | nil =>
    simp only [pack]
    split
    · simp
    · intro b hb
      have he : b = acc := by simpa using hb
      subst b
      have hne : acc ≠ [] := by assumption
      refine ⟨acc.dropLast,acc.getLast hne,(List.dropLast_append_getLast hne).symm,?_⟩
      apply (Finset.card_le_card ?_).trans ha
      intro x hx
      exact List.mem_toFinset.mpr ((List.dropLast_sublist acc).subset (List.mem_toFinset.mp hx))
  | cons r w ih =>
    simp only [pack]
    split
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨acc,r,rfl,ha⟩
      · exact ih [] (by simp) b hb
    · exact ih (acc++[r]) (by omega)

theorem pack_complete {n : ℕ} (k : ℕ) (acc w : List (Fin n)) :
    ∀ b ∈ (pack k acc w).dropLast, k < b.toFinset.card := by
  induction w generalizing acc with
  | nil => by_cases h : acc = []; simp [pack,h]; simp [pack,h]
  | cons r w ih =>
    simp only [pack]
    split
    · rename_i hc
      cases he : pack k [] w with
      | nil => simp
      | cons b bs =>
        simp only [List.dropLast_cons_cons]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hc
        · apply ih [] a
          simpa only [he] using ha
    · exact ih (acc++[r])

theorem no_endpoint_prefix {n k : ℕ} (seen : Finset (Fin n)) (p q : List (Fin n))
    (hp : (seen ∪ p.toFinset).card ≤ k) :
    blockCount (k:=k) seen (p++q) = blockCount (k:=k) (seen ∪ p.toFinset) q := by
  induction p generalizing seen with
  | nil => simp
  | cons r p ih =>
    have hsub : insert r seen ⊆ seen ∪ (r::p).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, List.toFinset_cons] at *
      aesop
    have hr : (insert r seen).card ≤ k := (Finset.card_le_card hsub).trans hp
    have he : insert r seen ∪ p.toFinset = seen ∪ (r::p).toFinset := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto
    simp only [List.cons_append, blockCount, ite_eq_right (by omega : ¬ k < (insert r seen).card),
      Nat.zero_add, bookStep]
    rw [ih (insert r seen) (by rwa [he]), he]

theorem good_count {n k : ℕ} {b : List (Fin n)} (hb : GoodBlock k b) :
    blockCount (k:=k) ∅ b ≤ 1 := by
  obtain ⟨p,r,rfl,hp⟩ := hb
  rw [no_endpoint_prefix ∅ p [r] (by simpa using hp)]
  simp only [Finset.empty_union, blockCount, bookStep]
  split
  · simp
  · split <;> simp_all

theorem complete_append {n k : ℕ} {b : List (Fin n)} (hb : GoodBlock k b)
    (hc : k < b.toFinset.card) (w : List (Fin n)) :
    blockCount (k:=k) ∅ (b++w) = 1 + blockCount (k:=k) ∅ w := by
  obtain ⟨p,r,rfl,hp⟩ := hb
  rw [List.append_assoc, no_endpoint_prefix ∅ p ([r]++w) (by simpa using hp)]
  have hr : k < (insert r p.toFinset).card := by simpa using hc
  simp [blockCount, bookStep, hr]

theorem block_count_bound {n k : ℕ} (bs : List (List (Fin n)))
    (hg : ∀ b ∈ bs, GoodBlock k b)
    (hc : ∀ b ∈ bs.dropLast, k < b.toFinset.card) :
    blockCount (k:=k) ∅ bs.flatten ≤ bs.length := by
  induction bs with
  | nil => simp [blockCount]
  | cons b bs ih =>
    cases bs with
    | nil => simpa using good_count (hg b (by simp))
    | cons c cs =>
      have hb : k < b.toFinset.card := hc b (by simp)
      have ht := ih (fun a ha => hg a (by simp_all)) (by
        intro a ha
        exact hc a (by simp_all))
      simpa only [List.flatten_cons, complete_append (hg b (by simp)) hb,
        List.length_cons, Nat.add_comm] using Nat.add_le_add_left ht 1

theorem completed_charge {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (pre w : List (Fin n)) (s : Configuration n k) :
    (((pack k [] w).length - 1 : ℕ) : ℝ)*δ ≤ offlineCost d s (pre++w) := by
  let bs := pack k [] w
  by_cases hnil : bs = []
  · have hw : w = [] := by
      have hh := flatten_pack k [] w
      change bs.flatten = []++w at hh
      simpa [hnil] using hh.symm
    subst w
    simp only [pack, ↓reduceIte, List.length_nil, Nat.zero_sub, Nat.cast_zero, zero_mul]
    rw [List.append_nil]
    apply le_csInf
    · refine ⟨costAlong d s (pre.map (fun r => (r,⟨0,hk⟩))),_,?_,rfl⟩
      simp only [List.map_map]
      exact List.map_id _
    · rintro c ⟨h,_,rfl⟩
      exact UniformKServer.costAlong_nonneg d s h
  · have hsplit : bs.dropLast ++ [bs.getLast hnil] = bs := List.dropLast_append_getLast hnil
    have hf : bs.dropLast.flatten ++ bs.getLast hnil = w := by
      have hh := congrArg List.flatten hsplit
      simpa [bs, flatten_pack] using hh
    have hc := RawBlockCharge.offline_blocks hk d δ hδ hsep bs.dropLast
      (pack_complete k [] w) pre (bs.getLast hnil) s
    rw [List.append_assoc, hf] at hc
    simpa only [List.length_dropLast] using hc

end UniformKServer.RawPartition


end OAI
