import Mathlib
import OAI.Combinatorics.UniformKServer.RawPartition

namespace OAI

namespace UniformKServer.EpochPartition
open RawPartition EpochShadow

def chunks {α : Type} (R : ℕ) (hR : 0 < R) : List α → List (List α)
  | [] => []
  | b::bs => (b::bs).take R :: chunks R hR ((b::bs).drop R)
termination_by bs => bs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

def epochs {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) : List (List (Fin n)) :=
  (chunks R hR (pack k [] w)).map List.flatten

theorem chunks_flatten {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    (chunks R hR bs).flatten = bs := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks, List.flatten_cons, ih, List.take_append_drop]

theorem chunks_nil {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    chunks R hR bs = [] ↔ bs = [] := by
  cases bs <;> simp [chunks]

theorem sublist_dropLast {α : Type} {bs cs : List α} (h : bs.Sublist cs) :
    bs.dropLast.Sublist cs.dropLast := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a h ih =>
    cases l₂ with
    | nil => simpa using ih
    | cons c cs =>
      simpa only [List.dropLast_cons_cons] using List.Sublist.cons a ih
  | @cons_cons l₁ l₂ a h ih =>
    cases l₁ with
    | nil => simp
    | cons b bs =>
      cases l₂ with
      | nil => have hh := h.length_le; simp at hh
      | cons c cs => simpa only [List.dropLast_cons_cons] using List.Sublist.cons_cons a ih

theorem chunks_sublist {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    ∀ c ∈ chunks R hR bs, c.Sublist bs ∧ c.length ≤ R := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨List.take_sublist _ _, by simp [List.length_take]⟩
    · obtain ⟨hs,hl⟩ := ih c hc
      exact ⟨hs.trans (List.drop_sublist _ _),hl⟩

theorem chunks_number {α : Type} (R : ℕ) (hR : 0 < R) (bs : List α) :
    ((chunks R hR bs).length - 1)*R ≤ bs.length - 1 := by
  induction bs using chunks.induct R hR with
  | case1 => simp [chunks]
  | case2 b bs ih =>
    rw [chunks]
    simp only [List.length_cons, Nat.add_sub_cancel]
    by_cases he : (b::bs).drop R = []
    · rw [he, chunks]
      simp
    · have hd : 0 < ((b::bs).drop R).length := List.length_pos_iff.mpr he
      have hn : 0 < (chunks R hR ((b::bs).drop R)).length :=
        List.length_pos_iff.mpr (mt (chunks_nil R hR _).mp he)
      have hmul : (chunks R hR ((b::bs).drop R)).length * R =
          ((chunks R hR ((b::bs).drop R)).length - 1)*R + R := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        simp [Nat.add_mul]
      rw [hmul]
      have hlen : R + ((b::bs).drop R).length = (b::bs).length := by
        simp only [List.length_drop] at *
        omega
      simp only [List.length_cons] at hlen
      omega

theorem epochs_flatten {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) :
    (epochs k R hR w).flatten = w := by
  unfold epochs
  rw [← List.flatten_flatten, chunks_flatten, flatten_pack]
  rfl

theorem epoch_blocks {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) :
    ∀ e ∈ epochs k R hR w, blockCount (k:=k) ∅ e ≤ R := by
  intro e he
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp he
  obtain ⟨hs,hl⟩ := chunks_sublist R hR (pack k [] w) bs hbs
  apply (block_count_bound bs ?_ ?_).trans hl
  · intro b hb
    exact pack_good k [] w (by simp) b (hs.subset hb)
  · intro b hb
    exact pack_complete k [] w b ((sublist_dropLast hs).subset hb)

theorem epoch_charge {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (R : ℕ) (hR : 0 < R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (pre w : List (Fin n)) (s : Configuration n k) :
    (((epochs k R hR w).length - 1 : ℕ) : ℝ)*R*δ ≤ offlineCost d s (pre++w) := by
  have hn := chunks_number R hR (pack k [] w)
  have hn' : (((chunks R hR (pack k [] w)).length - 1 : ℕ) : ℝ)*R ≤
      (((pack k [] w).length - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right hn' hδ
  have hc := completed_charge hk d δ hδ hsep pre w s
  simpa only [epochs, List.length_map] using hp.trans hc

end UniformKServer.EpochPartition




end OAI
