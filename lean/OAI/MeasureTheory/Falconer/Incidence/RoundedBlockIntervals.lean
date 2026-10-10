import OAI.MeasureTheory.Falconer.Recursion.OrderedEndpointIntervals
import OAI.MeasureTheory.Falconer.Incidence.BlockGrid

namespace OAI

/-! Real profile intervals select an ordered family of actual block intervals.
The selected endpoints and their normalized lengths remain exact. -/
namespace Falconer
open Regularization

theorem OrderedBlockIntervals.of_pairwise {i j : ℕ} {R : List (ℕ × ℕ)}
    (hji : j ≤ i) (hp : R.Pairwise (fun c d => d.1 ≤ c.2))
    (hb : ∀ c ∈ R, j ≤ c.2 ∧ c.2 ≤ c.1 ∧ c.1 ≤ i) :
    OrderedBlockIntervals i j R := by
  induction R generalizing i with
  | nil => exact hji
  | cons c R ih =>
    have hh := hb c (by simp)
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hp
    refine ⟨hh.2.2,hh.2.1,ih hh.1 htail ?_⟩
    intro d hd
    have hd' := hb d (by simp [hd])
    exact ⟨hd'.1,hd'.2.1,hhead d hd⟩

theorem normalized_blockDepth_le_imp {m B i j : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hi : i ≤ m) (hj : j ≤ m)
    (h : (blockDepth (m*B) B i:ℝ)/(m*B:ℕ) ≤ (blockDepth (m*B) B j:ℝ)/(m*B:ℕ)) :
    j ≤ i := by
  have hN : (0:ℝ) < (m*B:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hm hB)
  have hh := (div_le_div_iff_of_pos_right hN).mp h
  have hiB : i*B ≤ m*B := Nat.mul_le_mul_right B hi
  have hjB : j*B ≤ m*B := Nat.mul_le_mul_right B hj
  simp only [blockDepth,Nat.cast_sub hiB,Nat.cast_sub hjB,Nat.cast_mul] at hh
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB
  have hji : (j:ℝ) ≤ i := by nlinarith only [hh,hB']
  exact_mod_cast hji

theorem exists_rounded_block_interval_map {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (S : List (ℝ × ℝ))
    (hbound : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ 1)
    (hpos : ∀ c ∈ S, 0 < (innerProfileCell m c).2)
    (hordered : (S.map (innerProfileCell m)).Pairwise (fun c d => c.1+c.2 ≤ d.1)) :
    ∃ I : (ℝ × ℝ) → (ℕ × ℕ),
      (∀ c ∈ S, (I c).2 < (I c).1 ∧ (I c).1 ≤ m ∧
        (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
        (innerProfileCell m c).1+(innerProfileCell m c).2 =
          (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ)) ∧
      (S.map I).Pairwise (fun c d => d.1 ≤ c.2) ∧ OrderedBlockIntervals m 0 (S.map I) := by
  classical
  have hex (c : ℝ × ℝ) (hc : c ∈ S) : ∃ r : ℕ × ℕ,
      r.2 < r.1 ∧ r.1 ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B r.1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B r.2:ℝ)/(m*B:ℕ) := by
    obtain ⟨i,j,hji,hi,ha,hb⟩ := innerProfileCell_block_endpoints hm hB c
      (hbound c hc).1 (hbound c hc).2 (hpos c hc)
    exact ⟨(i,j),hji,hi,ha,hb⟩
  let I := fun c => if hc : c ∈ S then Classical.choose (hex c hc) else (0,0)
  have hI (c : ℝ × ℝ) (hc : c ∈ S) :
      (I c).2 < (I c).1 ∧ (I c).1 ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ) := by
    simpa only [I,dite_eq_left hc] using Classical.choose_spec (hex c hc)
  have hp : (S.map I).Pairwise (fun c d => d.1 ≤ c.2) := by
    apply List.pairwise_map.mpr
    apply (List.pairwise_map.mp hordered).imp_of_mem
    intro c d hc hd hcd
    have hc' := hI c hc
    have hd' := hI d hd
    rw [hc'.2.2.2,hd'.2.2.1] at hcd
    exact normalized_blockDepth_le_imp hm hB (hc'.1.le.trans hc'.2.1) hd'.2.1 hcd
  refine ⟨I,hI,hp,OrderedBlockIntervals.of_pairwise (Nat.zero_le _) hp ?_⟩
  intro r hr
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
  exact ⟨Nat.zero_le _,(hI c hc).1.le,(hI c hc).2.1⟩

end Falconer

end OAI
