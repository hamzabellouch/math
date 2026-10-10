import Mathlib
import OAI.Combinatorics.UniformKServer.PrefixTree

namespace OAI

                                     
section

/-! Height-free deterministic conversion of coordinate-key disagreements into
weighted subtree-count variation on the literal full prefix universe. -/
noncomputable section
namespace UniformKServer.PrefixMovement
open Finset TreeRounding TreeAncestry TreeLeaves PrefixTree
open scoped Classical
variable {A : Type*} [Fintype A] {J : ℕ}

def diff {T : Type*} (a b : T) : ℝ := if a=b then 0 else 1

theorem diff_nonneg {T : Type*} (a b : T) : 0 ≤ diff a b := by
  unfold diff; split_ifs <;> norm_num

theorem prefix_ext (p q : Fin J → A) (d : ℕ) (hd : d ≤ J)
    (h : ∀ i : Fin J, i.val < d → p i=q i) : atLevel p d hd=atLevel q d hd := by
  apply (chart A J).injective
  simp only [atLevel,Equiv.apply_symm_apply,wordPrefix]
  congr 1
  funext i
  exact h _ i.isLt

theorem prefix_disagreement (p q : Fin J → A) (d : ℕ) (hd : d ≤ J) :
    diff (atLevel p d hd) (atLevel q d hd) ≤ ∑ i : Fin J, if i.val < d then diff (p i) (q i) else 0 := by
  by_cases he : atLevel p d hd=atLevel q d hd
  · rw [diff,ite_eq_left he]
    exact sum_nonneg fun i _ => by split_ifs; exact diff_nonneg _ _; exact le_rfl
  · have hn : ∃ i : Fin J, i.val < d ∧ p i ≠ q i := by
      by_contra hh
      push Not at hh
      exact he (prefix_ext p q d hd hh)
    obtain ⟨i,hi,hn⟩ := hn
    rw [diff,ite_eq_right he]
    calc
      _ = (if i.val < d then diff (p i) (q i) else 0) := by rw [ite_eq_left hi,diff,ite_eq_right hn]
      _ ≤ _ := single_le_sum (f:=fun j : Fin J => if j.val < d then diff (p j) (q j) else 0)
        (fun j _ => by split_ifs; exact diff_nonneg _ _; exact le_rfl) (mem_univ i)

def mark (v : Vertex (size A J)) (p : Fin J → A) : ℝ :=
  if descends (shape A J) v (endpoint p) then 1 else 0

theorem mark_nonneg (v : Vertex (size A J)) (p : Fin J → A) : 0 ≤ mark v p := by
  unfold mark; split_ifs <;> norm_num

theorem mark_iff (v : Vertex (size A J)) (p : Fin J → A) :
    descends (shape A J) v (endpoint p) ↔ v=atLevel p (depth (shape A J) v) (depth_bound v) := by
  constructor
  · exact desc_endpoint p v
  · intro h
    conv_lhs => rw [h]
    exact at_descends p _ J le_rfl (depth_bound v)

theorem level_mark (p : Fin J → A) (d : Fin (J+1)) :
    (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p else 0)=1 := by
  rw [sum_eq_single (atLevel p d.val (by omega))]
  · rw [depth_at,ite_eq_left rfl,mark]
    exact ite_eq_left (at_descends p d.val J le_rfl (by omega))
  · intro v _ hv
    by_cases hd : depth (shape A J) v=d.val
    · rw [ite_eq_left hd,mark,ite_eq_right]
      intro hh
      apply hv
      have he := desc_endpoint p v hh
      simpa only [hd] using he
    · exact ite_eq_right hd
  · simp

theorem level_variation (p q : Fin J → A) (d : Fin (J+1)) :
    (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then |mark v p-mark v q| else 0) ≤
      2*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega)) := by
  by_cases he : atLevel p d.val (by omega)=atLevel q d.val (by omega)
  · rw [diff,ite_eq_left he,mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro v _
    by_cases hd : depth (shape A J) v=d.val
    · have hp : mark v p=mark v q := by
        unfold mark
        rw [mark_iff,mark_iff]
        simp only [hd,he]
      rw [ite_eq_left hd,hp,sub_self,abs_zero]
    · exact ite_eq_right hd
  · rw [diff,ite_eq_right he,mul_one]
    calc
      _ ≤ ∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p+mark v q else 0 := by
        apply sum_le_sum
        intro v _
        split_ifs
        · exact abs_sub_le_iff.mpr ⟨by linarith [mark_nonneg v q],by linarith [mark_nonneg v p]⟩
        · exact le_rfl
      _ = (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v p else 0)+
          (∑ v : Vertex (size A J), if depth (shape A J) v=d.val then mark v q else 0) := by
        rw [←sum_add_distrib]
        apply sum_congr rfl
        intro v _
        split_ifs <;> ring
      _ = _ := by rw [level_mark,level_mark]; norm_num

theorem depth_sum (f : Vertex (size A J) → ℝ) :
    (∑ v, f v)=∑ d : Fin (J+1), ∑ v, if depth (shape A J) v=d.val then f v else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  symm
  rw [sum_eq_single (⟨depth (shape A J) v,by have := depth_bound v; omega⟩ : Fin (J+1))]
  · exact ite_eq_left rfl
  · intro d _ hd
    exact ite_eq_right (fun he => hd (Fin.ext he.symm))
  · simp

theorem path_variation (p q : Fin J → A) (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (∑ v : Vertex (size A J), w (depth (shape A J) v)*|mark v p-mark v q|) ≤
      2*∑ d : Fin (J+1), w d.val*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega)) := by
  rw [depth_sum]
  calc
    _ = ∑ d : Fin (J+1), w d.val * ∑ v : Vertex (size A J),
        if depth (shape A J) v=d.val then |mark v p-mark v q| else 0 := by
      apply sum_congr rfl
      intro d _
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      split_ifs with hd
      · rw [hd]
      · rw [mul_zero]
    _ ≤ ∑ d : Fin (J+1), w d.val*(2*diff (atLevel p d.val (by omega)) (atLevel q d.val (by omega))) :=
      sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (level_variation p q d) (hw d.val)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring

theorem tail_bound (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i)
    (m N : ℕ) : (∑ i ∈ range N, r (m+i)) ≤ 2*r m := by
  induction N generalizing m with
  | zero => simp only [sum_range_zero]; exact mul_nonneg (by norm_num) (hr m)
  | succ N ih =>
    rw [sum_range_succ']
    have hh := ih (m+1)
    have he : (∑ x ∈ range N, r (m+(x+1)))=∑ x ∈ range N, r (m+1+x) := by
      apply sum_congr rfl
      intro x _
      congr 1; omega
    rw [he]
    simp only [Nat.add_zero]
    linarith [hdec m]

theorem tail_depths (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i)
    (i N : ℕ) : (∑ d ∈ range N, if i<d then r (d-1) else 0) ≤ 2*r i := by
  by_cases hi : N ≤ i+1
  · have hz : (∑ d ∈ range N, if i<d then r (d-1) else 0)=0 := by
      apply sum_eq_zero
      intro d hd
      exact ite_eq_right (by have := mem_range.mp hd; omega)
    rw [hz]
    exact mul_nonneg (by norm_num) (hr i)
  · have hN : N=(i+1)+(N-(i+1)) := by omega
    rw [hN,sum_range_add]
    have hz : (∑ d ∈ range (i+1), if i<d then r (d-1) else 0)=0 := by
      apply sum_eq_zero
      intro d hd
      exact ite_eq_right (by have := mem_range.mp hd; omega)
    rw [hz,zero_add]
    have he : (∑ d ∈ range (N-(i+1)), if i < i+1+d then r (i+1+d-1) else 0)=
        ∑ d ∈ range (N-(i+1)), r (i+d) := by
      apply sum_congr rfl
      intro d _
      rw [ite_eq_left (by omega)]
      congr 1; omega
    rw [he]
    exact tail_bound r hr hdec i _

def edgeWeight (r : ℕ → ℝ) (d : ℕ) : ℝ := if d=0 then 0 else r (d-1)

theorem spatial_variation (p q : Fin J → A) (r : ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i) :
    (∑ v : Vertex (size A J), edgeWeight r (depth (shape A J) v)*|mark v p-mark v q|) ≤
      4*∑ i : Fin J, r i.val*diff (p i) (q i) := by
  have hw (d : ℕ) : 0 ≤ edgeWeight r d := by unfold edgeWeight; split_ifs; exact le_rfl; exact hr _
  have hp := path_variation p q (edgeWeight r) hw
  have hs := sum_le_sum (s:=univ) (fun d (_ : d ∈ (univ : Finset (Fin (J+1)))) =>
    mul_le_mul_of_nonneg_left (prefix_disagreement p q d.val (by omega)) (hw d.val))
  have he : (∑ d : Fin (J+1), edgeWeight r d.val * ∑ i : Fin J, if i.val<d.val then diff (p i) (q i) else 0)=
      ∑ i : Fin J, (∑ d : Fin (J+1), if i.val<d.val then r (d.val-1) else 0)*diff (p i) (q i) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro d _
    by_cases hd : i.val<d.val
    · rw [ite_eq_left hd,ite_eq_left hd,edgeWeight,ite_eq_right (by omega)]
    · rw [ite_eq_right hd,ite_eq_right hd,mul_zero,zero_mul]
  rw [he] at hs
  have ht (i : Fin J) : (∑ d : Fin (J+1), if i.val<d.val then r (d.val-1) else 0) ≤ 2*r i.val := by
    simpa only [←Fin.sum_univ_eq_sum_range] using tail_depths r hr hdec i.val (J+1)
  have hb := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_right (ht i) (diff_nonneg (p i) (q i)))
  simp only [mul_assoc,←mul_sum] at hb
  linarith

end UniformKServer.PrefixMovement

end


end

end OAI
