import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace.NatGrid

def dist₁ (x y : Vertex) : ℝ := |(x.1:ℝ)-y.1|+|(x.2:ℝ)-y.2|

def ball (N : ℕ) (x : Vertex) (r : ℝ) : Finset Vertex :=
  (square N).filter (fun y => dist₁ x y ≤ r)

def localKernel (N : ℕ) (ν : Vertex → ℝ) (s : ℕ) (e : Edge) : ℝ :=
  (4/(s:ℝ)) * ∑ x ∈ square N,
    if e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1)) then ν x else 0

lemma local_mem_dist {N r : ℕ} {x : Vertex} {e : Edge}
    (he : e ∈ edges (lo x r) (hi N x r)) : dist₁ (anchor e) x ≤ 2*r := by
  have h := mem_box_iff.mp (anchor_mem_rect he)
  have h1 : |((anchor e).1:ℝ)-x.1| ≤ r := by
    rw [abs_le]
    constructor <;> linarith [show ((anchor e).1:ℝ) ≤ x.1+r by exact_mod_cast h.2.2.1,
      show (x.1:ℝ) ≤ (anchor e).1+r by exact_mod_cast h.2.2.2.1]
  have h2 : |((anchor e).2:ℝ)-x.2| ≤ r := by
    rw [abs_le]
    constructor <;> linarith [show ((anchor e).2:ℝ) ≤ x.2+r by exact_mod_cast h.2.2.2.2.1,
      show (x.2:ℝ) ≤ (anchor e).2+r by exact_mod_cast h.2.2.2.2.2]
  exact (add_le_add h1 h2).trans_eq (by ring)

lemma square_dist {N : ℕ} {x y : Vertex} (hx : x ∈ square N) (hy : y ∈ square N) :
    dist₁ x y ≤ 2*N := by
  have hx := square_mem.mp hx
  have hy := square_mem.mp hy
  have h1 : |(x.1:ℝ)-y.1| ≤ N := by
    rw [abs_le]
    have hx : (x.1:ℝ) ≤ N := by exact_mod_cast hx.1
    have hy : (y.1:ℝ) ≤ N := by exact_mod_cast hy.1
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) x.1,Nat.cast_nonneg (α := ℝ) y.1]
  have h2 : |(x.2:ℝ)-y.2| ≤ N := by
    rw [abs_le]
    have hx : (x.2:ℝ) ≤ N := by exact_mod_cast hx.2
    have hy : (y.2:ℝ) ≤ N := by exact_mod_cast hy.2
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) x.2,Nat.cast_nonneg (α := ℝ) y.2]
  exact (add_le_add h1 h2).trans_eq (by ring)

lemma localKernel_nonneg {N s : ℕ} {ν : Vertex → ℝ}
    (hν : ∀ x ∈ square N, 0 ≤ ν x) (e : Edge) : 0 ≤ localKernel N ν s e := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun x hx => by split_ifs <;> simp [hν x hx])

lemma localKernel_sup {N s : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s) {ν : Vertex → ℝ} {α C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hν : ∀ x ∈ square N, 0 ≤ ν x)
    (hspread : ∀ x ∈ square N, ∀ r : ℝ, 0 ≤ r → r ≤ 2*(N:ℝ) →
      (∑ y ∈ ball N x r, ν y) ≤ C*((r+1)/(N:ℝ))^α)
    {e : Edge} (he : e ∈ edges (0,0) (N,N)) :
    localKernel N ν s e ≤ (4/(s:ℝ))*C*((5*s)/(N:ℝ))^α := by
  have hanc : anchor e ∈ square N := anchor_mem_rect he
  have hnp : (0:ℝ) < N := by exact_mod_cast hN
  have hn : (0:ℝ) ≤ N := hnp.le
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  let R : ℝ := min (4*s) (2*N)
  have hr : 0 ≤ R := le_min (by positivity) (by positivity)
  have hrN : R ≤ 2*N := min_le_right _ _
  have hsum : (∑ x ∈ square N, if e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1)) then ν x else 0) ≤
      ∑ x ∈ ball N (anchor e) R, ν x := by
    rw [ball,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hm : e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1))
    · have hd := local_mem_dist hm
      have dd : (2*(2*s-1):ℕ) ≤ 4*s := by omega
      have hd4 : dist₁ (anchor e) x ≤ 4*s := hd.trans (by exact_mod_cast dd)
      have hdR : dist₁ (anchor e) x ≤ R := le_min hd4 (square_dist hanc hx)
      simp [hm,hdR]
    · simp only [ite_eq_right hm]
      split_ifs <;> simp [hν x hx]
  calc
    _ ≤ (4/(s:ℝ))*(∑ x ∈ ball N (anchor e) R, ν x) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (4/(s:ℝ))*(C*((R+1)/(N:ℝ))^α) :=
      mul_le_mul_of_nonneg_left (hspread (anchor e) hanc R hr hrN) (by positivity)
    _ ≤ (4/(s:ℝ))*C*((5*s)/(N:ℝ))^α := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow (by positivity) _ hα
      exact div_le_div_of_nonneg_right (by have := min_le_left (4*(s:ℝ)) (2*N);dsimp [R];linarith) hn

lemma localKernel_sum {N s : ℕ} (hs : 1 ≤ s) {ν : Vertex → ℝ} {C : ℝ}
    (hν : ∀ x ∈ square N, 0 ≤ ν x) (hmass : (∑ x ∈ square N, ν x) ≤ C) :
    (∑ e ∈ edges (0,0) (N,N), localKernel N ν s e) ≤ 128*C*s := by
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hcards (x : Vertex) : ((edges (lo x (2*s-1)) (hi N x (2*s-1))).card:ℝ) ≤ 32*(s:ℝ)^2 := by
    have h := edges_card_bound N x (2*s-1)
    have ha : 2*(2*s-1)+1 ≤ 4*s := by omega
    have hb : 2*(2*(2*s-1)+1)^2 ≤ 32*s^2 := by nlinarith [Nat.pow_le_pow_left ha 2]
    exact_mod_cast h.trans hb
  have hid (x : Vertex) : (∑ e ∈ edges (0,0) (N,N),
      if e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1)) then ν x else 0) =
      (edges (lo x (2*s-1)) (hi N x (2*s-1))).card*ν x := by
    rw [← Finset.sum_filter]
    have hf : (edges (0,0) (N,N)).filter
        (fun e => e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1))) =
        edges (lo x (2*s-1)) (hi N x (2*s-1)) := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨box_edges_subset N x _ h,h⟩⟩
    rw [hf,Finset.sum_const,nsmul_eq_mul]
  simp only [localKernel,← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hid]
  calc
    _ ≤ (4/(s:ℝ))*∑ x ∈ square N, (32*(s:ℝ)^2)*ν x :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hcards x) (hν x hx))) (by positivity)
    _ = (4/(s:ℝ))*(32*(s:ℝ)^2)*(∑ x ∈ square N, ν x) := by
      rw [← Finset.mul_sum, ← mul_assoc]
    _ ≤ (4/(s:ℝ))*(32*(s:ℝ)^2)*C := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by field_simp;ring

end GridTrace.NatGrid

end

end OAI
