import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

theorem near_probability_bound {ι α : Type*} [Fintype α]
    (S : Finset ι) (ancestor : ι → α) (P : ι → ℝ) (W : α → ℝ)
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (hW : ∀ a, 0 ≤ W a)
    (hcount : ∀ a, (S.filter (fun i => ancestor i = a)).card ≤ N)
    (hweight : ∀ i ∈ S, P i ≤ c*W (ancestor i)) :
    ∑ i ∈ S, P i ≤ (N:ℝ)*c*∑ a, W a := by
  classical
  have heq : ∑ i ∈ S, c*W (ancestor i) =
      ∑ a, ((S.filter (fun i => ancestor i = a)).card : ℝ)*(c*W a) := by
    calc
      _ = ∑ i ∈ S, ∑ a : α, if ancestor i = a then c*W a else 0 := by
        apply sum_congr rfl
        intro i hi
        simp
      _ = ∑ a, ∑ i ∈ S.filter (fun i => ancestor i = a), c*W a := by
        rw [sum_comm]
        simp only [sum_filter]
      _ = _ := by simp only [sum_const,nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ S, c*W (ancestor i) := sum_le_sum hweight
    _ = _ := heq
    _ ≤ ∑ a, (N:ℝ)*(c*W a) := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount a) (mul_nonneg hc (hW a))
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro a _; ring

lemma card_filter_product {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (rel : ι → κ → Prop) :
    ((S ×ˢ T).filter (fun p => rel p.1 p.2)).card =
      ∑ i ∈ S, (T.filter (rel i)).card := by
  classical
  simp only [card_eq_sum_ones,sum_filter,sum_product]

theorem far_pairs_card {ι : Type*} (S : Finset ι) (P : ι → ℝ)
    (near : ι → ι → Prop) (pstar ε : ℝ) (hpstar : 0 < pstar)
    (hlower : ∀ i ∈ S, pstar ≤ P i)
    (hnearmass : ∀ i ∈ S, ∑ j ∈ S.filter (near i), P j ≤ ε)
    (hsmall : 2*ε ≤ (S.card:ℝ)*pstar) :
    (S.card:ℝ)^2/2 ≤ (((S ×ˢ S).filter (fun p => ¬ near p.1 p.2)).card : ℝ) := by
  classical
  have hnear (i : ι) (hi : i ∈ S) :
      ((S.filter (near i)).card:ℝ)*pstar ≤ ε := by
    calc
      _ = ∑ j ∈ S.filter (near i), pstar := by simp
      _ ≤ ∑ j ∈ S.filter (near i), P j := sum_le_sum (fun j hj => hlower j (mem_filter.mp hj).1)
      _ ≤ ε := hnearmass i hi
  have hfar (i : ι) (hi : i ∈ S) :
      (S.card:ℝ)/2 ≤ ((S.filter (fun j => ¬ near i j)).card:ℝ) := by
    have heq := card_filter_add_card_filter_not (s:=S) (p:=near i)
    have heq' : ((S.filter (near i)).card:ℝ)+((S.filter (fun j => ¬ near i j)).card:ℝ) = S.card := by
      exact_mod_cast heq
    have hh := hnear i hi
    nlinarith only [hsmall,heq',hh,hpstar]
  have heq : (((S ×ˢ S).filter (fun p => ¬ near p.1 p.2)).card : ℝ) =
      ∑ i ∈ S, ((S.filter (fun j => ¬ near i j)).card : ℝ) := by
    simp only [card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,sum_filter,sum_product,
      Nat.cast_ite,Nat.cast_zero]
  calc
    _ = ∑ _i ∈ S, (S.card:ℝ)/2 := by simp; ring
    _ ≤ ∑ i ∈ S, ((S.filter (fun j => ¬ near i j)).card : ℝ) := sum_le_sum hfar
    _ = _ := heq.symm

theorem pair_orientation_fiber {ι : Type*} (S : Finset (ι × ι))
    (orient : ι × ι → ι × ι)
    (horient : ∀ p ∈ S, orient p = p ∨ orient p = p.swap)
    (q : ι × ι) :
    (S.filter (fun p => orient p = q)).card ≤ 2 := by
  classical
  have hsub : S.filter (fun p => orient p = q) ⊆ {q,q.swap} := by
    intro p hp
    obtain ⟨hp,heq⟩ := mem_filter.mp hp
    rcases horient p hp with h | h
    · have : p=q := h.symm.trans heq
      simp [this]
    · have : p=q.swap := by have hh := congrArg Prod.swap (h.symm.trans heq); simpa using hh
      simp [this]
  calc
    _ ≤ ( {q,q.swap} : Finset (ι × ι)).card := Finset.card_le_card hsub
    _ ≤ ({q.swap} : Finset (ι × ι)).card + 1 := card_insert_le _ _
    _ = 2 := by simp

theorem ordered_cost_multiplicity {X ι : Type*} (S : Finset ι)
    (B : ι → ι → Set X) (A : ι → Set X) (N M : ℕ)
    (hsource : ∀ i ∈ S, ∀ j ∈ S, B i j ⊆ A i)
    (hfirst : ∀ x, (S.filter (fun i => x ∈ A i)).card ≤ N)
    (hsecond : ∀ i ∈ S, ∀ x, (S.filter (fun j => x ∈ B i j)).card ≤ M) :
    ∀ x, ((S ×ˢ S).filter (fun p => x ∈ B p.1 p.2)).card ≤ N*M := by
  classical
  intro x
  rw [card_filter_product S S (fun i j => x ∈ B i j)]
  have heq : ∑ i ∈ S, (S.filter (fun j => x ∈ B i j)).card =
      ∑ i ∈ S.filter (fun i => x ∈ A i), (S.filter (fun j => x ∈ B i j)).card := by
    symm
    apply sum_subset (filter_subset _ _) ?_
    intro i hi hnot
    have hx : x ∉ A i := by simpa only [mem_filter,hi,true_and] using hnot
    have hf : S.filter (fun j => x ∈ B i j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hj,hxB⟩ := mem_filter.mp hj
      exact hx (hsource i hi j hj hxB)
    simp [hf]
  rw [heq]
  calc
    _ ≤ ∑ _i ∈ S.filter (fun i => x ∈ A i), M :=
      sum_le_sum (fun i hi => hsecond i (mem_filter.mp hi).1 x)
    _ = (S.filter (fun i => x ∈ A i)).card*M := by simp
    _ ≤ N*M := Nat.mul_le_mul_right M (hfirst x)

end CannonPairs

end

end
end
end
end
end

end OAI
