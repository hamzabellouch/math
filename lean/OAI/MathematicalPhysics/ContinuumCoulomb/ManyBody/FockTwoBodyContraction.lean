import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockOneBodyIntegral

namespace OAI

/-! The two occupied-coordinate contraction, with the signs obtained from
the actual antisymmetric coefficient tensor. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockTwoBodyContraction
open Laughlin

def pairInsert {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : Laughlin.Configuration (n+2) Q :=
  i.insertNth a (j.insertNth b c)

theorem pairInsert_left {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : pairInsert i j a b c i = a := by
  simp only [pairInsert,Fin.insertNth_apply_same]

theorem pairInsert_right {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) : pairInsert i j a b c (i.succAbove j) = b := by
  simp only [pairInsert,Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same]

theorem pairInsert_rest {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1))
    (c : Laughlin.Configuration n Q) (k : Fin n) :
    pairInsert i j a b c (i.succAbove (j.succAbove k)) = c k := by
  simp only [pairInsert,Fin.insertNth_apply_succAbove]

theorem pairInsert_coefficient {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (a b : Fin (Q+1)) (c : Laughlin.Configuration n Q) :
    ψ (pairInsert i j a b c) = (-1:ℂ)^(i.val+j.val)*ψ (Fin.cons a (Fin.cons b c)) := by
  rw [pairInsert,antisymmetric_insertNth hψ]
  rw [antisymmetric_insertNth (antisymmetric_cons hψ a),pow_add]
  ring

theorem pairInsert_delta {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (a b a' b' : Fin (Q+1)) (c d : Laughlin.Configuration n Q) :
    (∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j),
      if pairInsert i j a b c k=pairInsert i j a' b' d k then (1:ℂ) else 0) =
      if c=d then 1 else 0 := by
  by_cases h : c=d
  · subst d
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hki
    have hl : l ≠ j := fun he => hkj (congrArg i.succAbove he)
    obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hl
    simp only [pairInsert_rest,ite_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    have hki : i.succAbove (j.succAbove k) ≠ i := Fin.succAbove_ne _ _
    have hkj : i.succAbove (j.succAbove k) ≠ i.succAbove j := by
      rw [ne_eq,Fin.succAbove_right_inj]
      exact Fin.succAbove_ne _ _
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,
      Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩⟩)
    simp only [pairInsert_rest,ite_eq_right hk]

theorem twoBody_contraction {n Q : ℕ}
    (K : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ)
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (i : Fin (n+2)) (j : Fin (n+1)) :
    (∑ a, ∑ b, (star (ψ a)*φ b)*(K (a i) (a (i.succAbove j)) (b i) (b (i.succAbove j))*
      ∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j), if a k=b k then (1:ℂ) else 0)) =
      ∑ a, ∑ b, ∑ c, ∑ d, K a b c d*∑ e : Laughlin.Configuration n Q,
        star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e)) := by
  have hc (a b a' b' : Fin (Q+1)) (c d : Laughlin.Configuration n Q) :
      star (ψ (pairInsert i j a b c))*φ (pairInsert i j a' b' d) =
        star (ψ (Fin.cons a (Fin.cons b c)))*φ (Fin.cons a' (Fin.cons b' d)) := by
    rw [pairInsert_coefficient ψ hψ,pairInsert_coefficient φ hφ,star_mul,star_pow]
    simp only [star_neg,star_one]
    have hs : (-1:ℂ)^(i.val+j.val)*(-1:ℂ)^(i.val+j.val)=1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = ((-1:ℂ)^(i.val+j.val)*(-1:ℂ)^(i.val+j.val))*
        (star (ψ (Fin.cons a (Fin.cons b c)))*φ (Fin.cons a' (Fin.cons b' d))) := by ring
      _ = _ := by rw [hs,one_mul]
  rw [sum_config_insert i]
  simp_rw [sum_config_insert i,sum_config_insert j]
  change (∑ a, ∑ b, ∑ c, ∑ a', ∑ b', ∑ d,
    (star (ψ (pairInsert i j a b c))*φ (pairInsert i j a' b' d))*
      (K (pairInsert i j a b c i) (pairInsert i j a b c (i.succAbove j))
        (pairInsert i j a' b' d i) (pairInsert i j a' b' d (i.succAbove j))*
        ∏ k ∈ (Finset.univ.erase i).erase (i.succAbove j),
          if pairInsert i j a b c k=pairInsert i j a' b' d k then (1:ℂ) else 0)) = _
  simp only [pairInsert_left,pairInsert_right,pairInsert_delta,hc,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end ContinuumCoulomb.FockTwoBodyContraction

end

end OAI
