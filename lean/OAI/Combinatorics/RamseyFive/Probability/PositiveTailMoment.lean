import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.TailMoment
open scoped BigOperators Classical

theorem positive_tail_moment {I : Type*} [Fintype I] (f : I → ℝ)
    (hf0 : ∀ i,0 < f i) (hf2 : ∀ i,f i ≤ 2) (A : ℝ) (hA : 0 ≤ A)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun i => a ≤ f i).card:ℝ)*a^K ≤ A) :
    ∑ i,f i^R ≤ 2*A*2^R := by
  have hnear (i : I) : ∃ n : ℕ,(1/2:ℝ)^(n+1) < f i/2 ∧ f i/2 ≤ (1/2:ℝ)^n :=
    exists_nat_pow_near_of_lt_one (div_pos (hf0 i) (by norm_num)) (by linarith [hf2 i])
      (by norm_num) (by norm_num)
  let index : I → ℕ := fun i => (hnear i).choose
  have hind (i : I) := (hnear i).choose_spec
  let N := Finset.univ.sup index+1
  have hidx (i : I) (_ : i ∈ Finset.univ) : index i ∈ Finset.range N := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  rw [←Finset.sum_fiberwise_of_maps_to hidx (fun i => f i^R)]
  have hlevel (n : ℕ) :
      (∑ i ∈ Finset.univ.filter fun i => index i=n,f i^R) ≤ A*2^R*(1/2:ℝ)^n := by
    let E := Finset.univ.filter fun i => index i=n
    let a : ℝ := (1/2:ℝ)^n
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsub : E ⊆ Finset.univ.filter fun i => a ≤ f i := by
      intro i hi
      have he := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
      have hlo := (hind i).1
      change (1/2:ℝ)^(index i+1) < f i/2 at hlo
      rw [he,pow_succ] at hlo
      dsimp [a]
      linarith
    have hc : (E.card:ℝ)*a^K ≤ A :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
        (pow_nonneg ha.le _)).trans (htail a ha (ha1.trans (by norm_num)))
    calc
      _ ≤ ∑ i ∈ E,(2*a)^R := Finset.sum_le_sum fun i hi => by
        have he := (Finset.mem_filter.mp hi).2
        have hup := (hind i).2
        change f i/2 ≤ (1/2:ℝ)^(index i) at hup
        rw [he] at hup
        exact pow_le_pow_left₀ (hf0 i).le (by dsimp [a]; linarith) R
      _ = (E.card:ℝ)*2^R*a^R := by rw [Finset.sum_const,nsmul_eq_mul,mul_pow]; ring
      _ ≤ (E.card:ℝ)*2^R*a^(K+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ha.le ha1 hR) (by positivity)
      _ = ((E.card:ℝ)*a^K)*(2^R*a) := by rw [pow_succ]; ring
      _ ≤ A*(2^R*a) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.range N,A*2^R*(1/2:ℝ)^n := Finset.sum_le_sum fun n _ => hlevel n
    _ = A*2^R*∑ n ∈ Finset.range N,(1/2:ℝ)^n := (Finset.mul_sum ..).symm
    _ ≤ A*2^R*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (by positivity)
    _ = _ := by ring

theorem tail_moment {I : Type*} [Fintype I] (f : I → ℝ)
    (hf0 : ∀ i,0 ≤ f i) (hf2 : ∀ i,f i ≤ 2) (A : ℝ) (hA : 0 ≤ A)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun i => a ≤ f i).card:ℝ)*a^K ≤ A) :
    ∑ i,f i^R ≤ 2*A*2^R := by
  let S := Finset.univ.filter fun i => 0 < f i
  have hs : (∑ i,f i^R) = ∑ i ∈ S,f i^R := by
    apply (Finset.sum_subset (Finset.subset_univ _) _).symm
    intro i _ hi
    have hzero : f i = 0 := by
      have := not_lt.mp (show ¬0 < f i by simpa [S] using hi)
      linarith [hf0 i]
    simp [hzero,show R ≠ 0 by omega]
  rw [hs]
  rw [Finset.sum_subtype S (p := fun i => 0 < f i) (by intro i; simp [S])]
  apply positive_tail_moment (fun i : {i : I // 0 < f i} => f i.val)
    (fun i => i.property) (fun i => hf2 i.val) A hA K R hR
  intro a ha ha2
  have hc : (Finset.univ.filter fun i : {i : I // 0 < f i} => a ≤ f i.val).card ≤
      (Finset.univ.filter fun i => a ≤ f i).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.val)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg ha.le _)).trans
    (htail a ha ha2)

end SharpRamseyFive.TailMoment

end OAI
