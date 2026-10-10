import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Probability.NegativeStars
import OAI.Combinatorics.KMedian.Rounding.ExactRounding

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open Finset
variable {I : Type} [Fintype I] [DecidableEq I]

theorem integer_law (q : I → ℝ) (K L : ℕ) (hq0 : ∀ i, 0 ≤ q i)
    (hqL : ∀ i, q i ≤ L) (hsum : ∑ i, q i=K) :
    ∃ (μ : FiniteLaw (Finset I)) (C : Finset I → I → ℕ),
      (∀ S, 0 < μ.weight S → (∑ i, C S i)=K ∧ (∀ i, C S i ≤ L) ∧
        (∀ i, C S i=⌊q i⌋₊ ∨ C S i=⌊q i⌋₊+1)) ∧
      (∀ i, μ.expect (fun S => (C S i:ℝ))=q i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => (C S i:ℝ)*(C S j:ℝ)) ≤ q i*q j) ∧
      (∀ i, μ.variance (fun S => (C S i:ℝ)) ≤ q i) := by
  classical
  let m := fun i => ⌊q i⌋₊
  let p := fun i => q i-(m i:ℝ)
  have hmf : ∀ i, (m i:ℝ) ≤ q i := fun i => Nat.floor_le (hq0 i)
  have hp0 : ∀ i, 0 ≤ p i := fun i => sub_nonneg.mpr (hmf i)
  have hp1 : ∀ i, p i ≤ 1 := by
    intro i
    have h := Nat.lt_floor_add_one (q i)
    dsimp only [p,m]
    linarith only [h]
  have hmL : ∀ i, m i ≤ L := by
    intro i
    exact_mod_cast (hmf i).trans (hqL i)
  have hmK : (∑ i, m i) ≤ K := by
    have hh := (sum_le_sum (fun i (_ : i ∈ univ) => hmf i)).trans_eq hsum
    exact_mod_cast hh
  have hpK : (∑ i, p i)=(K-∑ i, m i:ℕ) := by
    simp only [p,sum_sub_distrib,hsum,Nat.cast_sub hmK,Nat.cast_sum]
  obtain ⟨μ,hs,hm,hpair⟩ := exact_law p (K-∑ i, m i) hp0 hp1 hpK
  let C := fun (S : Finset I) i => m i+if i ∈ S then 1 else 0
  have hCr : ∀ S i, (C S i:ℝ)=(m i:ℝ)+indicator S i := by
    intro S i
    simp only [C,Nat.cast_add,indicator]
    split_ifs <;> simp only [Nat.cast_one,Nat.cast_zero]
  have hmean : ∀ i, μ.expect (fun S => (C S i:ℝ))=q i := by
    intro i
    simp_rw [hCr]
    rw [FiniteLaw.expect_add,FiniteLaw.expect_const]
    change (m i:ℝ)+μ.prob (fun S => i ∈ S)=q i
    rw [hm]
    dsimp only [p]
    ring
  have hsup : ∀ S, 0 < μ.weight S → (∑ i, C S i)=K ∧ (∀ i, C S i ≤ L) ∧
      (∀ i, C S i=⌊q i⌋₊ ∨ C S i=⌊q i⌋₊+1) := by
    intro S hS
    refine ⟨?_,?_,?_⟩
    · have he : (∑ i, C S i)=(∑ i, m i)+S.card := by
        simp only [C,sum_add_distrib,sum_boole,filter_univ_mem,Nat.cast_id]
      rw [he,hs S hS]
      omega
    · intro i
      by_cases hi : i ∈ S
      · have hlt : m i < L := by
          by_contra hn
          have heq : m i=L := le_antisymm (hmL i) (le_of_not_gt hn)
          have hpz : p i=0 := by
            dsimp only [p]
            have hlo := hmf i
            rw [heq] at hlo ⊢
            exact sub_eq_zero.mpr (le_antisymm (hqL i) hlo)
          exact μ.prob_zero_support (fun T => i ∈ T) ((hm i).trans hpz) S hS hi
        simpa only [C,ite_eq_left hi] using Nat.add_one_le_iff.mpr hlt
      · simpa only [C,ite_eq_right hi,add_zero] using hmL i
    · intro i
      dsimp only [C,m]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
  refine ⟨μ,C,hsup,hmean,?_,?_⟩
  · intro i j hij
    simp_rw [hCr]
    have he := Preparation.activation_count_pair μ (fun S => indicator S i) (fun S => indicator S j)
      (m := m i) (n := m j) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hm i) (hm j) (hpair i j hij)
    simpa only [p,add_sub_cancel] using he
  · intro i
    apply μ.adjacent_variance (fun S => (C S i:ℝ)) (m := m i) (Nat.cast_nonneg _) _ (hmean i)
    intro S hS
    rcases (hsup S hS).2.2 i with he | he
    · exact Or.inl (by exact_mod_cast he)
    · exact Or.inr (by exact_mod_cast he)

end MetricKMedian.WeightedRounding
end
end

end OAI
