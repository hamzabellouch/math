import OAI.InformationTheory.Entanglement.RestrictedIntersections

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction

def Q : ℕ := b^3
def K : ℕ := 1086373952
def κ : ℕ := 3*a₀*b^2

irreducible_def binomialDimension (q : ℕ) : ℕ := Nat.choose q 8
def L : ℕ := binomialDimension Q
lemma L_def : L = Nat.choose Q 8 := binomialDimension_def Q
def D : ℕ := 4^L
def m : ℕ := Q*D

lemma base_card : Fintype.card Base=b := by
  let S := ((Finset.univ : Finset (Fin 1028)).powersetCard 514).filter (({0} : Finset (Fin 1028)) ⊆ ·)
  let e : Base ≃ S := {
    toFun := fun A => ⟨A.val,by simpa only [S,Finset.mem_filter,Finset.mem_powersetCard,
      Finset.subset_univ,true_and,Finset.singleton_subset_iff] using A.property⟩
    invFun := fun A => ⟨A.val,by simpa only [S,Finset.mem_filter,Finset.mem_powersetCard,
      Finset.subset_univ,true_and,Finset.singleton_subset_iff] using A.property⟩
    left_inv := fun A => rfl
    right_inv := fun A => rfl }
  rw [Fintype.card_congr e,Fintype.card_coe]
  change S.card=b
  dsimp only [S]
  rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _) (by simp)]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton,b]

lemma b_pos : 0 < b := Nat.choose_pos (by decide)
lemma a₀_pos : 0 < a₀ := by
  have he : 1 ≤ a₀ := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range 257) => Nat.zero_le (Nat.choose 1028 j))
      (show 0 ∈ Finset.range 257 by simp)
    simpa only [Nat.choose_zero_right,a₀] using h
  omega

lemma choose_le_of_le_half {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ n/2) :
    Nat.choose n i ≤ Nat.choose n j := by
  induction hij with
  | refl => rfl
  | @step j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma a₀_upper : a₀ ≤ 257*Nat.choose 1028 257 := by
  calc
    a₀ ≤ ∑ j ∈ Finset.range 257, Nat.choose 1028 257 := by
      apply Finset.sum_le_sum
      intro j hj
      exact choose_le_of_le_half (by have := Finset.mem_range.mp hj; omega) (by decide)
    _ = _ := by simp
lemma central_eq : Nat.choose 1028 514=2*b := by
  have hs : Nat.choose 1027 514=Nat.choose 1027 513 := by
    simpa only [show 1027-513=514 by rfl] using Nat.choose_symm (show 513≤1027 by decide)
  change Nat.choose (1027+1) (513+1)=_
  rw [Nat.choose_succ_succ,hs]
  unfold b
  omega
lemma b_lower : 2^1027 ≤ 1029*b := by
  have hs : 2^1028 ≤ 1029*(2*b) := by
    rw [← Nat.sum_range_choose 1028]
    calc
      _ ≤ ∑ j ∈ Finset.range 1029, Nat.choose 1028 514 := by
        apply Finset.sum_le_sum
        intro j _
        exact Nat.choose_le_middle j 1028
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,central_eq,Nat.cast_id]
  have hp : (2 : ℕ)^1028=2*2^1027 := by rw [show 1028=1027+1 by rfl,pow_succ,mul_comm]
  rw [hp] at hs
  omega
lemma binomial_term : Nat.choose 1028 257*3^771 ≤ 4^1028 := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (1028+1)) => Nat.zero_le ((1:ℕ)^j*3^(1028-j)*Nat.choose 1028 j))
    (show 257 ∈ Finset.range (1028+1) by simp)
  have he : (∑ j ∈ Finset.range (1028+1), (1:ℕ)^j*3^(1028-j)*Nat.choose 1028 j)=4^1028 := by
    simpa only [Nat.cast_id, show (1 : ℕ)+3=4 by rfl] using
      (add_pow (1 : ℕ) 3 1028).symm
  rw [he] at hs
  simpa only [one_pow,one_mul,show 1028-257=771 by rfl,show (1:ℕ)+3=4 by rfl,mul_comm]
    using hs
lemma arithmetic_gap : 3*1086373952*257*1029*4^1028 < 2^1027*3^771 := by
  rw [show 1028=128*8+4 by rfl,show 1027=128*8+3 by rfl,
    show 771=128*6+3 by rfl]
  simp only [pow_add,pow_mul]
  norm_num
lemma a₀_scaled_bound : a₀*3^771 ≤ 257*4^1028 := by
  calc
    _ ≤ (257*Nat.choose 1028 257)*3^771 := Nat.mul_le_mul_right _ a₀_upper
    _ = 257*(Nat.choose 1028 257*3^771) := mul_assoc _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ binomial_term
lemma strict_natural_gap : 3*K*a₀ < b := by
  have gap (smallBound largeBound coefficient powerTwo powerThree powerFour : ℕ)
      (positive : 0 < 1029*powerThree)
      (small : smallBound*powerThree ≤ 257*powerFour)
      (large : powerTwo ≤ 1029*largeBound)
      (arithmetic : 3*coefficient*257*1029*powerFour < powerTwo*powerThree) :
      3*coefficient*smallBound < largeBound := by
    apply (Nat.mul_lt_mul_right positive).mp
    calc
      (3*coefficient*smallBound)*(1029*powerThree) =
          3*coefficient*1029*(smallBound*powerThree) := by ring
      _ ≤ 3*coefficient*1029*(257*powerFour) := Nat.mul_le_mul_left _ small
      _ = 3*coefficient*257*1029*powerFour := by ring
      _ < powerTwo*powerThree := arithmetic
      _ ≤ (1029*largeBound)*powerThree := Nat.mul_le_mul_right _ large
      _ = largeBound*(1029*powerThree) := by ring
  exact gap a₀ b K (2^1027) (3^771) (4^1028) (by positivity)
    a₀_scaled_bound b_lower (by unfold K; exact arithmetic_gap)
lemma strict_gap : (κ : ℝ) < (Q : ℝ)/(K : ℝ) := by
  have hb : 0 < (b : ℝ) := Nat.cast_pos.mpr b_pos
  have hk : 0 < (K : ℝ) := by norm_num [K]
  have hn : 3*(K : ℝ)*(a₀ : ℝ) < b := by exact_mod_cast strict_natural_gap
  have hh := mul_lt_mul_of_pos_right hn (sq_pos_of_pos hb)
  rw [lt_div_iff₀ hk]
  dsimp [κ,Q]
  push_cast
  nlinarith
end FiniteConstruction

end

end OAI
