import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.AntecedentCountLemmas
import OAI.Computability.UniqueGames.Analysis.SubspaceCountingLemmas

namespace OAI

section

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

noncomputable section
namespace UniqueGamesTheorem.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

private lemma half_cancel (a b : ℕ) :
    (2:ℝ)^a * ((2:ℝ)⁻¹)^(a+b) = ((2:ℝ)⁻¹)^b := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma half_sum_identity (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) + 2*((2:ℝ)⁻¹)^n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    norm_num at *
    linarith

private lemma half_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) ≤ 2 := by
  have hid := half_sum_identity n
  have hp : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
  linarith

private lemma finite_level_sum {α : Type*} (s : Finset α) (r : α → ℕ) (d : ℕ)
    (hdeg : ∀ x ∈ s, r x ≤ d)
    (hc : ∀ k, ((s.filter (fun x => r x=k)).card : ℝ) ≤ (2:ℝ)^(3*d*k)) :
    (∑ x ∈ s, ((2:ℝ)⁻¹)^(4*d*r x)) ≤ 2 := by
  classical
  have hmap : ∀ x ∈ s, r x ∈ Finset.range (d+1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg x hx))
  have hone (n : ℕ) : ((2:ℝ)⁻¹)^n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
      norm_num at *
      nlinarith
  calc
    _ = ∑ k ∈ Finset.range (d+1), ∑ x ∈ s.filter (fun x => r x=k),
        ((2:ℝ)⁻¹)^(4*d*r x) :=
      (Finset.sum_fiberwise_of_maps_to (g := r) hmap _).symm
    _ ≤ ∑ k ∈ Finset.range (d+1), ((2:ℝ)⁻¹)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hmul : k ≤ d*k := by
        by_cases hd : d=0
        · subst d
          have : k=0 := by omega
          simp [this]
        · have : 1 ≤ d := by omega
          simpa using Nat.mul_le_mul_right k this
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmul
      have hdecay : ((2:ℝ)⁻¹)^(d*k) ≤ ((2:ℝ)⁻¹)^k := by
        rw [hj, pow_add]
        simpa using mul_le_mul_of_nonneg_left (hone j)
          (by positivity : 0 ≤ ((2:ℝ)⁻¹)^k)
      calc
        _ = ((s.filter (fun x => r x=k)).card : ℝ)*((2:ℝ)⁻¹)^(4*d*k) := by
          calc
            _ = ∑ x ∈ s.filter (fun x => r x=k), ((2:ℝ)⁻¹)^(4*d*k) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
            _ = _ := by simp
        _ ≤ (2:ℝ)^(3*d*k)*((2:ℝ)⁻¹)^(4*d*k) :=
          mul_le_mul_of_nonneg_right (hc k) (by positivity)
        _ = ((2:ℝ)⁻¹)^(d*k) := by
          have he : 4*d*k=3*d*k+d*k := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
        _ ≤ _ := hdecay
    _ ≤ 2 := half_sum_le (d+1)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

abbrev rank (X : E →ₗ[F2] F) : ℕ := finrank F2 X.range

@[instance_reducible] private def vectorFintype (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Fintype V :=
  Fintype.ofEquiv (Fin (finrank F2 V) → F2) (Module.finBasis F2 V).equivFun.symm.toEquiv

@[instance_reducible] def compressedFintype (X : E →ₗ[F2] F) : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := by
  classical
  letI := vectorFintype X.ker
  letI := vectorFintype (F ⧸ X.range)
  exact Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

/-- Energy of the actual merged derivative coefficients. -/
def energy (a : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ := by
  classical
  letI := compressedFintype X
  exact ∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
    then a Y else 0)^2

/-- Sum of predecessor weights, using the actual binary linear-map count. -/
theorem predecessor_weight_sum (Y : E →ₗ[F2] F) (d : ℕ) (hd : rank Y ≤ d) :
    (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
      ((2:ℝ)⁻¹)^(4*d*rank X)) ≤ 2 := by
  classical
  apply finite_level_sum _ rank d
  · intro X hX
    have hp := (Finset.mem_filter.mp hX).2
    change rank Y = rank X + rank (Y-X) at hp
    omega
  · intro k
    have hneg (X : E →ₗ[F2] F) : -X = X := by
      have htwo : (1+1:F2)=0 := by decide
      have hxx : X+X=0 := by
        have h := congrArg (fun c:F2 => c • X) htwo
        simpa only [add_smul, one_smul, zero_smul] using h
      exact neg_eq_iff_add_eq_zero.mpr hxx
    have hpred (X : E →ₗ[F2] F) : RankBelow X Y ↔
        rank Y = rank X + rank (Y+X) := by
      change (rank Y = rank X + rank (Y-X)) ↔ _
      rw [sub_eq_add_neg, hneg X]
    have hc := SubspaceCounting.card_binary_predecessors_le Y d k hd
    have hn : ((Finset.univ.filter (fun X => RankBelow X Y)).filter
        (fun X => rank X=k)).card ≤ 2^(3*d*k) := by
      simp_rw [hpred]
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter,
        and_comm, rank] using hc
    exact_mod_cast hn

/-- Corrected Appendix A.4, in exact coefficient form, for arbitrary real
coefficients supported on maps of rank at most d. -/
theorem weighted_fourth_coefficient_energy (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2 := by
  classical
  let A : ℝ := ∑ Y, a Y^2
  let AX (X : E →ₗ[F2] F) : ℝ := ∑ Y, if RankBelow X Y then a Y^2 else 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAX (X : E →ₗ[F2] F) : 0 ≤ AX X := by
    apply Finset.sum_nonneg
    intro Y _
    split_ifs <;> positivity
  have hAXA (X : E →ₗ[F2] F) : AX X ≤ A := by
    apply Finset.sum_le_sum
    intro Y _
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hmass : (∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) ≤ 2*A := by
    calc
      _ = ∑ Y, a Y^2 * (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
          ((2:ℝ)⁻¹)^(4*d*rank X)) := by
        simp only [AX, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Y _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X _
        split_ifs <;> ring
      _ ≤ ∑ Y, a Y^2*2 := by
        apply Finset.sum_le_sum
        intro Y _
        by_cases hy : rank Y ≤ d
        · exact mul_le_mul_of_nonneg_left (predecessor_weight_sum Y d hy) (sq_nonneg _)
        · have hz := hdegree Y (Nat.lt_of_not_ge hy)
          rw [hz]
          simp
      _ = 2*A := by rw [← Finset.sum_mul]; dsimp [A]; ring
  have hE (X : E →ₗ[F2] F) : 0 ≤ energy a X := by
    unfold energy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoarse (X : E →ₗ[F2] F) : energy a X ≤ (2:ℝ)^(2*d*rank X)*AX X := by
    let : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := compressedFintype X
    have h10 := DerivativeEnergy.coefficient_energy X a d hdegree
    have he : 2*rank X*(d-rank X) ≤ 2*d*rank X := by
      calc
        _ ≤ 2*rank X*d := Nat.mul_le_mul_left _ (Nat.sub_le d (rank X))
        _ = _ := by ring
    have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
    have hp : (2:ℝ)^(2*rank X*(d-rank X)) ≤ (2:ℝ)^(2*d*rank X) := by exact_mod_cast hn
    exact h10.trans (mul_le_mul_of_nonneg_right hp (hAX X))
  have hfour (X : E →ₗ[F2] F) : (energy a X)^2 ≤ (2:ℝ)^(4*d*rank X)*(A*AX X) := by
    have hs : (energy a X)^2 ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 :=
      (sq_le_sq₀ (hE X) (mul_nonneg (by positivity) (hAX X))).mpr (hcoarse X)
    have ha : (AX X)^2 ≤ A*AX X := by
      have hh := mul_le_mul_of_nonneg_right (hAXA X) (hAX X)
      simpa [pow_two] using hh
    calc
      _ ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 := hs
      _ = ((2:ℝ)^(2*d*rank X))^2*(AX X)^2 := by rw [mul_pow]
      _ ≤ ((2:ℝ)^(2*d*rank X))^2*(A*AX X) :=
        mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = _ := by
        rw [← pow_mul]
        congr 2
        ring
  calc
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2)
        ≤ ∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*(A*AX X) := by
      apply Finset.sum_le_sum
      intro X _
      calc
        _ ≤ ((2:ℝ)⁻¹)^(8*d*rank X)*((2:ℝ)^(4*d*rank X)*(A*AX X)) :=
          mul_le_mul_of_nonneg_left (hfour X) (by positivity)
        _ = ((2:ℝ)^(4*d*rank X)*((2:ℝ)⁻¹)^(8*d*rank X))*(A*AX X) := by ring
        _ = _ := by
          have he : 8*d*rank X=4*d*rank X+4*d*rank X := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
    _ = A*(∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    _ ≤ A*(2*A) := mul_le_mul_of_nonneg_left hmass hA
    _ = 2*A^2 := by ring

end UniqueGamesTheorem.Appendix.WeightedFourthMoment

end

end

end OAI
