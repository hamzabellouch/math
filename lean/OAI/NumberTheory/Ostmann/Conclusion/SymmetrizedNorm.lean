import OAI.NumberTheory.Ostmann.Conclusion.BadPairAverages
import OAI.NumberTheory.Ostmann.Conclusion.PermutationSymmetrization

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Conclusion

def pairCovariance {J G : Type*} [Fintype J] (w : J → ℝ)
    (A : G → J → ℂ) (a b : G) : ℝ :=
  ∑ j, w j * (A a j * conj (A b j)).re

theorem norm_average_sq {G : Type*} [Fintype G] (z : G → ℂ) :
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ a, z a‖^2 =
      (∑ a, ∑ b, (z a * conj (z b)).re)/(Fintype.card G : ℝ)^2 := by
  rw [norm_mul,norm_inv,Complex.norm_natCast,mul_pow,norm_sum_sq_eq_pair_sum]
  simp only [inv_pow,div_eq_mul_inv,mul_comm]

theorem average_energy_eq_pair_average {J G : Type*} [Fintype J] [Fintype G]
    (w : J → ℝ) (A : G → J → ℂ) :
    (∑ j, w j * ‖(Fintype.card G : ℂ)⁻¹ * ∑ a, A a j‖^2) =
      (∑ a, ∑ b, pairCovariance w A a b)/(Fintype.card G : ℝ)^2 := by
  simp_rw [norm_average_sq,← mul_div_assoc,← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ a, ∑ j, ∑ b, w j * (A a j * conj (A b j)).re := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

theorem average_energy_bound {J G : Type*} [Fintype J] [Fintype G] [Group G]
    (w : J → ℝ) (A : G → J → ℂ) (P : G → Prop) [DecidablePred P]
    {B ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ a b, P (a⁻¹*b) → pairCovariance w A a b ≤ B)
    (hgood : ∀ a b, ¬P (a⁻¹*b) → pairCovariance w A a b ≤ ε) :
    (∑ j, w j * ‖(Fintype.card G : ℂ)⁻¹ * ∑ a, A a j‖^2) ≤
      ((Fintype.card {b : G // P b} : ℝ)/(Fintype.card G : ℝ))*B+ε := by
  rw [average_energy_eq_pair_average]
  exact pair_average_bound P (pairCovariance w A) hε hbad hgood

theorem slot_average_energy_bound {J : Type*} [Fintype J] {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (w : J → ℝ)
    (A : Equiv.Perm (Fin r × Fin m) → J → ℂ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbad : ∀ a b, TransferBadArrangement (a⁻¹*b) → pairCovariance w A a b ≤ B)
    (hgood : ∀ a b, ¬TransferBadArrangement (a⁻¹*b) → pairCovariance w A a b ≤ ε) :
    (∑ j, w j * ‖(Fintype.card (Equiv.Perm (Fin r × Fin m)) : ℂ)⁻¹ *
      ∑ a, A a j‖^2) ≤
      ((r : ℝ)^(2*r)*Real.exp ((2-(3/4 : ℝ)*Real.log r)*(r : ℝ)*m))*B+ε := by
  classical
  refine (average_energy_bound w A TransferBadArrangement hε hbad hgood).trans ?_
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_right _ hB
  simpa only [transferBadCount,Nat.card_eq_fintype_card,Fintype.card_perm,
    Fintype.card_prod,Fintype.card_fin] using transferBad_fraction_bound hr hm

end Ostmann.Conclusion

end

end OAI
