import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCovariance
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalUnitary

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def GenericParameters (n : ℕ) (X : ℕ → ℂ) : Prop :=
  ∀ a b, a ≤ n → b ≤ n → exchangeDenominator (X a) (X b)≠0

theorem genericParameters_swap {n i : ℕ} (hi : i < n) {X : ℕ → ℂ}
    (hG : GenericParameters n X) : GenericParameters n (swapSite i X) := by
  intro a b ha hb
  apply hG
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> omega

theorem swapSite_eq_of_equal {α : Type*} (i : ℕ) (X : ℕ → α)
    (he : X i=X (i+1)) : swapSite i X=X := by
  funext k
  by_cases h0 : k=i
  · subst k; simp [he]
  by_cases h1 : k=i+1
  · subst k; simp [he]
  exact swapSite_other h0 h1 X

theorem naturalPrescription_collision_forward {ψ : NatSpectralTensor} {n : ℕ}
    (hψ : LowerExchange ψ n) (d : ℕ) :
    ∀ (i : ℕ) (_hi : i+d ≤ n) (X : ℕ → ℂ), GenericParameters n X →
      X i=X (i+d) → naturalPrescription ψ n i X=naturalPrescription ψ n (i+d) X := by
  induction d with
  | zero => intro i hi X hG he; simp
  | succ d ih =>
    intro i hi X hG he
    apply siteR_injective i (X i) (X (i+1)) (hG _ _ (by omega) (by omega))
      (hG _ _ (by omega) (by omega))
    rw [naturalPrescription_mark_right (by omega)]
    by_cases hd : d=0
    · subst d
      simp only [Nat.zero_add] at he ⊢
      rw [swapSite_eq_of_equal i X he,he,siteR_regular]
    · have hbefore := naturalPrescription_swap_before (ψ:=ψ) (i:=i+(d+1)) (j:=i)
        hi (by omega) hψ X
      rw [hbefore]
      congr 1
      have h := ih (i+1) (by omega) (swapSite i X) (genericParameters_swap (by omega) hG)
      have hj : swapSite i X (i+1+d)=X (i+(d+1)) := by
        rw [swapSite_other (by omega : i+1+d≠i) (by omega : i+1+d≠i+1)]
        congr 1; omega
      rw [swapSite_right,hj] at h
      simpa only [show i+1+d=i+(d+1) by omega] using h he

theorem naturalPrescription_collision_generic {ψ : NatSpectralTensor} {n i j : ℕ}
    (hψ : LowerExchange ψ n) (hi : i ≤ n) (hj : j ≤ n)
    (X : ℕ → ℂ) (hG : GenericParameters n X) (he : X i=X j) :
    naturalPrescription ψ n i X=naturalPrescription ψ n j X := by
  rcases le_total i j with h|h
  · have h' := naturalPrescription_collision_forward hψ (j-i) i (by omega) X hG
    simpa only [Nat.add_sub_of_le h] using h' (by simpa only [Nat.add_sub_of_le h] using he)
  · have h' := naturalPrescription_collision_forward hψ (i-j) j (by omega) X hG
    symm
    simpa only [Nat.add_sub_of_le h] using h' (by simpa only [Nat.add_sub_of_le h] using he.symm)

end PolynomialVacuumAlgebra

end OAI
