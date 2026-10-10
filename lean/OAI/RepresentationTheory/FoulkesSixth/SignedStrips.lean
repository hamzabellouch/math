import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.StripInterlace

namespace OAI

noncomputable section

namespace Foulkes.Strips
open MvPolynomial Finset

def staircase (n : ℕ) (j : Fin n) : ℕ := n-1-j.val

def shifted {n : ℕ} (γ : Fin n → ℕ) (j : Fin n) : ℕ := γ j + staircase n j

lemma staircase_antitone (n : ℕ) : Antitone (staircase n) := by
  intro j k hjk
  simp only [staircase]
  exact Nat.sub_le_sub_left hjk (n-1)

lemma shifted_antitone {n : ℕ} {γ : Fin n → ℕ} (hγ : Antitone γ) : Antitone (shifted γ) := by
  intro j k hjk
  exact add_le_add (hγ hjk) (staircase_antitone n hjk)

lemma shifted_sum {n i b : ℕ} (γ μ : Fin n → ℕ)
    (hs : ∑ j, γ j = (∑ j, μ j) + i*b) :
    ∑ j, shifted γ j = (∑ j, shifted μ j) + i*b := by
  simp only [shifted, Finset.sum_add_distrib]
  omega

def stripCoeff {n : ℕ} (i b : ℕ) (γ μ : Fin n → ℕ) : ℤ :=
  (completePowers n i b * alternant (shifted μ)).coeff (expVector (shifted γ))

theorem signed_strips {n i b : ℕ} (hi : 1 ≤ i) (hb : 1 ≤ b)
    (γ μ : Fin n → ℕ) (hγ : Antitone γ) (hμ : Antitone μ)
    (hsize : (∑ j, γ j) - (∑ j, μ j) = i*b) :
    (stripCoeff i b γ μ = 0 ∨ stripCoeff i b γ μ = 1 ∨ stripCoeff i b γ μ = -1) ∧
    (stripCoeff i b γ μ ≠ 0 → ∀ j : Fin n, μ j ≤ γ j ∧
      ∀ hji : j.val+i < n, γ ⟨j.val+i,hji⟩ ≤ μ j) := by
  have hip : 0 < i := by omega
  have hbp : 0 < b := by omega
  have hprod : 0 < i*b := Nat.mul_pos hip hbp
  have hs : ∑ j, γ j = (∑ j, μ j) + i*b := by omega
  have hbound := signed_strip_abs_le_one hip (shifted γ) (shifted μ) (shifted_sum γ μ hs)
  change Int.natAbs (stripCoeff i b γ μ) ≤ 1 at hbound
  constructor
  · omega
  · intro hnon j
    have heq := coefficient_eq_assignment_det hip (shifted γ) (shifted μ) (shifted_sum γ μ hs)
    change stripCoeff i b γ μ = _ at heq
    have hd : (incidence (assignments i (shifted γ) (shifted μ))).det ≠ 0 := by
      rwa [← heq]
    constructor
    · have hc := containment_of_det_ne_zero (shifted γ) (shifted μ)
        (shifted_antitone hγ) (shifted_antitone hμ) hd j
      simpa only [shifted, Nat.add_le_add_iff_right] using hc
    · intro hji
      have hc := shifted_containment_of_det_ne_zero hip (shifted γ) (shifted μ)
        (shifted_antitone hγ) (shifted_antitone hμ) hd j hji
      simp only [shifted, staircase] at hc
      have hjn := j.isLt
      omega

end Foulkes.Strips

end

end OAI
