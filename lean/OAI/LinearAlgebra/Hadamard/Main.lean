import OAI.LinearAlgebra.Hadamard.CubeFibers

namespace OAI

/-! The dichotomy implied by the two Fourier product identities. -/

open scoped BigOperators Matrix

namespace HadamardSix

def crossCharge : Charge := differenceCharge 2 0 3

def sameCharge : Charge := differenceCharge 2 0 1

lemma crossCharge_eq : crossCharge = ![2, 0, 0, -2, 0, 0] := by decide
lemma sameCharge_eq : sameCharge = ![2, -2, 0, 0, 0, 0] := by decide

private def pairOrdering : Index → Index → Index → Index :=
  ![    ![![0, 1, 2, 3, 4, 5],
      ![0, 1, 2, 3, 4, 5],
      ![0, 2, 1, 3, 4, 5],
      ![0, 1, 2, 3, 4, 5],
      ![0, 1, 2, 4, 3, 5],
      ![0, 1, 2, 4, 5, 3]],
    ![![1, 0, 2, 3, 4, 5],
      ![0, 1, 2, 3, 4, 5],
      ![2, 0, 1, 3, 4, 5],
      ![1, 0, 2, 3, 4, 5],
      ![1, 0, 2, 4, 3, 5],
      ![1, 0, 2, 4, 5, 3]],
    ![![1, 2, 0, 3, 4, 5],
      ![2, 1, 0, 3, 4, 5],
      ![0, 1, 2, 3, 4, 5],
      ![1, 2, 0, 3, 4, 5],
      ![1, 2, 0, 4, 3, 5],
      ![1, 2, 0, 4, 5, 3]],
    ![![3, 4, 5, 0, 1, 2],
      ![4, 3, 5, 0, 1, 2],
      ![4, 5, 3, 0, 1, 2],
      ![0, 1, 2, 3, 4, 5],
      ![3, 4, 5, 0, 1, 2],
      ![3, 4, 5, 0, 2, 1]],
    ![![3, 4, 5, 1, 0, 2],
      ![4, 3, 5, 1, 0, 2],
      ![4, 5, 3, 1, 0, 2],
      ![3, 4, 5, 1, 0, 2],
      ![0, 1, 2, 3, 4, 5],
      ![3, 4, 5, 2, 0, 1]],
    ![![3, 4, 5, 1, 2, 0],
      ![4, 3, 5, 1, 2, 0],
      ![4, 5, 3, 1, 2, 0],
      ![3, 4, 5, 1, 2, 0],
      ![3, 4, 5, 2, 1, 0],
      ![0, 1, 2, 3, 4, 5]]]

private lemma pairOrdering_bijective (i j : Index) :
    Function.Bijective (pairOrdering i j) := by
  fin_cases i <;> fin_cases j <;> decide

lemma double_difference_transport (i j : Index) (hij : i ≠ j) :
    ∃ (p : Equiv.Perm Index) (q : Charge),
      (q = crossCharge ∨ q = sameCharge) ∧
      (permuteCharge p alpha = alpha ∨ permuteCharge p alpha = -alpha) ∧
      permuteCharge p q = differenceCharge 2 i j := by
  let p := Equiv.ofBijective (pairOrdering i j) (pairOrdering_bijective i j)
  refine ⟨p, if i.val / 3 = j.val / 3 then sameCharge else crossCharge, ?_, ?_, ?_⟩
  · split_ifs <;> simp
  · fin_cases i <;> fin_cases j <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

lemma dichotomy_of_product_identities {H : Matrix6} (hH : IsComplexHadamard H)
    (hcross : ∀ p : Equiv.Perm Index,
      g H (permuteCharge p alpha) * g H (permuteCharge p crossCharge) = 0)
    (hsame : ∀ p : Equiv.Perm Index,
      g H (permuteCharge p alpha) * g H (permuteCharge p sameCharge) = 0) :
    (∀ p : Equiv.Perm Index, g H (permuteCharge p alpha) = 0) ∨
      IsComplexHadamard (entrywiseSquare H) := by
  classical
  by_cases hvanish : ∀ p : Equiv.Perm Index, g H (permuteCharge p alpha) = 0
  · exact Or.inl hvanish
  right
  push Not at hvanish
  obtain ⟨p, hp⟩ := hvanish
  let K : Matrix6 := fun i k => H (p.symm i) k
  have hK : IsComplexHadamard K := hH.permute_rows p.symm
  have hnonzero : g K alpha ≠ 0 := by
    simpa [K, ← g_permuteCharge] using hp
  have hnegative : g K (-alpha) ≠ 0 := by
    rw [g_neg hK.1]
    exact star_ne_zero.mpr hnonzero
  have hc (q : Equiv.Perm Index) :
      g K (permuteCharge q alpha) * g K (permuteCharge q crossCharge) = 0 := by
    simpa only [K, ← g_permuteCharge, permuteCharge_trans] using hcross (p.trans q)
  have hs (q : Equiv.Perm Index) :
      g K (permuteCharge q alpha) * g K (permuteCharge q sameCharge) = 0 := by
    simpa only [K, ← g_permuteCharge, permuteCharge_trans] using hsame (p.trans q)
  have hKs : IsComplexHadamard (entrywiseSquare K) := by
    apply (square_hadamard_iff hK.1).mpr
    intro i j hij
    obtain ⟨q, a, ha, hqa, hqx⟩ := double_difference_transport i j hij
    have hprod : g K (permuteCharge q alpha) * g K (permuteCharge q a) = 0 := by
      rcases ha with rfl | rfl
      · exact hc q
      · exact hs q
    rw [hqx] at hprod
    have hfirst : g K (permuteCharge q alpha) ≠ 0 := by
      rcases hqa with hqa | hqa
      · simpa only [hqa] using hnonzero
      · simpa only [hqa] using hnegative
    exact (mul_eq_zero.mp hprod).resolve_left hfirst
  have hback := hKs.permute_rows p
  change IsComplexHadamard (fun i k => H i k ^ 2)
  simpa only [K, entrywiseSquare, Equiv.symm_apply_apply] using hback

end HadamardSix

end OAI
