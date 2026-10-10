import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterEnergy
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProof

namespace OAI

/-! # Finite multiplicative large sieve for the complex-zero density argument

Summing the full character Parseval identity before discarding imprimitive
characters retains the conductor saving in the Gauss normalization.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem primitive_multiplicative_large_sieve (M Q : ℕ) (hM : 1 ≤ M) (hQ : 1 ≤ Q)
    (J : ℤ) (c : Fin M → ℂ)
    (S : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hS : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ S q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q,
      ‖∑ n, c n * χ ((J + (n.val : ℤ) : ℤ) : ZMod q)‖ ^ 2) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) * ∑ n, ‖c n‖ ^ 2 := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :
      (∑ χ ∈ S q, ‖∑ n, c n * χ ((J + (n.val : ℤ) : ℤ) : ZMod q)‖ ^ 2) ≤
        ∑ h ∈ reducedNumerators q, ‖additiveSieveSum (fun n => star (c n)) J q h‖ ^ 2 := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    let : NeZero q := ⟨ne_of_gt hqpos⟩
    have h := primitive_character_energy_le (S q) (hS q hq) c
      (fun n => ((J + (n.val : ℤ) : ℤ) : ZMod q))
    rw [sum_reducedNumerators_eq_units]
    simpa only [additiveSieveSum, sieveAdditivePhase_eq_stdAddChar,
      ZMod.natCast_zmod_val] using h
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
        ‖additiveSieveSum (fun n => star (c n)) J q h‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := by
      simpa only [norm_star] using
        publishedAdditiveLargeSieve M Q hM hQ J (fun n => star (c n))

end Ostmann

end OAI
