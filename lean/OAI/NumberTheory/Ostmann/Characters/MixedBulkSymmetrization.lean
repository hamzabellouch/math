import OAI.NumberTheory.Ostmann.Characters.MixedExternalGram
import OAI.NumberTheory.Ostmann.Characters.TreeArrangementFraction

namespace OAI

/-! # Symmetrization of the original mixed law, with bad pairs paid by energy -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def mixedBulkSymmetrize {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (s : ℤ) (y : B → A) (x z : ℝ) : ℂ :=
  finiteFamilyAverage (fun e : Equiv.Perm (TreeLeafIndex n × Fin m) =>
    fun _ : Unit => F s (selectedBulkSample slot e⁻¹ y) x z) ()

theorem mixedExternalAverage_weighted_square_permute {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s (selectedBulkSample slot e y) x z‖ ^ 2 : ℂ) * W s y x z) =
    mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z) := by
  have h := mixedExternalAverage_selectedBulkSample slot e ν hν N u v r w center
    (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)
  simpa only [hW] using h

/-- The ordinary diagonal energy controls every bad pair. Only good relative
permutations use the signed arithmetic correlation estimate. -/
theorem mixedBulkSymmetrize_energy_bound {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (hm : 1 ≤ m) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z)
    (hinv : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ D)
    (hgood : ∀ e : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n) →
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z => (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
          W s y x z)‖ ≤ E) :
    (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  have hall (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z => (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
          W s y x z)‖ ≤ D := by
    apply mixedExternalAverage_weighted_correlation_bound ν hν N u v r w center
      F (fun s y x z => F s (selectedBulkSample slot e y) x z) W hW D hdiag
    rw [mixedExternalAverage_weighted_square_permute slot e ν hidentical N u v r w center F W hinv]
    exact hdiag
  have hpair (e f : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z =>
          (F s (selectedBulkSample slot e⁻¹ y) x z *
            star (F s (selectedBulkSample slot f⁻¹ y) x z)) * W s y x z)‖ ≤
        if BadTreeArrangement (e⁻¹ * f) then D else E := by
    rw [mixedExternalAverage_pair_swap]
    rw [mixedExternalAverage_relative_pair slot f⁻¹ e⁻¹ ν hidentical N u v r w center F
      (fun s y x z => (W s y x z : ℂ)) (fun e s y x z => congrArg Complex.ofReal (hinv e s y x z))]
    simp only [inv_inv]
    split_ifs with hbad
    · exact hall _
    · exact hgood _ (by simpa only [BadTreeArrangement, not_lt] using hbad)
  have hb := mixedExternalAverage_family_bound ν N u v r w center
    (fun e s y x z => F s (selectedBulkSample slot e⁻¹ y) x z) W
    BadTreeArrangement D E hE hpair
  apply hb.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right (badTreeArrangement_fraction_bound n m hm) hD

end Ostmann

end OAI
