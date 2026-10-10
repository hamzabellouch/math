import OAI.NumberTheory.Ostmann.Characters.MixedBulkSymmetrization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalEnergy

namespace OAI

/-! # Bulk averaging inside the original product and frequency fibres -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkAverage_statistic {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (G W : (B → A) → ℂ)
    (hG : ∀ e y, G (selectedBulkSample slot e y) = G y) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y *
      mixedBulkSymmetrize n m slot (fun _ y _ _ => W y) 0 y 0 0) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W y := by
  have hc : (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W (selectedBulkSample slot e y)) =
        ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W y := by
    have h := selectedBulkSample_sum slot e ν hν (fun y => G y * W y)
    simpa only [hG, mul_assoc] using h
  unfold mixedBulkSymmetrize finiteFamilyAverage
  simp only [Finset.mul_sum]
  simp_rw [show ∀ (y : B → A) (e : Equiv.Perm (TreeLeafIndex n × Fin m)),
    ((∏ i, ν i (y i) : ℝ) : ℂ) * G y *
      ((Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ)⁻¹ *
        W (selectedBulkSample slot e⁻¹ y)) =
    (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ)⁻¹ *
      (((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W (selectedBulkSample slot e⁻¹ y)) by intros; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- All pointwise cutoffs may remain inside the coefficient. Only the key
and the original independent bulk law are invariant under reassignment. -/
theorem groupedCoefficient_bulk_average {B A K : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (key : (B → A) → K) (hkey : ∀ e y, key (selectedBulkSample slot e y) = key y)
    (W : (B → A) → ℂ) (k : K) :
    groupedCoefficient key (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) *
      mixedBulkSymmetrize n m slot (fun _ y _ _ => W y) 0 y 0 0) k =
    groupedCoefficient key (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * W y) k := by
  have h := selectedBulkAverage_statistic n m slot ν hν
    (fun y => if key y = k then 1 else 0) W (fun e y => by rw [hkey e y])
  simpa only [groupedCoefficient, mul_ite, mul_one, mul_zero, ite_mul, zero_mul] using h

end Ostmann

end OAI
