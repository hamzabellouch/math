import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsCells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem real_prime_product_pos {Q n : ℕ} (q : Fin n → PrimeUpTo Q) :
    0 < ((∏ a, ((q a).val : ℤ)) : ℝ) := by
  exact Finset.prod_pos (fun a _ => by exact_mod_cast (primeUpTo_prime (q a)).pos)

theorem log_int_prime_product {Q n : ℕ} (q : Fin n → PrimeUpTo Q) :
    Real.log (((∏ a, ((q a).val : ℤ)) : ℤ) : ℝ) =
      Real.log (characterTupleProduct q : ℝ) := by
  simp only [characterTupleProduct, Nat.cast_prod, Int.cast_prod, Int.cast_natCast]

theorem scheduled_pivot_atom_log_bounds {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : (schedule k j).Slot) (l : Fin k)
    (hi : (schedule k j).role i = .pivot l.val)
    (q : Fin (sourceWidth cfg m ((schedule k j).role i)) → PrimeUpTo Q)
    (hq : ∀ a, q a ∈ scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩) :
    ((cfg.2 l.castSucc).sum : ℝ) ≤ Real.log (characterTupleProduct q : ℝ) ∧
    Real.log (characterTupleProduct q : ℝ) ≤
      ((cfg.2 l.castSucc).sum : ℝ) + (cfg.2 l.castSucc).length := by
  have he : sourceWidth cfg m ((schedule k j).role i) = (cfg.2 l.castSucc).length := by
    rw [hi,sourceWidth_pivot]
  let e := finCongr he
  let q' := q ∘ e.symm
  have hq' : ∀ a, q' a ∈ boundedRawLogCell E ((cfg.2 l.castSucc).get a) := by
    intro a
    have hh := hq (e.symm a)
    rw [scheduledPrimeShells_pivot cfg m j bulk top E i l hi] at hh
    exact hh
  have hp : characterTupleProduct q' = characterTupleProduct q := by
    unfold characterTupleProduct
    exact e.symm.prod_comp (fun a => (q a).val)
  simpa only [hp] using log_tuple_of_cells (cfg.2 l.castSucc) E q' hq'

theorem scheduled_anchor_atom_log_bounds {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : (schedule k j).Slot) (l : Fin k) (big : Bool)
    (hi : (schedule k j).role i = .anchor l.val big)
    (q : Fin (sourceWidth cfg m ((schedule k j).role i)) → PrimeUpTo Q)
    (hq : ∀ a, q a ∈ scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩) :
    (cfg.1 (anchorCoordinate l big) : ℝ) ≤ Real.log (characterTupleProduct q : ℝ) ∧
    Real.log (characterTupleProduct q : ℝ) ≤ (cfg.1 (anchorCoordinate l big) : ℝ) + 1 := by
  have he : sourceWidth cfg m ((schedule k j).role i) = 1 := by
    rw [hi,sourceWidth_anchor]
  rw [log_characterTupleProduct]
  have hc (a : Fin (sourceWidth cfg m ((schedule k j).role i))) :
      (cfg.1 (anchorCoordinate l big) : ℝ) ≤ Real.log ((q a).val : ℝ) ∧
      Real.log ((q a).val : ℝ) < (cfg.1 (anchorCoordinate l big) : ℝ) + 1 := by
    have hh := hq a
    rw [scheduledPrimeShells_anchor cfg m j bulk top E i l big hi] at hh
    exact (Finset.mem_filter.mp hh).2
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hc a).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,he,nsmul_eq_mul,
      Nat.cast_one,one_mul] using hh
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hc a).2.le)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,he,nsmul_eq_mul,
      Nat.cast_one,one_mul] using hh

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
