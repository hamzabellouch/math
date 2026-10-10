import OAI.Analysis.Pureness.Operators.RowContractionNormalization

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_rowContraction_of_no_tracialState (h : ¬ Nonempty (TracialState A)) :
    ∃ (n : ℕ) (a : Fin n → A),
      (∑ i, star (a i) * a i) = 1 ∧ ‖∑ i, a i * star (a i)‖ < 1 := by
  obtain ⟨n, a, ha⟩ := exists_finite_selfCommutator_ge_half h
  obtain ⟨b, hb⟩ := normalize_selfCommutator_family a ha
  exact ⟨n + 1, b, hb⟩

theorem no_tracialState_of_rowContraction {n : ℕ} (a : Fin n → A)
    (hcol : (∑ i, star (a i) * a i) = 1) (hrow : ‖∑ i, a i * star (a i)‖ < 1) :
    ¬ Nonempty (TracialState A) := by
  rintro ⟨τ⟩
  have hval : τ.functional (∑ i, a i * star (a i)) = 1 := by
    calc
      _ = ∑ i, τ.functional (a i * star (a i)) := map_sum _ _ _
      _ = ∑ i, τ.functional (star (a i) * a i) :=
        Finset.sum_congr rfl (fun i _ => τ.tracial _ _)
      _ = τ.functional (∑ i, star (a i) * a i) := (map_sum _ _ _).symm
      _ = 1 := by rw [hcol, τ.normalized]
  have hh := τ.functional.norm_apply_le_of_nonneg (∑ i, a i * star (a i))
    (Finset.sum_nonneg (fun i _ => mul_star_self_nonneg (a i)))
  rw [hval, τ.normalized, norm_one, one_mul] at hh
  exact (not_lt_of_ge hh) hrow

theorem no_tracialState_iff_rowContraction :
    (¬ Nonempty (TracialState A)) ↔
      ∃ (n : ℕ) (a : Fin n → A),
        (∑ i, star (a i) * a i) = 1 ∧ ‖∑ i, a i * star (a i)‖ < 1 :=
  ⟨exists_rowContraction_of_no_tracialState, fun ⟨_, a, hc, hr⟩ =>
    no_tracialState_of_rowContraction a hc hr⟩
end CuntzPureness

end

end OAI
