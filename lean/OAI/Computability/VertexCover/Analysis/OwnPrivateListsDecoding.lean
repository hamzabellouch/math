import Mathlib
import OAI.Computability.VertexCover.Reduction.DecodingUpperThreeHalves
import OAI.Computability.VertexCover.Analysis.OwnListEnergy

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def ownPrivateLists (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (β : ℝ) : Φ.PrivateLists d := by
  classical
  exact fun i => if hi : i.1 ∈ J then
    Φ.ownList J frozen c0 A hA ⟨i.1, hi⟩ i (s ⟨i.1, hi⟩) β else []

theorem ownPrivateLists_length (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (m : ℕ) (hm : 0 < m) (i : Φ.Query d) :
    (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m) i).length ≤ Parameters.ell m := by
  classical
  unfold ownPrivateLists
  split_ifs with hi
  · exact Φ.ownList_length J frozen c0 A hA ⟨i.1, hi⟩ i _ m hm
  · simp

theorem ownPrivateLists_membership_measurable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (i : Φ.Query d) (a : i.LocalLabel) :
    MeasurableSet {s | a ∈ Φ.ownPrivateLists J frozen c0 A hA s β i} := by
  classical
  unfold ownPrivateLists
  by_cases hi : i.1 ∈ J
  · simp only [dite_eq_left hi, mem_ownList]
    exact measurableSet_le measurable_const
      (((Φ.ownGradient_measurable J frozen c0 A hA ⟨i.1, hi⟩ i (i.slot a)).comp
        (measurable_pi_apply (⟨i.1, hi⟩ : J))).abs)
  · simp only [dite_eq_right hi, List.not_mem_nil, Set.ofPred_false]
    exact MeasurableSet.empty

theorem ownPrivateLists_decoding_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    (∫ s, finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J) < 3/2 := by
  classical
  let B : ℝ := 1 + ((Parameters.h m).choose 2 : ℝ) *
    (Parameters.ell m : ℝ)^2 * Parameters.σ m
  have hbound : ∀ s : Φ.BatchWeights J, finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)) ≤ B := by
    intro s
    have hh := Φ.decoding_upper_bound hval
      (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
      (Φ.ownPrivateLists_length J frozen c0 A hA s m (by omega)) J frozen
    simpa only [hJ] using hh
  have hint := integral_mono_of_nonneg (μ := Φ.batchLaw J)
    (f := fun s => finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)))
    (g := fun _ => B) (Filter.Eventually.of_forall (fun s => by
      unfold finiteMean
      exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (Nat.cast_nonneg _))) (integrable_const B) (Filter.Eventually.of_forall hbound)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hp := Parameters.pair_budget_lt m hm
  dsimp [B] at hint
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
