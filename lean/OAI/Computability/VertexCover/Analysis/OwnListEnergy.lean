import Mathlib
import OAI.Computability.VertexCover.Reduction.GridBudget
import OAI.Computability.VertexCover.Analysis.OwnGradientMeasurable
import OAI.Computability.VertexCover.Analysis.ThresholdListEnergy

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

noncomputable def ownList (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ) :
    List i.LocalLabel :=
  i.thresholdList (β/2) (Φ.ownGradient J frozen c0 A hA j i s)

@[simp] theorem mem_ownList (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ)
    (a : i.LocalLabel) :
    a ∈ Φ.ownList J frozen c0 A hA j i s β ↔
      β/2 ≤ |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)| :=
  i.mem_thresholdList _ _ a

theorem ownList_membership_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (β : ℝ) (a : i.LocalLabel) :
    MeasurableSet {s | a ∈ Φ.ownList J frozen c0 A hA j i s β} := by
  simp only [mem_ownList]
  exact measurableSet_le measurable_const
    (Φ.ownGradient_measurable J frozen c0 A hA j i (i.slot a)).abs

theorem ownList_unsupported (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    {β : ℝ} (hβ : 0 < β) (hi : Φ.ownFiber J frozen j i = ∅) :
    Φ.ownList J frozen c0 A hA j i s β = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have h := (Φ.mem_ownList J frozen c0 A hA j i s β a).mp ha
  rw [Φ.ownGradient_unsupported J frozen c0 A hA j i hi s] at h
  simp only [Pi.zero_apply, abs_zero] at h
  linarith

theorem ownList_length (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (m : ℕ) (hm : 0 < m) :
    (Φ.ownList J frozen c0 A hA j i s (Parameters.β m)).length ≤ Parameters.ell m := by
  have h := i.thresholdList_card (Parameters.β m / 2) _
    (Φ.ownGradient_block_bound J frozen c0 A hA j i s)
  have hβ : 0 < Parameters.β m / 2 := by
    have := (Parameters.positive m hm).2.1
    positivity
  apply Nat.cast_le (α := ℝ) |>.mp
  change ((i.thresholdList _ _).length : ℝ) ≤ _
  rw [Parameters.ell_eq m hm]
  have hh := (le_div_iff₀ hβ).mpr h
  simpa only [div_div_eq_mul_div, one_mul] using hh

theorem ownList_energy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    {β : ℝ} (hβ : 0 < β) :
    (∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2) ≤ β/2 +
      ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)| := by
  classical
  exact i.thresholdList_energy (β/2) (by positivity) _
    (Φ.ownGradient_block_bound J frozen c0 A hA j i s)
    (fun k hk => Φ.ownGradient_unused J frozen c0 A hA j i s k hk)

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
