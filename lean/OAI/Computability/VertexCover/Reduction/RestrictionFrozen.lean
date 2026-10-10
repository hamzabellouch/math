import Mathlib
import OAI.Computability.VertexCover.Reduction.PrivateTotalEnergyLaw
import OAI.Computability.VertexCover.Reduction.PrivateProjectionBatchLower

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
open MeasureTheory ProbabilityTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem restrictionFunction_energy_variance (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        variance (fun s => Φ.separator A hA (Φ.continuousSum seed s))
          (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) := by
  rw [restrictionForm_energy]
  apply congrArg VertexCover.finiteMean
  funext seed
  rw [variance_eq_integral
    (Φ.separator_continuousSum_continuous A hA seed).measurable.aemeasurable,
    Φ.separator_continuousSum_mean_zero]
  simp only [sub_zero, restrictionFunction_apply]
  exact CompactCube.integral_realWeights
    ((Φ.separator_continuousSum_continuous A hA seed).pow 2).measurable.aestronglyMeasurable

theorem restriction_frozen_exists (Φ : LabelCover) {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (hhd : h ≤ d) (ν : ℝ) (hν : 0 < ν)
    (hscale : 16*(h:ℝ)+32*(h:ℝ)^2 ≤ ν*d/2)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (henergy : ν*d ≤ (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA)) :
    ∃ J : Finset (Fin d), J.card = h ∧ ∃ frozen : Φ.Seeds d,
      ∃ s : Φ.RestrictionWeights d,
        ν*h/4 ≤ Φ.ownTotalVariance J frozen
          (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA := by
  classical
  have : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  by_contra hno
  push Not at hno
  have hbound (J : Finset (Fin d)) (hJ : J ∈ batches d h) :
      (∑ j ∈ J, (Φ.restrictionForm d).energy
        (Φ.privateProjection J j (Φ.restrictionFunction A hA))) ≤ ν*h/4 := by
    rw [← Finset.sum_coe_sort J, Φ.privateTotal_energy_law J A hA]
    calc
      _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => ν*h/4) := by
        apply VertexCover.finiteMean_mono
        intro frozen
        have hb := integral_mono (Φ.ownTotalVariance_frozen_integrable J frozen A hA)
          (integrable_const (ν*h/4))
          (fun s => (hno J (mem_batches.mp hJ) frozen s).le)
        simpa using hb
      _ = _ := VertexCover.finiteMean_const _
  have hsum := Finset.sum_le_sum hbound
  have hl := Φ.privateProjection_batch_lower hd hh ν hscale A hA henergy
  simp only [Finset.sum_const, nsmul_eq_mul, card_batches] at hsum
  have hpos : 0 < (d.choose h:ℝ)*ν*h :=
    mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hhd)) hν)
      (Nat.cast_pos.mpr (by omega))
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
