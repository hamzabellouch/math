import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnTotalEnergyNo
import OAI.Computability.VertexCover.Analysis.Poincare

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

theorem ownMean_poincare (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    variance (Φ.ownMean J frozen c0 A hA j i)
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) ≤
      2 * ∫ s, ∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
  apply VertexCover.Cube.poincare (Φ.ownMean_lipschitz J frozen c0 A hA j i)
    (Φ.ownGradient J frozen c0 A hA j i)
    (Φ.ownGradient_measurable J frozen c0 A hA j i)
  · intro s k
    exact VertexCover.Threshold.coordinate_bound (Φ.ownGradient_block_bound J frozen c0 A hA j i s) k
  · exact Φ.ownMean_partial_ae J frozen c0 A hA j i

noncomputable def ownTotalVariance (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : ℝ :=
  ∑ j : J, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    variance (Φ.ownMean J frozen c0 A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))))

theorem ownGradient_sq_integrable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    Integrable (fun s => ∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2)
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) := by
  apply integrable_finsetSum
  intro k hk
  apply Integrable.of_bound ((Φ.ownGradient_measurable J frozen c0 A hA j i k).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with s
  have hb := VertexCover.Threshold.coordinate_bound (Φ.ownGradient_block_bound J frozen c0 A hA j i s) k
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg (Φ.ownGradient J frozen c0 A hA j i s k),
    sq_abs (Φ.ownGradient J frozen c0 A hA j i s k)]

theorem ownTotalVariance_le_energy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalVariance J frozen c0 A hA ≤ 2 * Φ.ownTotalEnergy J frozen c0 A hA := by
  classical
  unfold ownTotalVariance ownTotalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [VertexCover.integral_finiteMean _ _ (fun hidden =>
    Φ.ownGradient_sq_integrable J frozen c0 A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))]
  calc
    _ ≤ VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      2 * ∫ s, ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))) :=
      VertexCover.finiteMean_mono (fun hidden => Φ.ownMean_poincare J frozen c0 A hA j _)
    _ = _ := by simp only [VertexCover.finiteMean, ← Finset.mul_sum]; ring

theorem ownTotalVariance_no_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalVariance J frozen c0 A hA < 7 := by
  have he := Φ.ownTotalVariance_le_energy J frozen c0 A hA
  have hu := Φ.ownTotalEnergy_no_upper m hm hval J hJ frozen c0 A hA
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
