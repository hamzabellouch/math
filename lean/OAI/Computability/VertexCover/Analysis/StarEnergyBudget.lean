import Mathlib
import OAI.Computability.VertexCover.Analysis.BatchFunctionOwnLipschitz
import OAI.Computability.VertexCover.Analysis.StarMeanContinuous

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
namespace VertexCover.Cube
open MeasureTheory
open scoped ENNReal

theorem ae_interval : ∀ᵐ x ∂intervalLaw, |x| ≤ (1 : ℝ) := by
  have h : ∀ᵐ x ∂intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)).mpr
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [h] with x hx
  exact abs_le.mpr hx

theorem ae_block_cube {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ∀ᵐ s ∂blockLaw ι κ, ∀ j k, |s j k| ≤ (1 : ℝ) := by
  classical
  rw [ae_all_iff]
  intro j
  have hinner : ∀ᵐ v ∂law κ, ∀ k, |v k| ≤ (1 : ℝ) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_eval (fun _ : κ => intervalLaw) k).quasiMeasurePreserving.ae ae_interval
  exact (measurePreserving_eval (fun _ : ι => law κ) j).quasiMeasurePreserving.ae hinner

end VertexCover.Cube

namespace VertexCover.LabelCover
open MeasureTheory

theorem star_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 4 := by
  have hi := VertexCover.Cube.integrable_continuous_block
    (((Φ.separator_continuousSum_continuous A hA seed).sub
      (Φ.starMean_continuous A hA k seed)).pow 2)
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2 ≤ (4 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.star_residual_abs_le A hA k seed s hs
    have hsq := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2) |>.mpr hh
    rw [sq_abs] at hsq
    norm_num only [OfNat.ofNat, pow_two, Nat.reduceMul] at hsq ⊢
    nlinarith
  simpa using integral_mono_ae hi (integrable_const (4 : ℝ)) hb

theorem star_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 4*d := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _k : Fin d, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (4 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.star_residual_integral_le A hA k)
        _ = 4 := VertexCover.finiteMean_const _
    _ = 4*d := by simp [mul_comm]

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
