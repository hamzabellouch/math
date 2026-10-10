import Mathlib
import OAI.Computability.VertexCover.Analysis.StarEnergyBudget

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

theorem ae_cube {ι : Type*} [Fintype ι] :
    ∀ᵐ s ∂law ι, ∀ j, |s j| ≤ (1 : ℝ) := by
  rw [ae_all_iff]
  intro j
  exact (measurePreserving_eval (fun _ : ι => intervalLaw) j).quasiMeasurePreserving.ae ae_interval

end VertexCover.Cube

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def weightMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  ∫ x, Φ.separator A hA (Φ.continuousSum seed (Function.update s k x))
    ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))

theorem weightMean_measurable (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) : Measurable (Φ.weightMean A hA k seed) := by
  classical
  have hc : Continuous (fun p : (Fin d → Fin (Φ.WeightDimension d) → ℝ) ×
      (Fin (Φ.WeightDimension d) → ℝ) =>
      Φ.separator A hA (Φ.continuousSum seed (Function.update p.1 k p.2))) :=
    (Φ.separator_continuousSum_continuous A hA seed).comp
      (continuous_fst.update k continuous_snd)
  exact hc.stronglyMeasurable.integral_prod_right.measurable

theorem weight_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s| ≤ 2 := by
  classical
  have hi : Integrable (fun x => Φ.separator A hA (Φ.continuousSum seed (Function.update s k x)))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) :=
    VertexCover.Cube.integrable_continuous
      ((Φ.separator_continuousSum_continuous A hA seed).comp
        (continuous_const.update k continuous_id))
  have he : Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s =
      ∫ x, (Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.continuousSum seed (Function.update s k x)))
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
    rw [integral_sub (integrable_const _) hi]
    simp [weightMean]
  rw [he]
  have hb : ∀ᵐ x ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      ‖Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.continuousSum seed (Function.update s k x))‖ ≤ (2:ℝ) := by
    filter_upwards [VertexCover.Cube.ae_cube] with x hx
    have hu : Φ.InWeightCube (Function.update s k x) := by
      intro j c
      by_cases hj : j = k
      · subst j
        simpa using hx c
      · simpa only [Function.update_of_ne hj] using hs j c
    simpa only [Real.norm_eq_abs] using Φ.separator_weight_oscillation A hA seed s
      (Function.update s k x) hs hu k (fun j hj => (Function.update_of_ne hj _ _).symm)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

theorem weight_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 4 := by
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2 ≤ (4 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.weight_residual_abs_le A hA k seed s hs
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hh
    rw [sq_abs] at hsq
    nlinarith
  have hi : Integrable (fun s =>
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2)
      (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    apply Integrable.of_bound
      (((Φ.separator_continuousSum_continuous A hA seed).measurable.sub
        (Φ.weightMean_measurable A hA k seed)).pow_const 2).aestronglyMeasurable 4
    filter_upwards [hb] with s hs
    simpa only [Real.norm_eq_abs, Pi.sub_apply, abs_pow, sq_abs] using hs
  simpa using integral_mono_ae hi (integrable_const (4 : ℝ)) hb

theorem weight_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 4*d := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _k : Fin d, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (4 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.weight_residual_integral_le A hA k)
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
