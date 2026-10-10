import Mathlib
import OAI.Computability.VertexCover.Analysis.StarEnergyBudget
import OAI.Computability.VertexCover.Analysis.FiniteMeanConditionBest

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

noncomputable instance starKeyFintype (Φ : LabelCover) (d : ℕ) : Fintype (Φ.StarKey d) := by
  unfold StarKey
  infer_instance

theorem starMean_eq_fiberAverage (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.starMean A hA k seed s =
      VertexCover.Average.fiberAverage (Φ.starKey k)
        (fun _ seed' => Φ.separator A hA (Φ.continuousSum seed' s)) (Φ.starKey k seed) := by
  classical
  calc
    _ = (∑ seed' ∈ Φ.starFiber k seed,
        Φ.separator A hA (Φ.continuousSum seed' s)) / (Φ.starFiber k seed).card :=
      VertexCover.Average.finiteMean_finset (Φ.starFiber k seed)
        (fun seed' => Φ.separator A hA (Φ.continuousSum seed' s))
    _ = _ := rfl

theorem star_residual_orthogonal (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (g : Φ.StarKey d → ℝ) :
    VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s) *
        g (Φ.starKey k seed)) = 0 := by
  simp_rw [Φ.starMean_eq_fiberAverage]
  exact VertexCover.Average.finiteMean_condition_orthogonal _ _ _

theorem star_residual_le_retained (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (g : Φ.StarKey d → ℝ) :
    VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2) ≤
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        (Φ.separator A hA (Φ.continuousSum seed s) - g (Φ.starKey k seed))^2) := by
  simp_rw [Φ.starMean_eq_fiberAverage]
  exact VertexCover.Average.finiteMean_condition_best _ _ _

end VertexCover.LabelCover

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def seedMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  VertexCover.finiteMean (fun c : Fin Φ.M =>
    Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s))

theorem seed_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s| ≤ 4 := by
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have he : Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s =
      VertexCover.finiteMean (fun c : Fin Φ.M =>
        Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s)) := by
    rw [VertexCover.finiteMean_sub, VertexCover.finiteMean_const]
    rfl
  rw [he]
  apply (VertexCover.finiteMean_abs_le _).trans
  calc
    _ ≤ VertexCover.finiteMean (fun _ : Fin Φ.M => (4 : ℝ)) :=
      VertexCover.finiteMean_mono (Φ.separator_seed_oscillation A hA seed s hs e)
    _ = 4 := VertexCover.finiteMean_const _

theorem seedMean_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) : Continuous (Φ.seedMean A hA e seed) := by
  classical
  unfold seedMean VertexCover.finiteMean
  exact (continuous_finsetSum _ (fun c _ =>
    Φ.separator_continuousSum_continuous A hA (Φ.replaceSeed seed e c))).div_const _

theorem seed_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 16 := by
  have hi := VertexCover.Cube.integrable_continuous_block
    (((Φ.separator_continuousSum_continuous A hA seed).sub
      (Φ.seedMean_continuous A hA e seed)).pow 2)
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2 ≤ (16 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.seed_residual_abs_le A hA e seed s hs
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)).mpr hh
    rw [sq_abs] at hsq
    nlinarith
  simpa using integral_mono_ae hi (integrable_const (16 : ℝ)) hb

theorem seed_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ e : PositionPair d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 8*(d:ℝ)^2 := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _e : PositionPair d, (16 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (16 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.seed_residual_integral_le A hA e)
        _ = 16 := VertexCover.finiteMean_const _
    _ ≤ 8*(d:ℝ)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, positionPair_card]
      rw [Nat.cast_choose_two]
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

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
