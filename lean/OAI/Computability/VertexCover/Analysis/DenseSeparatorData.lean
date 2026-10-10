import Mathlib
import OAI.Computability.VertexCover.Analysis.IndependentSecondMomentLower
import OAI.Computability.VertexCover.Analysis.DenseHighFraction

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
namespace VertexCover.Parameters

theorem variance_scale (m : ℕ) (hm : 0 < m) :
    b₀ m * ((t m:ℝ)/2)^2 = ν m * (d m:ℝ) := by
  have hmR : (m:ℝ) ≠ 0 := by positivity
  simp only [b₀, t, ν, d, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end VertexCover.Parameters
namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem dense_separator_data (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    ∃ hV : (Φ.highVectors (Parameters.t m) A).Nonempty,
      (∀ seed : Φ.Seeds (Parameters.d m),
        (∫ s, Φ.separator (Φ.highVectors (Parameters.t m) A) hV (Φ.continuousSum seed s)
          ∂VertexCover.Cube.blockLaw (Fin (Parameters.d m))
            (Fin (Φ.WeightDimension (Parameters.d m)))) = 0) ∧
      Parameters.ν m * (Parameters.d m:ℝ) ≤
        VertexCover.finiteMean (fun seed : Φ.Seeds (Parameters.d m) =>
          variance (fun s => Φ.separator (Φ.highVectors (Parameters.t m) A) hV
            (Φ.continuousSum seed s))
            (VertexCover.Cube.blockLaw (Fin (Parameters.d m))
              (Fin (Φ.WeightDimension (Parameters.d m))))) := by
  classical
  have hfrac := Φ.dense_high_fraction m hm A hA hdense
  have hb0 : 0 < Parameters.b₀ m := by
    unfold Parameters.b₀
    have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hBN : (A.filter (fun v => (Parameters.t m:ℝ) <
      Φ.compatibilityNorm (Φ.sumVector v))).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : (A.filter (fun v => (Parameters.t m:ℝ) <
      Φ.compatibilityNorm (Φ.sumVector v))).card = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hfrac
    linarith
  have hV : (Φ.highVectors (Parameters.t m) A).Nonempty := hBN.image Φ.sumVector
  refine ⟨hV, fun seed => Φ.separator_continuousSum_mean_zero _ hV seed, ?_⟩
  have hround : (Parameters.d m:ℝ)/(2*Parameters.d m+1) < (Parameters.t m:ℝ)/2 := by
    have h := (Parameters.grid_budget m hm).1.trans (Parameters.grid_budget m hm).2.1
    simpa only [Parameters.p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h
  have hlow := Φ.independent_secondMoment_lower (Nat.cast_nonneg (Parameters.t m))
    hround A hA hV
  have hvareq : ∀ seed : Φ.Seeds (Parameters.d m),
      variance (fun s => Φ.separator (Φ.highVectors (Parameters.t m) A) hV
          (Φ.continuousSum seed s))
        (VertexCover.Cube.blockLaw (Fin (Parameters.d m))
          (Fin (Φ.WeightDimension (Parameters.d m)))) =
      ∫ s, (Φ.separator (Φ.highVectors (Parameters.t m) A) hV
          (Φ.continuousSum seed s))^2
        ∂VertexCover.Cube.blockLaw (Fin (Parameters.d m))
          (Fin (Φ.WeightDimension (Parameters.d m))) := by
    intro seed
    rw [variance_eq_integral
      (Φ.separator_continuousSum_continuous _ hV seed).measurable.aemeasurable,
      Φ.separator_continuousSum_mean_zero]
    simp only [sub_zero]
  simp_rw [hvareq]
  calc
    Parameters.ν m * (Parameters.d m:ℝ) =
        Parameters.b₀ m * ((Parameters.t m:ℝ)/2)^2 :=
      (Parameters.variance_scale m (by omega)).symm
    _ ≤ (((A.filter (fun v => (Parameters.t m:ℝ) <
        Φ.compatibilityNorm (Φ.sumVector v))).card:ℝ) /
          Fintype.card (Φ.Vertex (Parameters.d m))) * ((Parameters.t m:ℝ)/2)^2 :=
      mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
    _ = ((Parameters.t m:ℝ)/2)^2 *
        (A.filter (fun v => (Parameters.t m:ℝ) <
          Φ.compatibilityNorm (Φ.sumVector v))).card /
          Fintype.card (Φ.Vertex (Parameters.d m)) := by ring
    _ ≤ _ := hlow
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
