import Mathlib
import OAI.Computability.VertexCover.Analysis.GraphCompleteness
import OAI.Computability.VertexCover.Analysis.BatchFunctionOwnLipschitz
import OAI.Computability.VertexCover.Analysis.SeparatorRoundingErrorAe

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
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory

theorem block_integral {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p : ℕ) (hp : 0 < p) (F : (ι → κ → Fin p) → ℝ) :
    (∫ s, F (fun j k => index p hp (s j k)) ∂VertexCover.Cube.blockLaw ι κ) =
      VertexCover.finiteMean F := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  have h := block_measurePreserving (ι := ι) (κ := κ) p hp
  have hm : AEStronglyMeasurable F (uniformOn (Set.univ : Set (ι → κ → Fin p))) :=
    (measurable_of_countable F).aestronglyMeasurable
  have he := integral_map h.aemeasurable (by simpa only [h.map_eq] using hm)
  rw [h.map_eq] at he
  rw [← he, integral_uniform_finite]
  rfl
end VertexCover.GridCoupling

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem independent_secondMoment_lower (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hround : (d:ℝ)/(2*d+1) < t/2)
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d)))
    (hV : (Φ.highVectors t A).Nonempty) :
    (t/2)^2 * (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).card /
        Fintype.card (Φ.Vertex d) ≤
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s))^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  let B := A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))
  let H : Φ.Vertex d → ℝ := fun v => if v ∈ B then (t/2)^2 else 0
  have hseed : ∀ seed : Φ.Seeds d,
      VertexCover.finiteMean (fun w => H (seed,w)) ≤
        ∫ s, (Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s))^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
    intro seed
    rw [← VertexCover.GridCoupling.block_integral (2*d+1) (by omega)
      (fun w => H (seed,w))]
    apply integral_mono_of_nonneg
    · apply Filter.Eventually.of_forall
      intro s
      dsimp [H]
      split_ifs <;> positivity
    · exact VertexCover.Cube.integrable_continuous_block
        ((Φ.separator_continuousSum_continuous (Φ.highVectors t A) hV seed).pow 2)
    · filter_upwards [Φ.separator_rounding_error_ae (Φ.highVectors t A) hV seed] with s hs
      change H (Φ.roundedVertex seed s) ≤ _
      dsimp only [H]
      split_ifs with hv
      · have hmem : Φ.sumVector (Φ.roundedVertex seed s) ∈ Φ.highVectors t A :=
          Finset.mem_image.mpr ⟨Φ.roundedVertex seed s, hv, rfl⟩
        have hpos := Φ.separator_pos_on (Φ.highVectors t A) hV
          (Φ.highVectors_separated t A hA) _ hmem
        have he := (abs_le.mp hs).1
        have hh : t/2 < Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s) := by
          linarith
        nlinarith
      · exact sq_nonneg _
  have h := VertexCover.finiteMean_mono hseed
  rw [← VertexCover.finiteMean_product H] at h
  have he : VertexCover.finiteMean H = (t/2)^2 * (B.card:ℝ) /
      Fintype.card (Φ.Vertex d) := by
    simp [VertexCover.finiteMean, H, Finset.sum_ite_mem, mul_comm]
  rwa [he] at h

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
