import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnListEnergy
import OAI.Computability.VertexCover.Analysis.SelectedIntegralAbs

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

theorem canonicalGradient_update_integrable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) (k : Fin (Φ.WeightDimension d)) :
    Integrable (fun other : Φ.BatchWeights J =>
      Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (Φ.batchLaw J) := by
  apply Integrable.of_bound
    (Φ.canonicalGradient_update_measurable seed J c0 A hA j s k).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro other
  simpa only [Real.norm_eq_abs] using VertexCover.Threshold.coordinate_bound
    (Φ.canonicalGradient_block_bound seed J c0 A hA (Function.update other j s) j) k

theorem ownList_jensen (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ) :
    (∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
      |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)|) ≤
    VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
      ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J) := by
  classical
  exact VertexCover.Average.selected_integral_abs_le (Φ.batchLaw J)
    (Φ.ownList J frozen c0 A hA j i s β).toFinset
    (fun (hidden : Φ.ownFiber J frozen j i) other a =>
      Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j (i.slot a))
    (fun hidden a => Φ.canonicalGradient_update_integrable _ J c0 A hA j s (i.slot a))

theorem ownGradient_energy_le_averaged_mass (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    {β : ℝ} (hβ : 0 < β) :
    (∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
      ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J) := by
  exact (Φ.ownList_energy J frozen c0 A hA j i s hβ).trans
    (add_le_add le_rfl (Φ.ownList_jensen J frozen c0 A hA j i s β))

theorem ownFiber_tower (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (F : Φ.Query d → Φ.HiddenSeeds J → ℝ) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.finiteMean (fun hidden' : Φ.ownFiber J frozen j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) =>
          F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden')) =
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden) := by
  classical
  exact VertexCover.Average.finiteMean_fiber_tower_of_mem
    (fun hidden : Φ.HiddenSeeds J => Φ.query (Φ.spliceSeeds J frozen hidden) j) F
    (Φ.ownFiber J frozen j) (fun i hidden => Φ.mem_ownFiber J frozen j i hidden)

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
