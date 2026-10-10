import Mathlib
import OAI.Computability.VertexCover.Analysis.IntegralUpdate

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
namespace VertexCover.Product

theorem update_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (k : ι) : LipschitzWith 1 (Function.update s k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro l
  by_cases hl : l = k
  · subst l; simp
  · simp [Function.update_of_ne hl, dist_nonneg]

theorem hasDerivAt_nested_update {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (other : ι → κ → ℝ) (j : ι)
    (s : κ → ℝ) (k : κ) :
    HasDerivAt (fun x => Function.update other j (Function.update s k x))
      (Pi.single j (Pi.single k 1)) (s k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Function.update_self, Pi.single_eq_same] using
      hasDerivAt_update s k (s k)
  · simpa only [Function.update_of_ne hl, Pi.single_eq_of_ne hl] using
      hasDerivAt_const (s k) (other l)

end VertexCover.Product

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem batchFunction_own_partial (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (other : Φ.BatchWeights J) (j : J) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d))
    (hd : DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))
    (hg : Φ.canonicalGradient seed J c0 A hA (Function.update other j s) =
      Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))) :
    HasDerivAt (fun x => Φ.batchFunction seed J c0 A hA
      (Function.update other j (Function.update s k x)))
      (Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (s k) := by
  classical
  have hD : HasFDerivAt (Φ.batchFunction seed J c0 A hA)
      (fderiv ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))
      (Function.update other j (Function.update s k (s k))) := by
    simpa only [Function.update_eq_self] using hd.hasFDerivAt
  rw [hg]
  exact hD.comp_hasDerivAt (s k) (VertexCover.Product.hasDerivAt_nested_update other j s k)

theorem ownIntegral_partial_ae (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (k : Fin (Φ.WeightDimension d)) :
    ∀ᵐ s ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      HasDerivAt (fun x => ∫ other, Φ.batchFunction seed J c0 A hA
        (Function.update other j (Function.update s k x)) ∂Φ.batchLaw J)
        (∫ other, Φ.canonicalGradient seed J c0 A hA
          (Function.update other j s) j k ∂Φ.batchLaw J) (s k) := by
  classical
  have hfull := Φ.canonicalGradient_ae_cube seed J c0 A hA
  have hae := VertexCover.Product.update_ae
    (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) j hfull
  filter_upwards [hae] with s hs
  have hi : ∀ x : ℝ, Integrable (fun other => Φ.batchFunction seed J c0 A hA
      (Function.update other j (Function.update s k x))) (Φ.batchLaw J) := by
    intro x
    exact VertexCover.Cube.integrable_continuous_block
      ((Φ.batchFunction_continuous _ J c0 A hA).comp
        (continuous_id.update j continuous_const))
  have hdiff : ∀ᵐ other ∂Φ.batchLaw J,
      HasDerivAt (fun x => Φ.batchFunction seed J c0 A hA
        (Function.update other j (Function.update s k x)))
        (Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (s k) := by
    filter_upwards [hs] with other ho
    exact Φ.batchFunction_own_partial seed J c0 A hA other j s k ho.1 ho.2
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := Set.univ) (bound := fun _ => (1 : ℝ)) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun x => (hi x).aestronglyMeasurable))
    (hi (s k))
    (Φ.canonicalGradient_update_measurable seed J c0 A hA j s k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun other => by
      have hl := (Φ.batchFunction_own_lipschitz seed J c0 A hA other j).comp
        (VertexCover.Product.update_lipschitz s k)
      simpa [Function.comp_def] using hl.lipschitzOnWith (s := Set.univ)))
    (integrable_const (1 : ℝ)) hdiff).2

theorem ownMean_partial_ae (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (k : Fin (Φ.WeightDimension d)) :
    ∀ᵐ s ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      HasDerivAt (fun x => Φ.ownMean J frozen c0 A hA j i (Function.update s k x))
        (Φ.ownGradient J frozen c0 A hA j i s k) (s k) := by
  classical
  have hall := (ae_all_iff.mpr (fun hidden : Φ.ownFiber J frozen j i =>
    Φ.ownIntegral_partial_ae (Φ.spliceSeeds J frozen hidden) J c0 A hA j k))
  filter_upwards [hall] with s hs
  simpa only [ownMean, ownGradient, VertexCover.finiteMean, Finset.sum_apply] using
    (HasDerivAt.sum (u := Finset.univ) (fun hidden _ => hs hidden)).div_const
      (Fintype.card (Φ.ownFiber J frozen j i) : ℝ)

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
