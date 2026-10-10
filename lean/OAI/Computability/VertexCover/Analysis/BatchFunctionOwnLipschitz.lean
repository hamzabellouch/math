import Mathlib
import OAI.Computability.VertexCover.Reduction.SeparatorContinuousSumOdd
import OAI.Computability.VertexCover.Analysis.CanonicalGradientInvariant
import OAI.Computability.VertexCover.Analysis.BlockLawAc

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
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem integrable_continuous {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (law ι) := by
  rw [law_eq_restrict_volume]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).smul_measure (by finiteness)

theorem integrable_continuous_block {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → κ → ℝ) → ℝ} (hf : Continuous f) : Integrable f (blockLaw ι κ) := by
  rw [blockLaw_eq_restrict_volume]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc)))).smul_measure
      (by finiteness)

end VertexCover.Cube

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def batchLaw (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :
    Measure (Φ.BatchWeights J) := VertexCover.Cube.blockLaw J (Fin (Φ.WeightDimension d))

instance batchLaw_probability (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :
    IsProbabilityMeasure (Φ.batchLaw J) := by
  unfold batchLaw
  infer_instance

theorem canonicalGradient_ae_cube (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    ∀ᵐ s ∂Φ.batchLaw J, DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) s ∧
      Φ.canonicalGradient seed J c0 A hA s =
        Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) := by
  let : (volume : Measure (Φ.BatchWeights J)).IsAddHaarMeasure := by
    change (Measure.pi (fun _ : J => (volume : Measure (Fin (Φ.WeightDimension d) → ℝ)))).IsAddHaarMeasure
    apply Measure.pi.isAddHaarMeasure
  exact (VertexCover.Cube.blockLaw_ac J (Fin (Φ.WeightDimension d))).ae_le
    (Φ.canonicalGradient_ae_derivative seed J c0 A hA volume)

theorem batchFunction_integrable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Integrable (Φ.batchFunction seed J c0 A hA) (Φ.batchLaw J) :=
  VertexCover.Cube.integrable_continuous_block (Φ.batchFunction_continuous seed J c0 A hA)

theorem batchSum_update_sub (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) (j : J)
    (u v : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.batchSum seed J (Function.update s j u) -
      Φ.batchSum seed J (Function.update s j v) = Φ.increment (Φ.query seed j) (u-v) := by
  classical
  simp only [batchSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp only [Function.update_self, ← Φ.increment_sub]
  · intro k _ hkj
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj, sub_self]
  · simp

theorem batchFunction_own_lipschitz (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (j : J) :
    LipschitzWith 1 (fun u => Φ.batchFunction seed J c0 A hA (Function.update s j u)) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (Φ.separator_lipschitz A hA _ _).trans
  rw [add_sub_add_left_eq_sub, Φ.batchSum_update_sub]
  apply Φ.increment_norm_le _ _ (_root_.norm_nonneg _)
  intro k
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (u-v) k

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
