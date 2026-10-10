import Mathlib
import OAI.Computability.VertexCover.Analysis.CanonicalGradientValid

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

theorem canonicalGradient_measurable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Measurable (Φ.canonicalGradient seed J c0 A hA) := by
  classical
  apply Measurable.ite (VertexCover.AffineSelector.regular_measurableSet _ _)
  · apply Measurable.of_eval; intro batchIndex
    apply Measurable.of_eval; intro weightIndex
    exact (ContinuousLinearMap.apply ℝ ℝ
      (Pi.single batchIndex (Pi.single weightIndex 1))).measurable.comp
      (measurable_fderiv ℝ (Φ.batchFunction seed J c0 A hA))
  · exact measurable_const

theorem canonicalGradient_ae_derivative (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (μ : Measure (Φ.BatchWeights J)) [μ.IsAddHaarMeasure] :
    ∀ᵐ s ∂μ, DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) s ∧
      Φ.canonicalGradient seed J c0 A hA s =
        Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) := by
  classical
  filter_upwards [VertexCover.AffineSelector.ae_regular μ (Φ.affineSlope seed J)
    (Φ.affineOffset c0 (A := A))] with s hs
  obtain ⟨im, ip, hder⟩ := Φ.batchFunction_hasFDerivAt seed J c0 A hA s hs
  exact ⟨hder.differentiableAt, by simp [canonicalGradient, hs]⟩

theorem canonicalGradient_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) (j : J) :
    ∑ k, |Φ.canonicalGradient seed J c0 A hA s j k| ≤ 1 := by
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  simp_rw [heq]
  exact Φ.hull_block_bound seed hG j

theorem canonicalGradient_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (j : J) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    Φ.canonicalGradient seed J c0 A hA s j k = 0 := by
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  rw [heq]
  exact Φ.hull_unused seed hG j k hk

theorem canonicalGradient_listMass (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (L : Φ.PrivateLists d) :
    (∑ j : J, ∑ a ∈ (L (Φ.query seed j)).toFinset,
      |Φ.canonicalGradient seed J c0 A hA s j ((Φ.query seed j).slot a)|) ≤
        Φ.listHitMaximum L seed J := by
  classical
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  simp_rw [heq]
  exact (Finset.sum_coe_sort J (fun j =>
    ∑ a ∈ (L (Φ.query seed j)).toFinset, |G j ((Φ.query seed j).slot a)|)).trans_le
      (Φ.listMass_le_hitMaximum L seed J hG)

theorem canonicalGradient_query_invariant (Φ : LabelCover) {d : ℕ}
    (seed seed' : Φ.Seeds d) (J : Finset (Fin d))
    (hq : ∀ j : J, Φ.query seed j = Φ.query seed' j)
    (c0 : Φ.Coordinate d → ℝ) (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Φ.canonicalGradient seed J c0 A hA = Φ.canonicalGradient seed' J c0 A hA := by
  have hS : Φ.batchSum seed J = Φ.batchSum seed' J := by
    funext s
    unfold batchSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [hq j]
  have hC : Φ.batchSumCLM seed J = Φ.batchSumCLM seed' J := by
    ext s p
    exact congrFun (congrFun hS s) p
  have hA' : (Φ.affineSlope seed J (A := A)) = Φ.affineSlope seed' J := by
    funext i
    simp only [affineSlope, hC]
  have hf : Φ.batchFunction seed J c0 A hA = Φ.batchFunction seed' J c0 A hA := by
    funext s
    simp only [batchFunction, hS]
  funext s
  unfold canonicalGradient
  have hr : VertexCover.AffineSelector.Regular (Φ.affineSlope seed J)
      (Φ.affineOffset c0 (A := A)) s ↔
      VertexCover.AffineSelector.Regular (Φ.affineSlope seed' J)
      (Φ.affineOffset c0 (A := A)) s := by rw [hA']
  simp only [hf]
  split_ifs <;> first | rfl | (exfalso; tauto)

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
