import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSeedBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSlowScales

namespace OAI

/-! The concrete starting family for the finite primitive iteration.
At amplitude z^(1/4), both its C2 displacement and its normalized mean
defect are bounded by fixed multiples of z^(1/2). -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates

lemma initial_amplitude_square {z : ℝ} (hz : 0 < z) :
    (z^(1/4 : ℝ))^2 = z^(1/2 : ℝ) := by
  rw [← Real.rpow_mul_natCast hz.le]
  norm_num

lemma initial_error_quotient {z : ℝ} (hz : 0 < z) :
    z/(z^(1/4 : ℝ))^2 = z^(1/2 : ℝ) := by
  rw [initial_amplitude_square hz]
  calc
    z / z^(1/2 : ℝ) = z^(1 : ℝ)/z^(1/2 : ℝ) := by rw [Real.rpow_one]
    _ = z^((1 : ℝ)-1/2) := (Real.rpow_sub hz _ _).symm
    _ = z^(1/2 : ℝ) := by norm_num

theorem primitive_initial_family {n : ℕ} {U : Set JetPolynomial.Base}
    (hU : IsOpen U) (K : Compacts JetPolynomial.Base) (hUK : U ⊆ K)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ B E : ℕ → ℝ, (∀ m, 1 ≤ B m) ∧ (∀ m, 1 ≤ E m) ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 →
      ContDiff ℝ ∞ (primitiveSeed (z^(1/4 : ℝ)) F) ∧
      WeightedBound U 1 2 (A*z^(1/2 : ℝ)) (primitiveSeed (z^(1/4 : ℝ)) F-F) ∧
      (∀ m, WeightedBound U 1 m (B m) (lowJet (primitiveSeed (z^(1/4 : ℝ)) F))) ∧
      (∀ m, WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) 1 m (E m*z^(1/2 : ℝ))
        (normalizedMeanDefect (z^(1/4 : ℝ))
          (RealModes.realMetricTensor (F ∘ planeCoordinateIsometry.symm))
          (coordinateMetricMap P z (primitiveSeed (z^(1/4 : ℝ)) F)))) := by
  obtain ⟨Q,hQ,A,B,hA,hB,hseed⟩ := compact_primitiveSeed_bounds hU K hUK hF
  choose E hE he using fun m => primitiveSeed_defect_bound hQ P hP m
    (B (m+tensorOrder P)) (hB (m+tensorOrder P))
  refine ⟨A 2,hA 2,B,(fun m => 1+E m),hB,?_,?_⟩
  · intro m
    exact le_add_of_nonneg_right (hE m)
  · intro z hz hz1
    have hδ : 0 < z^(1/4 : ℝ) := Real.rpow_pos_of_pos hz _
    have hδ1 : (z^(1/4 : ℝ))^2 ≤ 1 := by
      rw [initial_amplitude_square hz]
      exact Real.rpow_le_one hz.le hz1 (by norm_num)
    obtain ⟨hGQ,hGb,_,hclose⟩ := hseed (z^(1/4 : ℝ)) hδ1
    refine ⟨primitiveSeed_smooth _ hF,?_,hGb,?_⟩
    · simpa only [initial_amplitude_square hz] using hclose 2
    · intro m
      have hb := he m U hU hF (z^(1/4 : ℝ)) z hδ.ne' hδ1 hz.le hz1 hGQ
        (hGb (m+tensorOrder P))
      apply hb.mono_const
      calc
        E m*z/(z^(1/4 : ℝ))^2 = E m*(z/(z^(1/4 : ℝ))^2) := by ring
        _ = E m*z^(1/2 : ℝ) := by rw [initial_error_quotient hz]
        _ ≤ (1+E m)*z^(1/2 : ℝ) := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) (Real.rpow_pos_of_pos hz _).le

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
