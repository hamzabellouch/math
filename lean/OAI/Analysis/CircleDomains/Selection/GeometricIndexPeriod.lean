import OAI.Analysis.CircleDomains.Topology.HalfPlanePathSides
import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex

namespace OAI

/-! Deck translation adds the corresponding integer to the actual ray
index and hence to its expectation. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem translatedHalfPlaneRay_curve_add (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k n : ℤ) (t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ (k + n)).curve t =
      (translatedHalfPlaneRay γ hγ k).curve t + (n : ℂ) := by
  change diskRayComplex γ hγ.1 hγ.2.2.1 t + ((k + n : ℤ) : ℂ) =
    (diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)) + (n : ℂ)
  rw [Int.cast_add, add_assoc]

 theorem rayRightIndices_translate_iff (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (k n : ℤ) :
    k + n ∈ rayRightIndices hsch γ hγ (z + (n : ℂ)) ↔ k ∈ rayRightIndices hsch γ hγ z := by
  constructor
  · intro hm
    have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ (k + n)) (translatedHalfPlaneRay γ hγ k)
      (rayJordan_spec hsch γ hγ (k + n)) (rayJordan_spec hsch γ hγ k)
      (-(n : ℝ)) (fun t => by
        rw [translatedHalfPlaneRay_curve_add]
        push_cast
        simp only [add_neg_cancel_right]) hza hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_neg, Complex.ofReal_intCast,
      add_neg_cancel_right] using hh
  · intro hm
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ k) (translatedHalfPlaneRay γ hγ (k + n))
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ (k + n))
      (n : ℝ) (fun t => by simpa only [Complex.ofReal_intCast] using
        translatedHalfPlaneRay_curve_add γ hγ k n t) hz hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_intCast] using hh

 theorem geometricRayIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (n : ℤ) :
    geometricRayIndex hsch γ hγ (z + (n : ℂ)) = geometricRayIndex hsch γ hγ z + n := by
  have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
  have h0 := geometricRayIndex_isGreatest hsch γ hγ z hz
  have h1 := geometricRayIndex_isGreatest hsch γ hγ (z + (n : ℂ)) hza
  apply le_antisymm
  · have hm : geometricRayIndex hsch γ hγ (z + (n : ℂ)) - n ∈ rayRightIndices hsch γ hγ z := by
      apply (rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mp
      simpa only [sub_add_cancel] using h1.1
    have hb := h0.2 hm
    omega
  · exact h1.2 ((rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mpr h0.1)

 def ClosedUpperHalfPlane.translate (z : ClosedUpperHalfPlane) (n : ℤ) : ClosedUpperHalfPlane :=
  ⟨z.val + (n : ℂ), by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using z.property⟩

 theorem meanGeometricIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (n : ℤ) :
    meanGeometricIndex hsch K hKS η (z.translate n) = meanGeometricIndex hsch K hKS η z + (n : ℝ) := by
  have hi := integrable_geometricRayIndex hsch hsep K hK hKS η z
  simp only [meanGeometricIndex, ClosedUpperHalfPlane.translate,
    geometricRayIndex_translate hsch hsep _ _ _ z.property, Int.cast_add,
    integral_add hi (integrable_const (n : ℝ)), integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]

end CircleDomainRigidity

end

end OAI
