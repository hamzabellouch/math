import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexIndependence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame

namespace OAI

/-! # Fourteen physical directions fill any containing contour of dimension at most fourteen -/

namespace DefocusingNLS

theorem profileSymmetryParameters_finrank : Module.finrank ℝ ProfileSymmetryParameters = 14 := by
  simp only [ProfileSymmetryParameters, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin]

theorem homogeneous_physical_frame_spans (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (F : ProfileSymmetryParameters →L[ℝ] HomogeneousY a k) (hF : Function.Injective F)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    [FiniteDimensional ℂ P.range]
    (hfix : ∀ p, P (homogeneousComplexEmbed a k ha ha1 hk (F p)) =
      homogeneousComplexEmbed a k ha ha1 hk (F p))
    (hdim : Module.finrank ℂ P.range ≤ 14) :
    Submodule.span ℂ (Set.range (fun p => homogeneousComplexEmbed a k ha ha1 hk (F p))) = P.range := by
  classical
  let ι := homogeneousComplexEmbed a k ha ha1 hk
  let W := Submodule.span ℂ (Set.range (fun p => ι (F p)))
  have hWP : W ≤ P.range := by
    apply Submodule.span_le.mpr
    rintro w ⟨p, rfl⟩
    exact ⟨ι (F p), hfix p⟩
  let : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWP
  let b := Module.finBasis ℝ ProfileSymmetryParameters
  have hli : LinearIndependent ℝ (fun j => F (b j)) :=
    b.linearIndependent.map' F.toLinearMap (LinearMap.ker_eq_bot.mpr hF)
  have hcli := homogeneousComplexEmbed_linearIndependent a k ha ha1 hk _ hli
  let v := fun j => (⟨ι (F (b j)), Submodule.subset_span ⟨b j, rfl⟩⟩ : W)
  have hv : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp W.subtype
    exact hcli
  have hlo : 14 ≤ Module.finrank ℂ W := by
    simpa only [Fintype.card_fin, profileSymmetryParameters_finrank] using hv.fintype_card_le_finrank
  have hhi := Submodule.finrank_mono hWP
  change W = P.range
  exact Submodule.eq_of_le_of_finrank_eq hWP (by omega)

end DefocusingNLS

end OAI
