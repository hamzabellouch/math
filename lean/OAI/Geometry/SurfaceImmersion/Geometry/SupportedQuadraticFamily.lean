import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Geometry.CombinedQuadraticExpansion

namespace OAI

/-! Actual supported targets for the doubled and mixed quadratic phases.
Mixed labels retain the intersection of the original amplitude supports. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

def quadraticCompacts {ι : Type*} (K : ι → Compacts Base) :
    RealModes.QuadraticLabel ι → Compacts Base
  | .inl i => K i
  | .inr ⟨i,j,_⟩ => K i ⊓ K j

lemma quadraticCompacts_coe {ι : Type*} (K : ι → Compacts Base)
    (l : RealModes.QuadraticLabel ι) :
    (quadraticCompacts K l : Set Base) = quadraticFamilySupport (fun i => (K i : Set Base)) l := by
  rcases l with i | ⟨i,j,b⟩ <;> rfl

lemma modeSupport_quadraticCompacts {ι : Type*} (K : ι → Compacts Base)
    (l : RealModes.QuadraticLabel ι) :
    (modeSupport (quadraticCompacts K l) : Set SmallModes.Base) =
      RealModes.quadraticSupport (fun i => (modeSupport (K i) : Set SmallModes.Base)) l := by
  rcases l with i | ⟨i,j,b⟩
  · rfl
  · exact Set.image_inter planeCoordinateIsometry.injective

lemma coordinateAmplitude_tsupport {K : Compacts Base}
    (H : SupportedField (F := Fin 4 → ℂ) K) :
    tsupport (coordinateAmplitude H) ⊆ (modeSupport K : Set SmallModes.Base) :=
  (pushSupported planeCoordinateIsometry K H).tsupport_subset

def metricQuadraticTarget {ι : Type*} {K : ι → Compacts Base}
    (φ : ι → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i)) (τ : ℝ)
    (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (quadraticCompacts K l)) := by
  have ht := RealModes.quadraticAmplitude_tsupport τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i)) (fun i => coordinateAmplitude_tsupport (H i)) l
  rw [← modeSupport_quadraticCompacts] at ht
  exact ContDiffMapSupportedIn.of_support_subset
    (RealModes.quadraticAmplitude_smooth
      (fun i => (hφ i).comp planeCoordinateIsometry.symm.contDiff)
      (fun i => (H i).contDiff.comp planeCoordinateIsometry.symm.contDiff) τ l)
    (subset_closure.trans ht)

lemma metricQuadraticTarget_apply {ι : Type*} {K : ι → Compacts Base}
    (φ : ι → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i)) (τ : ℝ)
    (l : RealModes.QuadraticLabel ι) (x : SmallModes.Base) :
    metricQuadraticTarget φ hφ H τ l x =
      RealModes.quadraticAmplitude τ (fun i => coordinatePhase (φ i))
        (fun i => coordinateAmplitude (H i)) l x := rfl

def combinedQuadraticTarget {n : ℕ} {ι : Type*} {K : ι → Compacts Base}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
    (hQ : Set.MapsTo (lowJet G) U O) (l : RealModes.QuadraticLabel ι)
    (hKU : (quadraticCompacts K l : Set Base) ⊆ U) (ε τ t : ℝ) :
    SupportedField (F := ComplexTensor) (modeSupport (quadraticCompacts K l)) :=
  metricQuadraticTarget φ hφ H τ l + pushSupported planeCoordinateIsometry (quadraticCompacts K l)
    (polynomialQuadraticTarget hU hO hP hG hφ (fun i => (H i).contDiff) hQ
      (fun i => (K i).isCompact.isClosed) (fun i => (H i).tsupport_subset)
      l (quadraticCompacts K l) hKU (quadraticCompacts_coe K l).symm.subset ε τ t)

lemma combinedQuadraticTarget_apply {n : ℕ} {ι : Type*} {K : ι → Compacts Base}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
    (hQ : Set.MapsTo (lowJet G) U O) (l : RealModes.QuadraticLabel ι)
    (hKU : (quadraticCompacts K l : Set Base) ⊆ U) (ε τ t : ℝ) (x : SmallModes.Base) :
    combinedQuadraticTarget hU hO P hP hG φ hφ H hQ l hKU ε τ t x =
      combinedQuadraticCoefficient P ε G φ (fun i => H i) τ t l x := rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
