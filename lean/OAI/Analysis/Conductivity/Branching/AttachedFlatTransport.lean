import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalFlatTransport
import OAI.Analysis.Conductivity.Flux.AttachedFlatTensor

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedPhysicalFlatTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  attachedFlatTensor s a i j (sourceCollarInverse i j y)

def attachedPhysicalFlatGradient (a : ℝ) (i j : Fin 4)
    (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  attachedCartesianMatrix a i j (sourceCollarInverse i j y)*ᵥ
    v (sourceCollarInverse i j y)

theorem attachedPhysicalFlat_energy_integral (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (v w : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      attachedPhysicalFlatGradient a i j v y ⬝ᵥ
        (attachedPhysicalFlatTensor s a i j y*ᵥattachedPhysicalFlatGradient a i j w y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v x ⬝ᵥ (flatCylinderMatrix s*ᵥw x)) := by
  rw [sourceExtended_integral i j hl hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hx' : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100) := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  simp only [attachedPhysicalFlatGradient,attachedPhysicalFlatTensor,
    sourceCollarInverse_extended i j hl hr hx,smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact attachedFlatTensor_energy_density s ha i j hx' (v x) (w x)

lemma attachedPhysicalFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) :
    (attachedPhysicalFlatTensor s a i j y)ᵀ=attachedPhysicalFlatTensor s a i j y :=
  attachedFlatTensor_symmetric s a i j _

theorem attachedPhysicalFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ c C : ℝ,0<c ∧ c<C ∧
      ∀ y∈sourceCollarPiece i j '' sourceExtendedBox (-(1:ℝ)/100) (1/100),
        ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (attachedPhysicalFlatTensor s a i j y*ᵥv) ∧
          v ⬝ᵥ (attachedPhysicalFlatTensor s a i j y*ᵥv)≤C*‖v‖^2 := by
  obtain ⟨c,C,hc,hcC,h⟩ := attachedFlatTensor_elliptic s hs ha i j
  refine ⟨c,C,hc,hcC,?_⟩
  rintro _ ⟨x,hx,rfl⟩ v
  simpa only [attachedPhysicalFlatTensor,
    sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx] using h x hx v

lemma attachedPhysicalFlatGradient_poisson (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      attachedPhysicalFlatGradient a i j
        (fun x k => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)
        (sourceCollarPiece i j x) ⬝ᵥ v := by
  simp only [attachedPhysicalFlatGradient,sourceCollarInverse_point i j hx]
  exact attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht v

end ScalarConductivity

end

end OAI
