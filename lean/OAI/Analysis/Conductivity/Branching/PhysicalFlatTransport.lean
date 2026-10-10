import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFlatEllipticity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceCollarInverse_extended (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox l r) :
    sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact sourceCollarInverse_left_pos i j
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
      (sourceCollarRadius_extended j ⟨hl.trans ht.1,ht.2.trans hr⟩ hb).1)
    (by linarith [ht.2]) ha hb

def sourcePhysicalFlatTensor (s : Fin 3 → ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  sourceFlatTensor s i j (sourceCollarInverse i j y)

def sourcePhysicalFlatGradient (i j : Fin 4) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  sourceCartesianGradientMatrix i j (sourceCollarInverse i j y)*ᵥ
    v (sourceCollarInverse i j y)

theorem sourcePhysicalFlat_energy_integral (s : Fin 3 → ℝ) (i j : Fin 4)
    {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (v w : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      sourcePhysicalFlatGradient i j v y ⬝ᵥ
        (sourcePhysicalFlatTensor s i j y*ᵥsourcePhysicalFlatGradient i j w y))=
      ∫ x in sourceExtendedBox l r,
        angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v x ⬝ᵥ (flatCylinderMatrix s*ᵥw x)) := by
  rw [sourceExtended_integral i j hl hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hx' : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100) := by
    obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩
  simp only [sourcePhysicalFlatGradient,sourcePhysicalFlatTensor,
    sourceCollarInverse_extended i j hl hr hx,smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact sourceFlatTensor_energy_density s i j hx' (v x) (w x)

lemma sourcePhysicalFlatTensor_symmetric (s : Fin 3 → ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) :
    (sourcePhysicalFlatTensor s i j y)ᵀ=sourcePhysicalFlatTensor s i j y :=
  sourceFlatTensor_symmetric s i j _

theorem sourcePhysicalFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i j : Fin 4) :
    ∃ c C : ℝ,0<c ∧ c<C ∧
      ∀ y∈sourceCollarPiece i j '' sourceExtendedBox (-(1:ℝ)/100) (1/100),
        ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (sourcePhysicalFlatTensor s i j y*ᵥv) ∧
          v ⬝ᵥ (sourcePhysicalFlatTensor s i j y*ᵥv)≤C*‖v‖^2 := by
  obtain ⟨c,C,hc,hcC,h⟩ := sourceFlatTensor_elliptic s hs i j
  refine ⟨c,C,hc,hcC,?_⟩
  rintro _ ⟨x,hx,rfl⟩ v
  simpa only [sourcePhysicalFlatTensor,sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx]
    using h x hx v

lemma sourcePhysicalFlatGradient_poisson (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<x 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (physicalEndPoissonField s f 0 y).re) (sourceCollarPiece i j x) v=
      sourcePhysicalFlatGradient i j
        (fun x k => (endPoissonField s f k.succ
          (x 0,torusAngles (sourceFaceAngles i j x))).re) (sourceCollarPiece i j x) ⬝ᵥ v := by
  simp only [sourcePhysicalFlatGradient,sourceCollarInverse_point i j hx]
  exact physicalEndPoisson_real_fderiv s hs f i j hx ht v

end ScalarConductivity

end

end OAI
