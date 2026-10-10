import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFaceUniqueness

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _
local instance : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

lemma attachedFaceTensorList_bounded (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (ks : List (Fin 4 × Fin 4)) :
    ∃ B : ℝ,0<B ∧ ∀ y,‖attachedFaceTensorList s a ks y‖≤B := by
  classical
  induction ks with
  | nil =>
    exact ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
      change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖≤_; linarith⟩
  | cons k ks ih =>
    obtain ⟨B,hB,h⟩ := ih
    obtain ⟨C,hC⟩ := (isCompact_sourceFlatPatch k.1 k.2).exists_bound_of_continuousOn
      (continuousOn_attachedPhysicalFlatTensor s ha k.1 k.2)
    refine ⟨max B C,lt_of_lt_of_le hB (le_max_left _ _),?_⟩
    intro y
    rw [attachedFaceTensorList_cons]
    by_cases hy : y∈sourceFlatPatch k.1 k.2
    · simp only [ite_eq_left hy,attachedPatchTensor]
      exact (hC y hy).trans (le_max_right _ _)
    · simp only [ite_eq_right hy]
      exact (h y).trans (le_max_left _ _)

lemma attachedCollarTensor_memLp_top (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) :
    MemLp (attachedCollarTensor s a) ∞ (volume : Measure (Fin 3 → ℝ)) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  obtain ⟨B,_,hB⟩ := attachedFaceTensorList_bounded s ha
    (Finset.univ : Finset (Fin 4 × Fin 4)).toList
  exact memLp_top_of_bound (attachedFaceTensorList_measurable s ha _).aestronglyMeasurable
    B (ae_of_all _ hB)

theorem attachedCollarTensor_poisson_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f g : spectralTraceGraph (torusRate s)) {a b : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox)
    (ht : 0<a*(x 0-b)) :
    let F := fun k : Fin 3 => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x) (Pi.single k 1)
    let G := fun k : Fin 3 => fderiv ℝ (fun y => (attachedEndPoissonField s g a b 0 y).re)
      (sourceCollarPiece i j x) (Pi.single k 1)
    |(sourceCollarJacobian i j x).det| *(F ⬝ᵥ
      (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥG))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        ((fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) ⬝ᵥ
          (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (endPoissonField s g k.succ
            (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re))) := by
  dsimp only
  simp_rw [attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht,
    attachedCartesianMatrix_poisson_derivative s hs g a b i j hx ht]
  simp only [dotProduct_single,mul_one,attachedCollarTensor_open s a i j hx]
  exact attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx) _ _

end ScalarConductivity

end

end OAI
