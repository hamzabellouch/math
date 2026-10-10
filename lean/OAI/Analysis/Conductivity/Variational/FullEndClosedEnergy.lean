import Mathlib
import OAI.Analysis.Conductivity.Variational.FullWeakEndEnergy

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

lemma fullAttachedEnd_vector_integral_open (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    {a b l r : ℝ} (ha : a≠0) (i j : Fin 4)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      fullAttachedEndGradient s f a b κ y ⬝ᵥ (attachedCollarTensor s a y*ᵥG y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
            (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥG (sourceCollarPiece i j x)))) := by
  rw [sourceExtended_integral i j hl hr]
  apply integral_congr_ae
  filter_upwards [sourceExtendedBox_open_ae hl hr,
    sourceExtendedBox_axial_strict_ae l r] with x hx hm
  simp only [smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact fullAttachedEnd_vector_energy s hs f κ _ ha i j hx (ht (x 0) hm)

end ScalarConductivity

end

end OAI
