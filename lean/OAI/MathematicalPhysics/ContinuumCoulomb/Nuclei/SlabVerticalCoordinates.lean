import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabPlanarTail
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabSections

namespace OAI

/-! Vertical-first coordinates for the actual three-dimensional slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def slabVerticalEquiv : Position ≃ᵐ ℝ × PlanarPosition :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem slabVerticalEquiv_symm_apply (p : ℝ × PlanarPosition) :
    slabVerticalEquiv.symm p = WithLp.toLp 2 ![p.2 0, p.2 1, p.1] := by
  ext i
  fin_cases i <;> rfl

theorem slabVerticalEquiv_apply (x : Position) :
    slabVerticalEquiv x = (x 2, WithLp.toLp 2 ![x 0, x 1]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem slabVerticalEquiv_measurePreserving : MeasurePreserving slabVerticalEquiv :=
  ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem slabVerticalEquiv_preimage (H S : ℝ) :
    slabVerticalEquiv ⁻¹' (Set.Icc (-S) S ×ˢ slabPlanarBox H) = slabDomain H S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, slabVerticalEquiv_apply,
    slabPlanarBox, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, slabDomain, abs_le]
  tauto

theorem slabVertical_setIntegral (H S : ℝ) (f : Position → ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ p in Set.Icc (-S) S ×ˢ slabPlanarBox H, f (slabVerticalEquiv.symm p) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    h.integral_comp' (f ∘ slabVerticalEquiv.symm)

def slabAxisPoint (z : ℝ) : Position := WithLp.toLp 2 ![0,0,z]

theorem regularizedSlab_vertical_kernel (epsilon z : ℝ) (p : ℝ × PlanarPosition) :
    NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-slabVerticalEquiv.symm p) =
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖ := by
  rw [regularizedKernel_eq_sqrt, slabVerticalEquiv_symm_apply]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [slabAxisPoint, PiLp.sub_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    zero_sub, neg_sq]
  rw [Fin.succ_zero_eq_one]
  ring

theorem regularizedSlab_vertical_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntegrableOn (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      (Set.Icc (-S) S ×ˢ slabPlanarBox H) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  have hs := (MeasurePreserving.symm slabVerticalEquiv h).integrable_comp_emb
    (g := fun x : Position => NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-x))
    slabVerticalEquiv.symm.measurableEmbedding
  exact (hs.mpr (regularizedSlab_integrableOn hepsilon hH hS (slabAxisPoint z))).congr
    (Filter.Eventually.of_forall (regularizedSlab_vertical_kernel epsilon z))

theorem regularizedSlab_vertical (epsilon rho : ℝ) {H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in Set.Icc (-S) S, ∫ p in slabPlanarBox H,
        coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖ := by
  unfold regularizedSlabPotential
  rw [slabVertical_setIntegral]
  simp_rw [regularizedSlab_vertical_kernel]
  rw [Measure.volume_eq_prod, setIntegral_prod _
    (regularizedSlab_vertical_integrable hepsilon hH hS z)]

end ContinuumCoulomb

end

end OAI
