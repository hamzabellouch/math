import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabKernelEstimates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Exact ordinary product coordinates for the slab Coulomb integral.
These allow the finite-box potential to be treated by one-coordinate
integrals without changing the Euclidean volume normalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

abbrev SlabTriple := ℝ × (ℝ × ℝ)

def slabTripleEquiv : Position ≃ᵐ SlabTriple :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

theorem slabTripleEquiv_apply (x : Position) : slabTripleEquiv x = (x 0, x 1, x 2) := rfl

theorem slabTripleEquiv_symm_apply (p : SlabTriple) :
    slabTripleEquiv.symm p = WithLp.toLp 2 ![p.1, p.2.1, p.2.2] := by
  ext a
  fin_cases a <;> rfl

theorem slabTripleEquiv_measurePreserving : MeasurePreserving slabTripleEquiv := by
  exact ((MeasurePreserving.id volume).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))

def slabTripleBox (H S : ℝ) : Set SlabTriple :=
  Set.Icc (-H) H ×ˢ (Set.Icc (-H) H ×ˢ Set.Icc (-S) S)

theorem slabTripleBox_measurable (H S : ℝ) : MeasurableSet (slabTripleBox H S) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem slabTripleBox_preimage (H S : ℝ) :
    slabTripleEquiv ⁻¹' slabTripleBox H S = slabDomain H S := by
  ext x
  simp only [Set.mem_preimage, slabTripleBox, slabTripleEquiv_apply,
    Set.mem_prod, Set.mem_Icc, slabDomain, Set.mem_ofPred_eq, abs_le]

theorem slabTriple_setIntegral (H S : ℝ) (f : Position → ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ p in slabTripleBox H S, f (slabTripleEquiv.symm p) := by
  have h := slabTripleEquiv_measurePreserving.restrict_preimage (slabTripleBox_measurable H S)
  rw [slabTripleBox_preimage] at h
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    h.integral_comp' (f ∘ slabTripleEquiv.symm)

theorem slabPotential_eq_setIntegral (rho H S : ℝ) (y : Position) :
    slabPotential rho H S y = -rho * ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x) := by
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity rho H S x) =
      (slabDomain H S).indicator (fun x => rho*Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx]
      ring
    · simp only [slabDensity, Set.indicator_of_notMem hx, mul_zero]
  unfold slabPotential
  rw [he, integral_indicator (slabDomain_isClosed H S).measurableSet, integral_const_mul]
  ring

theorem slabPotential_triple (rho H S : ℝ) (y : Position) :
    slabPotential rho H S y =
      -rho * ∫ p in slabTripleBox H S,
        Coulomb.coulombKernel (y-slabTripleEquiv.symm p) := by
  rw [slabPotential_eq_setIntegral, slabTriple_setIntegral]

end ContinuumCoulomb

end

end OAI
