import OAI.Geometry.NodalSets.Elliptic.CorrugationClosedCell

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

def corrugationCellIndex (z : ℝ × ℝ) : ℤ × ℤ :=
  (⌊z.1+(1/2:ℝ)⌋,⌊z.2+(1/2:ℝ)⌋)

def corrugationCellPoint (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1-(corrugationCellIndex z).1,z.2-(corrugationCellIndex z).2)

def corrugationCellRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt ((corrugationCellPoint z).1^2+(corrugationCellPoint z).2^2)

lemma corrugationCellPoint_bounds (z : ℝ × ℝ) :
    |(corrugationCellPoint z).1| ≤ 1/2 ∧ |(corrugationCellPoint z).2| ≤ 1/2 :=
  ⟨centered_integer_representative z.1,centered_integer_representative z.2⟩

lemma corrugationCellPoint_reconstruct (z : ℝ × ℝ) :
    ((corrugationCellPoint z).1+(corrugationCellIndex z).1,
     (corrugationCellPoint z).2+(corrugationCellIndex z).2) = z := by
  simp [corrugationCellPoint]

lemma corrugationCellRadius_properties (z : ℝ × ℝ) :
    0 ≤ corrugationCellRadius z ∧
    (corrugationCellRadius z)^2 = (corrugationCellPoint z).1^2+(corrugationCellPoint z).2^2 :=
  ⟨Real.sqrt_nonneg _,Real.sq_sqrt (by positivity)⟩

lemma corrugationPeriodicWell_global_jets (a : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) z =
      fderiv ℝ (corrugationDiskWell a (1/4)) (corrugationCellPoint z) ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) (corrugationCellPoint z) := by
  have hs := corrugationPeriodicWell_shift_jets a (corrugationCellIndex z) (corrugationCellPoint z)
  rw [corrugationCellPoint_reconstruct] at hs
  have hc := corrugationPeriodicWell_closed_cell_jets a (corrugationCellPoint z)
    (corrugationCellPoint_bounds z).1 (corrugationCellPoint_bounds z).2
  exact ⟨hs.1.trans hc.1,hs.2.trans hc.2⟩

lemma corrugationPeriodicWell_global_derivative_bound {a : ℝ} (ha : 0 ≤ a) (z : ℝ × ℝ) :
    ‖fderiv ℝ (corrugationPeriodicWell a) z‖ ≤
      2*corrugationSlope a (1/4) (corrugationCellRadius z) := by
  have h := corrugationPeriodicWell_closed_derivative_bound ha (corrugationCellIndex z)
    (corrugationCellPoint z) (corrugationCellPoint_bounds z).1 (corrugationCellPoint_bounds z).2
    (corrugationCellRadius_properties z).1 (corrugationCellRadius_properties z).2
  rwa [corrugationCellPoint_reconstruct] at h

lemma corrugationPeriodicWell_global_radial_jets (a : ℝ) (z u v : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    fderiv ℝ (corrugationPeriodicWell a) z v =
      corrugationSlope a (1/4) (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) v (corrugationCellRadius z) ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z u v =
      deriv (corrugationSlope a (1/4)) (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) u (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) v (corrugationCellRadius z) +
      (corrugationSlope a (1/4) (corrugationCellRadius z)/corrugationCellRadius z)*
        angularComponent (corrugationCellPoint z) u (corrugationCellRadius z)*
        angularComponent (corrugationCellPoint z) v (corrugationCellRadius z) := by
  rw [(corrugationPeriodicWell_global_jets a z).1,(corrugationPeriodicWell_global_jets a z).2]
  exact ⟨corrugationDiskWell_radial_first a (1/4) _ v hr (corrugationCellRadius_properties z).2,
    corrugationDiskWell_radial_second a (1/4) _ u v hr (corrugationCellRadius_properties z).2⟩

end
end Yau.Geometry

end OAI
