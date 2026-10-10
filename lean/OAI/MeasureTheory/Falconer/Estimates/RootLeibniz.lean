import OAI.MeasureTheory.Falconer.Fourier.RootPairSymbols
import OAI.MeasureTheory.Falconer.Measures.NormalizedLeibnizAssignment
import OAI.MeasureTheory.Falconer.Estimates.InverseLeibniz

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev RootMaskIndex := PolicyDescriptor ⊕ PolicyDescriptor

noncomputable def rootMaskIndices (d e : RootEndpointData) : Finset RootMaskIndex := d.S.disjSum e.S

def rootMaskDescriptor : RootMaskIndex → PolicyDescriptor := Sum.elim id id

noncomputable def rootAngleFactor (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : RootMaskIndex → ℝ → ℝ :=
  Sum.elim
    (fun b => descriptorAngleMask d.Q d.ρ d.mass N d.lam sig d.J d.i b z.1)
    (fun b => descriptorAngleMask e.Q e.ρ e.mass N e.lam sig e.J e.i b z.2)

noncomputable def rootAssignmentScale (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : ℝ :=
  ∏ b ∈ rootMaskIndices d e, (sourceAngularRadius N sig (descriptorLength (rootMaskDescriptor b)))⁻¹^(k b)

theorem rootAngleFactor_contDiff (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) (b : RootMaskIndex) :
    ContDiff ℝ ∞ (rootAngleFactor d e N sig z b) := by
  cases b with
  | inl b => exact descriptorAngleMask_contDiff _ hd _ _ _ _ _ _ _ _ _
  | inr b => exact descriptorAngleMask_contDiff _ he _ _ _ _ _ _ _ _ _

theorem rootPairSymbol_product (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (θ : ℝ) :
    rootPairSymbol d e N sig z (sourceUnitDirection θ) =
      ∏ b ∈ rootMaskIndices d e, (rootAngleFactor d e N sig z b θ : ℂ) := by
  simp [rootPairSymbol,RootEndpointData.mask,descriptorListMask,rootMaskIndices,
    Finset.prod_disjSum,rootAngleFactor,descriptorAngleMask,Complex.ofReal_prod]

theorem root_assignment_normalized (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) (z : Plane × Plane) (θ : ℝ) :
    assignedDerivProduct (rootMaskIndices d e) (fun b t => (rootAngleFactor d e N sig z b t : ℂ)) k θ =
      (rootAssignmentScale d e N sig k : ℂ) *
        (d.symbol N sig (fun b => k (.inl b)) (fun _ => 1) z.1 (sourceUnitDirection θ) *
          conj (e.symbol N sig (fun b => k (.inr b)) (fun _ => 1) z.2 (sourceUnitDirection θ))) := by
  rw [assignedDerivProduct_normalized _ _ _ k
    (fun b _ => rootAngleFactor_contDiff d e hd he N sig z b)
    (fun b _ => (sourceAngularRadius_pos N sig (descriptorLength (rootMaskDescriptor b))).ne') θ]
  congr 1
  simp only [RootEndpointData.symbol,inheritedCircleSymbol_comp,one_mul,Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  congr 1
  simp [rootMaskIndices,Finset.prod_disjSum,rootAngleFactor,rootMaskDescriptor,inheritedMaskProduct]

theorem rootPairSymbol_inverse_leibniz (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (j : ℕ) (θ : ℝ) :
    inverseStationaryOperator j (fun t => rootPairSymbol d e N sig z (sourceUnitDirection t)) θ =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun a =>
        a.1 * ((rootAssignmentScale d e N sig a.2 : ℂ) *
          (d.symbol N sig (fun b => a.2 (.inl b)) (fun _ => 1) z.1 (sourceUnitDirection θ) *
            conj (e.symbol N sig (fun b => a.2 (.inr b)) (fun _ => 1) z.2 (sourceUnitDirection θ)))))).sum := by
  simp_rw [rootPairSymbol_product]
  rw [inverseLeibnizTerms_expansion j (rootMaskIndices d e)
    (fun b t => (rootAngleFactor d e N sig z b t : ℂ))
    (fun b _ => Complex.ofRealCLM.contDiff.comp (rootAngleFactor_contDiff d e hd he N sig z b))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [root_assignment_normalized d e hd he N sig a.2 z θ]

end PlanarFalconer

end OAI
