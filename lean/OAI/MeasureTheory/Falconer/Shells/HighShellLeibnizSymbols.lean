import OAI.MeasureTheory.Falconer.Measures.NormalizedLeibnizAssignment
import OAI.MeasureTheory.Falconer.Estimates.InverseLeibniz
import OAI.MeasureTheory.Falconer.Fourier.MinimalPairSymbol

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev PairMaskIndex := PolicyDescriptor × Fin 2

noncomputable def pairMaskIndices (S : Finset PolicyDescriptor) : Finset PairMaskIndex :=
  S.product Finset.univ

noncomputable def assignmentScale (S : Finset PolicyDescriptor) (N : ℕ) (sig : ℝ)
    (k : PairMaskIndex → ℕ) : ℝ :=
  ∏ a ∈ pairMaskIndices S, (sourceAngularRadius N sig (descriptorLength a.1))⁻¹^(k a)

theorem paired_inheritedMaskProduct (S : Finset PolicyDescriptor) (k : PairMaskIndex → ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (x : Fin 2 → Plane) (θ : ℝ) :
    (inheritedMaskProduct (pairMaskIndices S) Prod.fst k Q ρ m N lam sig J i (fun a => x a.2) θ : ℂ) =
      inheritedCircleSymbol S id (fun b => k (b,0)) Q ρ m N lam sig J i (fun _ => 1) (x 0) (sourceUnitDirection θ) *
      conj (inheritedCircleSymbol S id (fun b => k (b,1)) Q ρ m N lam sig J i (fun _ => 1) (x 1) (sourceUnitDirection θ)) := by
  rw [inheritedCircleSymbol_comp,inheritedCircleSymbol_comp]
  simp only [one_mul,Complex.conj_ofReal,← Complex.ofReal_mul]
  congr 1
  simp [inheritedMaskProduct,pairMaskIndices,Finset.prod_product,Fin.prod_univ_two,
    Finset.prod_mul_distrib]

theorem paired_assignment_normalized (S : Finset PolicyDescriptor) (k : PairMaskIndex → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : Fin 2 → Plane) (θ : ℝ) :
    assignedDerivProduct (pairMaskIndices S)
      (fun a t => (descriptorAngleMask Q ρ m N lam sig J i a.1 (x a.2) t : ℂ)) k θ =
    (assignmentScale S N sig k : ℂ) *
      (inheritedCircleSymbol S id (fun b => k (b,0)) Q ρ m N lam sig J i (fun _ => 1) (x 0) (sourceUnitDirection θ) *
      conj (inheritedCircleSymbol S id (fun b => k (b,1)) Q ρ m N lam sig J i (fun _ => 1) (x 1) (sourceUnitDirection θ))) := by
  rw [actual_assignment_normalized _ _ _ _ hQ,paired_inheritedMaskProduct]
  rfl

namespace PositiveDistanceData

theorem pairMaskSymbol_product (d : PositiveDistanceData) (z : Plane × Plane) (θ : ℝ) :
    let S := policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
    d.pairMaskSymbol z (sourceUnitDirection θ) =
      ∏ a ∈ pairMaskIndices S,
        (descriptorAngleMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i a.1 (![z.1,z.2] a.2) θ : ℂ) := by
  simp [pairMaskSymbol,pairMaskIndices,Finset.prod_product,Fin.prod_univ_two,
    Finset.prod_mul_distrib,descriptorAngleMask,descriptorListMask]

theorem pairMaskSymbol_inverse_leibniz (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) (j : ℕ) (θ : ℝ) :
    let S := policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
    inverseStationaryOperator j (fun t => d.pairMaskSymbol z (sourceUnitDirection t)) θ =
      ((inverseLeibnizTerms j (pairMaskIndices S)).map (fun a =>
        a.1 * ((assignmentScale S d.N d.sig a.2:ℂ) *
          (inheritedCircleSymbol S id (fun b => a.2 (b,0)) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) z.1 (sourceUnitDirection θ) *
            conj (inheritedCircleSymbol S id (fun b => a.2 (b,1)) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) z.2 (sourceUnitDirection θ)))))).sum := by
  dsimp only
  let S := policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  let f : PairMaskIndex → ℝ → ℂ := fun a t =>
    (descriptorAngleMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i a.1 (![z.1,z.2] a.2) t : ℂ)
  have hf : ∀ a ∈ pairMaskIndices S, ContDiff ℝ ∞ (f a) := by
    intro a ha
    exact Complex.ofRealCLM.contDiff.comp
      (descriptorAngleMask_contDiff d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i a.1 (![z.1,z.2] a.2))
  simp_rw [pairMaskSymbol_product]
  change inverseStationaryOperator j (fun t => ∏ a ∈ pairMaskIndices S, f a t) θ = _
  rw [inverseLeibnizTerms_expansion j (pairMaskIndices S) f hf]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  change a.1 * assignedDerivProduct (pairMaskIndices S)
    (fun b t => (descriptorAngleMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b.1 (![z.1,z.2] b.2) t : ℂ)) a.2 θ = _
  rw [paired_assignment_normalized _ _ _ hQ]
  rfl

end PositiveDistanceData

end PlanarFalconer

end OAI
