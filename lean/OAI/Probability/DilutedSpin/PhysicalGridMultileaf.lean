import OAI.Probability.DilutedSpin.CanonicalRegularMultileaf
import OAI.Probability.DilutedSpin.JointGridSelection

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {p t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- Physical specialization of the non-singleton induction step. The only
signed history is literally the covariance controlled by joint_grid_selection;
all other errors are the single-copy shift error and proper-child root energies.
The evaluation depth is positive, as it is on the regular depth domain. -/
theorem physical_grid_root_multileaf (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
    (u : Spec (H+1+1+r+1+d) × ℕ → ℝ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+(d+1))) (ha : (Q a).val=r+1+(d+1))
    (had : ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) (r+1+(d+1)+1) (r+1+(d+1)+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+(d+1):ℕ)) (hr : DepthAverage.Regular η Q) :
    let L₀ := H+1+1+r+1+d
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
      (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
      (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    let ht := shiftedFrameHeight H r (d+1)
    let OldChild := fun j => realize (H+1) (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) (d+1)
    let S := splitFrame OldNode r (d+1)
    let RawTarget := splitFrame NewNode (r+1) (d+1)
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r (d+1) (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) (d+1) (K' z) (f' z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) (d+1) 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) (d+1) 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r (d+1) 0 b
    let m := Fin.cons 0 (gridExponents L₀)
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) (d+1) (K z) (f z) ∂μ) ≤
      2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  let L₀ := H+1+1+r+1+d
  have hh := canonical_regular_root_multileaf
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)) H r (d+1) k hk a C e Q ha had hlarge hr
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
    (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
    (measurable_physicalBase M θB hB N) (readVector_bound _) b b' q0 hq hu hv
  dsimp only at hh
  have hg : grid (H+1+1+r+1+(d+1)) 0 (H+1+1+r+1+(d+1)) =
      Fin.cons 0 (gridExponents L₀) := (gridExponents_cons L₀).symm
  simp only [hg] at hh
  rw [physicalTreeMatrixCovariance_history]
  exact hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
