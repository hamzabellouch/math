import OAI.Probability.DilutedSpin.PhysicalGridMultileaf
import OAI.Probability.DilutedSpin.RegularPhysicalShift
import OAI.Probability.DilutedSpin.ScheduledCovariance
import OAI.Probability.DilutedSpin.ScheduledSingleton

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

 
theorem physical_grid_scheduled_step (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
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
    let _ := fun z => kernelHeightCast ht.symm (K z)
    let _ := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+(d+1)) (C j) (fun v => (Q (e j v)).val) (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+1+(d+1)) (C j) (fun v => (Q (e j v)).val+1) (K z) (f z) ∂μ)
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
    ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C) (rootSchedule (r+1+(d+1)) (fun j v => (Q (e j v)).val)) (K z) (f z) ∂μ) ≤
      2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  have hh := physical_grid_root_multileaf M θB hB N H r d u k hk a C e Q ha had hlarge hr b b' q0 hq hu hv
  dsimp only at hh
  have hQ : ∀ j v, r+1+(d+1)+1≤(Q (e j v)).val := by
    intro j v
    exact admissible_lower (C j) _ (had j) v
  conv_lhs =>
    arg 2
    arg 2
    ext z
    exact scheduledShapeEnergy_node (H+1) r (d+1) k hk C _ hQ _ _
  simp_rw [descendantEnergyAt_eq_scheduled] at hh
  simp only [scheduledShapeEnergy_heightCast] at hh
  exact hh

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance physicalScheduledStepDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

 
noncomputable def physicalScheduledEnergy (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) : ℝ :=
  ∫ z, scheduledShapeEnergy (L+1) (Q none).val S (fun v => (Q (some v)).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

lemma physicalScheduledEnergy_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    0 ≤ physicalScheduledEnergy M θB hB N L u S Q :=
  integral_nonneg (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)

lemma physicalScheduledEnergy_leaf (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (Q : Option ReducedTopology.leaf.Vertex → Fin (L+1)) :
    physicalScheduledEnergy M θB hB N L u .leaf Q=
      physicalSingletonEnergy (gridExponents L) M θB hB N u (Q none).val := by
  unfold physicalScheduledEnergy physicalSingletonEnergy rootConditionalEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => scheduledShapeEnergy_leaf _ (Q none).isLt _ _ _)

 
theorem physical_scheduled_child_moment (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ))
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) (s : Bool) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (physicalScheduledEnergy M θB hB N L u (C j)
          (DepthAverage.coordinateProjection (childCoordinates (hk := hk) j)
            (fun _ => DepthAverage.shiftPerm s) Q)))) ≤
      Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (DepthAverage.average (regularShapeDomain (C j) (L+1) (η/2))
          (physicalScheduledEnergy M θB hB N L u (C j)))) := by
  exact regular_scheduled_child_moment
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))
    hη hlarge k hk C s

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
