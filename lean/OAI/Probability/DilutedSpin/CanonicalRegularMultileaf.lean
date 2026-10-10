import OAI.Probability.DilutedSpin.PhysicalMultileafMoments
import OAI.Probability.DilutedSpin.ScheduledRegularFrame
import OAI.Probability.DilutedSpin.TwoPointLabeling

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree HeterogeneousMarks
open scoped BigOperators
variable {α Ω J X Y : Type} [Fintype α] [DecidableEq α]
    [Fintype Ω] {Mark : J → Type} [∀ j, Fintype (Mark j)] [Countable J]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace X] [MeasurableSpace Y]
    {M N t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

 
theorem canonical_regular_root_multileaf (μ : Measure (FullRootState Y X J M))
    [IsProbabilityMeasure μ]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+d:ℕ)) (hr : DepthAverage.Regular η Q)
    (T : KernelTower Ω (H+1+1+r+1+d)) (P : (j : J) → Fin (H+1+1+r+1+d) → FiniteLaw (Mark j))
    (m : Fin (H+1+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (H+1+1+r+1+d) → ℝ)
    (old : (j : J) → FinitePath Ω (H+1+1+r+1+d) → FinitePath (Mark j) (H+1+1+r+1+d) → ℝ)
    (V : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i|≤1) :
    let K := rootTower T P m base old
    let f := rootVector V (I := J) (A := Mark) (X := X) (Y := Y) (M := M)
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) d
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r d (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let _ := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : Option (Fin (t+1)) => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) d 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let _ := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ (rootAlphabet (Ω := Ω) (A := Mark)) Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  have hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val := by
    intro j v
    rw [ha]
    exact admissible_lower (C j) _ (had j) v
  let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
  let B := shiftedPrefixDepths (stem BaseNode r) d
  have hS := scheduled_regular_old_count H r d k hk a C e Q ha had hlarge hr
  exact physical_scheduled_root_multileaf_moments μ H r d k hk a C e Q ha hQ T P m base old V hb hV
    b b' q0 hq none (some (Fin.last t)) (by simp) hu hv B hS
    (canonicalMatrixTail t) (canonicalMatrixTail_nodup t) (canonicalMatrixTail_not_mem t)
    (canonicalMatrixTail_full t)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
