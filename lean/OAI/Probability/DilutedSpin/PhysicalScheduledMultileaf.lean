import OAI.Probability.DilutedSpin.RootChildSumIntegrability
import OAI.Probability.DilutedSpin.RootProjectionIntegrability
import OAI.Probability.DilutedSpin.RootShiftIntegrability
import OAI.Probability.DilutedSpin.ScheduledRootMultileaf

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree HeterogeneousMarks
open scoped BigOperators
variable {α I Ω J X Y : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype Ω] {Mark : J → Type} [∀ j, Fintype (Mark j)] [Countable J]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace X] [MeasurableSpace Y]
    {M N : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- Actual physical-root multileaf induction, with ALL ordinary integrability
premises discharged for finite alphabets and countably many marker types.
The signed root covariance remains a single centered term, not a pointwise
absolute value. This is a dependency of decorrelation, not the main formula. -/
theorem physical_scheduled_root_multileaf (μ : Measure (FullRootState Y X J M))
    [IsProbabilityMeasure μ]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
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
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
    let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let _ := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let _ := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ (rootAlphabet (Ω := Ω) (A := Mark)) Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let OldNode := PrescribedTree.node k OldChild
  let NewNode := PrescribedTree.node k NewChild
  let RawTarget := splitFrame NewNode (r+1) d
  let Target := heightCast ht RawTarget
  let q := fun j => leafHeightCast ht RawTarget (q0 j)
  let S := splitFrame OldNode r d
  let x := splitFrameLeaf OldNode r d 0 b
  let y := splitFrameLeaf OldNode r d 1 b
  apply scheduled_root_multileaf μ (rootAlphabet (Ω := Ω) (A := Mark)) H r d k hk a C e Q ha hQ
    (rootTower T P m base old) (rootVector V) (fun z y i => hV _ i)
    b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  · exact integrable_rootShapeEnergy (stem OldNode r) d T P m base old V hb μ hV
  · exact integrable_rootProjectedTriple OldNode r d T P m base old V hb μ hV
  · have hh := integrable_rootMatrixObservableHistory Target S q (v::cs) x T P m base old
      (spatialProduct (fun _ : I => V)) (spatialProduct (fun _ : S.Leaf => V)) hb μ
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
    have hg (z : FullRootState Y X J M) : treeOverlap S (rootVector (A := Mark) V z) =
        (fun w => spatialProduct (fun _ : S.Leaf => V)
          (fun c => physical (rootArray z.2.2.1 z.2.2.2) _ (S.pathAt c w))) := by
      funext w
      exact treeOverlap_eq_spatialProduct S (rootVector (A := Mark) V z) w
    change Integrable (fun z => matrixObservableHistory Target q (rootTower T P m base old z)
      (grid L 0 L) (v::cs) S x (spatialProduct (fun _ : I => rootVector (A := Mark) V z))
      (treeOverlap S (rootVector (A := Mark) V z))) μ
    simp_rw [hg]
    exact hh
  · exact integrable_rootTargetError OldNode r d T P m base old V hb Target q u v
      (spatialProduct (fun _ : I => V)) μ hV
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
  · exact integrable_rootOldError OldNode r d T P m base old V hb S x y μ hV
  · exact integrable_rootTreeMean T P m base old hb Target
      (fun w => spatialProduct (fun _ : I => V) (fun j => w (q j))) μ
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) _)
  · exact integrable_rootChildSum k OldChild r d rfl T P m base old V hb μ hV
  · exact integrable_sqrt_rootChildSum k OldChild r d rfl T P m base old V hb μ hV
  · exact integrable_sqrt_rootChildSum k NewChild (r+1) d ht.symm T P m base old V hb μ hV
  · exact integrable_root_projectionShiftError a C e T P m base old V hb μ hV Q

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
