import OAI.Probability.DilutedSpin.PhysicalScheduledMultileaf
import OAI.Probability.DilutedSpin.RootChildMoment

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

/-- Root-moment form of the genuine multileaf induction. Projection costs
are now functions of the ROOT conditional covariance of proper children;
there are no caller integrability or projection-error hypotheses. -/
theorem physical_scheduled_root_multileaf_moments (μ : Measure (FullRootState Y X J M))
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
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r d (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z) ∂μ)
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
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  have hh := physical_scheduled_root_multileaf μ H r d k hk a C e Q ha hQ T P m base old V hb hV
    b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  have hW := integral_rootChildSum_le k OldChild r d rfl T P m base old V hb μ hV
  have hOld := integral_sqrt_rootChildSum_le k OldChild r d rfl T P m base old V hb μ hV
  have hNew := integral_sqrt_rootChildSum_le k NewChild (r+1) d ht.symm T P m base old V hb μ hV
  apply hh.trans
  have hmass : 0 ≤ pairHistoryMass (splitFrame (.node k OldChild) r d) (grid L 0 L)
      (splitFrameLeaf (.node k OldChild) r d 0 b) := by unfold pairHistoryMass; positivity
  have hcharge : 0 ≤ shiftedCharge B (heightCast ht (splitFrame (.node k NewChild) (r+1) d))
      (splitFrame (.node k OldChild) r d) (v::cs).length := by
    unfold shiftedCharge
    exact mul_nonneg (chargeBound_nonneg (by positivity) (by positivity) _ _) (by positivity)
  gcongr
  all_goals first | exact hW | exact hOld | exact hNew

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
