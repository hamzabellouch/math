import OAI.Probability.DilutedSpin.RootMultileafMatrix
import OAI.Probability.DilutedSpin.ScheduledFrameError

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
open PrescribedTree
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}

 
theorem scheduled_multileaf_matrix (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (K : KernelTower Ω (H+1+1+r+1+d))
    (f : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := kernelHeightCast ht.symm K
    let f' := vectorHeightCast ht.symm f
    let W := (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d K f)
    let W' := (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d K' f')
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    (((d:ℝ)+2)/(L:ℝ))*shapeEnergyAt (stem OldNode r) d K f ≤
      2*((L:ℝ)⁻¹ + matrixObservableHistory Target q K m (v::cs) S x
          (spatialProduct (fun _ : I => f)) (treeOverlap S f)/J+
        (2*Real.sqrt W'+projectionShiftError a C e K f Q)*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  let ht := shiftedFrameHeight H r d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let RawTarget := splitFrame (.node k NewChild) (r+1) d
  let Target := heightCast ht RawTarget
  let q := fun j => leafHeightCast ht RawTarget (q0 j)
  let S := splitFrame (.node k OldChild) r d
  have hq' : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp hq
  have hqd : splitDepth Target (q u) (q v)=d := by
    rw [splitDepth_heightCast,hu,hv]
    exact splitFrame_split (.node k NewChild) (r+1) d b'
  have hbase := multileaf_matrix_pointwise k OldChild b r d Target q hq' B hS K u v huv
    cs hcs hdis hfull hqd f hf
  have hproj := scheduled_frame_target_error_le H r d k hk a C e Q ha hQ K f hf b' q0 hq u v hu hv
  have hcharge : 0 ≤ shiftedCharge B Target S (v::cs).length := by
    unfold shiftedCharge
    exact mul_nonneg (chargeBound_nonneg (by positivity) (by positivity) _ _) (by positivity)
  have hproj' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproj hcharge)
    (abs_nonneg (partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) (Finset.univ.image q)/
      partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) ((insert v ({u}:Finset I)).image q)))
  exact hbase.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hproj') le_rfl) (by norm_num)) le_rfl)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
