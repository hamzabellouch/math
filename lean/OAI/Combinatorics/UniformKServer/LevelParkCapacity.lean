import Mathlib
import OAI.Combinatorics.UniformKServer.ParkCapacity
import OAI.Combinatorics.UniformKServer.ParkCoefficients

namespace OAI

                                        
section

/-! A cumulative level sum retains the shared tree subtree capacity. Zero
parks require no fictitious nonempty region. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [Fintype X] [MetricSpace X]

theorem positive_sum (a : Allocation S k) (V : Finset (Vertex n)) :
    (∑ v∈V.filter (fun u=>0<park S a.amount u),park S a.amount v)=∑ v∈V,park S a.amount v := by
  rw [sum_filter]
  apply sum_congr rfl
  intro v _
  split_ifs with h
  · rfl
  · exact (le_antisymm (le_of_not_gt h) (a.park_nonneg v)).symm

theorem level_cumulative (a : Allocation S k) (G : Geometry S X) (μ : X→ℝ)
    (hμ : ∀ x,0≤μ x) (C : ℝ) (hC : 0≤C)
    (hdom : ∀ v,a.amount v≤C*mass μ (G.region v)) (V : ℕ→Finset (Vertex n))
    (J j : ℕ) (y : X)
    (hdepth : ∀ i<J,∀ v∈V i,depth S v=i+1)
    (hw : ∀ i<J,∀ v∈V i,0<park S a.amount v→
      ∃ x∈G.region v,dist y x≤27*G.radius (i+1)) :
    ParkCoefficients.tail (fun i=>∑ v∈V i,park S a.amount v) J j≤
      C*mass μ (ball y (67*G.radius (j+1))) := by
  let U : ℕ→Finset (Vertex n) := fun i=>(V i).filter (fun v=>0<park S a.amount v)
  have hdp : (Ico j J : Set ℕ).PairwiseDisjoint U := by
    intro i hi l hl hne
    apply Finset.disjoint_left.mpr
    intro v hv hu
    have hd1 := hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1
    have hd2 := hdepth l (mem_Ico.mp hl).2 v (mem_filter.mp hu).1
    omega
  have he : ParkCoefficients.tail (fun i=>∑ v∈V i,park S a.amount v) J j=
      ∑ v∈(Ico j J).biUnion U,park S a.amount v := by
    rw [sum_biUnion hdp]
    exact sum_congr rfl (fun i _=>(positive_sum a (V i)).symm)
  rw [he]
  apply cumulative a G μ hμ C hC hdom
  · intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    rw [hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1]
    exact Nat.add_le_add_right (mem_Ico.mp hi).1 1
  · intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    obtain ⟨x,hx,hd⟩ := hw i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    refine ⟨x,hx,?_⟩
    rw [hdepth i (mem_Ico.mp hi).2 v (mem_filter.mp hv).1]
    exact hd

end UniformKServer.ParkCapacity

end


end

end OAI
