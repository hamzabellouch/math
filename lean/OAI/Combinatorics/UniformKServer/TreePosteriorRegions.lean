import Mathlib
import OAI.Combinatorics.UniformKServer.TreeCountData
import OAI.Combinatorics.UniformKServer.ParkCapacity

namespace OAI

                                           
section

/-! True posterior counts are exactly the mass of the current causal tree
region. This is an identity, not an auxiliary estimate assumed of a law. -/
noncomputable section
namespace UniformKServer.TreePosteriorRegions
open Finset TreeRounding TreeAncestry TreeLeaves ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {n k : ℕ} {S : Shape n}

def region (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ) (ω : Ω)
    (u : Vertex n) : Finset X := univ.filter (fun x => descends S u (M.toLeaf t ω x))

omit [Fintype X] in
theorem atom_sum (x : X) (R : Finset X) :
    (∑ y ∈ R, HiddenFlow.atom x y)=if x ∈ R then 1 else 0 := by
  simp only [HiddenFlow.atom]
  rw [sum_ite_eq]

theorem raw_count (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ)
    (ω z : Ω) (u : Vertex n) :
    (TreeLeaves.count (S:=S) (fun a => M.toLeaf t ω (D.position t z a)) u:ℝ)=
      ∑ y ∈ region D M t ω u, HiddenFlow.counts D t z y := by
  unfold TreeLeaves.count HiddenFlow.counts
  rw [sum_comm]
  simp only [Nat.cast_sum,atom_sum]
  apply sum_congr rfl
  intro a _
  simp only [TreeLeaves.indicator,region,mem_filter,mem_univ,true_and]
  split_ifs <;> norm_num

theorem mean_mass (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (t : ℕ)
    (ω : Ω) (u : Vertex n) :
    TreeCoverage.mean (TreeCountData.data D M) t ω u=
      ParkCapacity.mass (HiddenFlow.current D t ω) (region D M t ω u) := by
  unfold TreeCoverage.mean posterior ParkCapacity.mass HiddenFlow.current
  change (∑ z, kernel D.weight (D.filtration t) ω z*(TreeCountData.data D M).count t z u)=_
  have hh : (∑ z, kernel D.weight (D.filtration t) ω z*((TreeCountData.data D M).count t z u:ℝ))=
      ∑ z, kernel D.weight (D.filtration t) ω z*(∑ y ∈ region D M t ω u, HiddenFlow.counts D t z y) := by
    apply sum_congr rfl
    intro z _
    by_cases hz : (D.filtration t).r ω z
    · have he := M.causal t ω z hz
      change _ * (TreeLeaves.count (S:=S) (fun a => M.toLeaf t z (D.position t z a)) u:ℝ)=_
      rw [←he,raw_count D M t ω z u]
    · simp only [kernel,ite_eq_right hz,zero_mul]
  rw [hh]
  simp only [mul_sum]
  rw [sum_comm]
  rfl

theorem domination (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) (u : Vertex n) :
    TreeAllocator.amount (TreeCountData.data D M) hk t ω u ≤
      132*ParkCapacity.mass (HiddenFlow.current D t ω) (region D M t ω u) := by
  rw [←mean_mass]
  exact TreeCoverage.domination _ hk (TreeCountData.root D M) t ω u

end UniformKServer.TreePosteriorRegions

end


end

end OAI
