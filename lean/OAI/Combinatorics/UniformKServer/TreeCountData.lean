import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenFlow
import OAI.Combinatorics.UniformKServer.TreeCoverage

namespace OAI

                                    
section

/-! Tree-law data and guaranteed request coverage derived from a causal map to
leaves and actual legal hidden one-server trajectories. -/
noncomputable section
namespace UniformKServer.TreeCountData
open Finset TreeRounding TreeAncestry TreeLeaves
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

structure Map (D : HiddenFlow.Data X Ω k) (S : Shape n) where
  toLeaf : ℕ → Ω → X → Vertex n
  leaf : ∀ t ω x, TreeLeaves.leaf (S:=S) (toLeaf t ω x)
  causal : ∀ t ω v, (D.filtration t).r ω v → toLeaf t ω=toLeaf t v

def data (D : HiddenFlow.Data X Ω k) (M : Map D S) : TreeRankData.Data Ω S k where
  weight := D.weight
  positive := D.positive
  total := D.total
  filtration := D.filtration
  refines := D.refines
  count := fun t ω => TreeLeaves.count (S:=S) (fun a => M.toLeaf t ω (D.position t ω a))
  bound := fun _t _ω v => count_le _ v
  conserves := fun t ω v hv => count_children _ (fun _a => M.leaf t ω _) v hv

theorem root (D : HiddenFlow.Data X Ω k) (M : Map D S) (t : ℕ) (ω : Ω) :
    (data D M).count t ω 0=k := count_root _

theorem served_count (D : HiddenFlow.Data X Ω k) (M : Map D S) (t : ℕ) (ω v : Ω)
    (hv : (D.filtration (t+1)).r ω v) :
    1 ≤ (data D M).count (t+1) v (M.toLeaf (t+1) ω (D.request t ω)) := by
  have hpos : D.position (t+1) v (D.chosen t v)=D.request t v := by rw [D.update,ite_eq_left rfl]
  have hmap := M.causal (t+1) ω v hv
  have hreq := D.request_measurable t ω v hv
  have he : TreeLeaves.indicator (S:=S) (M.toLeaf (t+1) ω (D.request t ω))
      (M.toLeaf (t+1) v (D.position (t+1) v (D.chosen t v)))=1 := by
    rw [hpos,←hmap,←hreq]
    exact ite_eq_left (desc_refl _)
  conv_lhs => rw [←he]
  exact single_le_sum (f := fun a => TreeLeaves.indicator (S:=S) (M.toLeaf (t+1) ω (D.request t ω))
    (M.toLeaf (t+1) v (D.position (t+1) v a))) (fun _ _ => Nat.zero_le _) (mem_univ (D.chosen t v))

theorem serves (D : HiddenFlow.Data X Ω k) (M : Map D S) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    1 ≤ TreeAllocator.amount (data D M) hk (t+1) ω (M.toLeaf (t+1) ω (D.request t ω)) :=
  TreeCoverage.required (data D M) hk (t+1) ω _ (served_count D M t ω)

end UniformKServer.TreeCountData

end


end

end OAI
