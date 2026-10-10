import Mathlib
import OAI.Combinatorics.UniformKServer.StarMovementBudget
import OAI.Combinatorics.UniformKServer.TreeAllocator

namespace OAI

                                             
section

/-! Global allocation movement with an absolute, degree/depth independent
coefficient. The finite additive term is displayed as a function of the fixed
tree, its radii and k, not of a law or a horizon. -/
noncomputable section
namespace UniformKServer.TreeAllocationMovement
open Finset TreeRounding TreeRankData TreeAllocator RankTracking
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def integral (d : Data Ω S k) (H : ℕ) (f : ℕ → Ω → ℝ) : ℝ :=
  ∑ t ∈ range H, average d.weight (f t)

theorem integral_sum {A : Type*} [Fintype A] (d : Data Ω S k) (H : ℕ) (f : A → ℕ → Ω → ℝ) :
    integral d H (fun t ω => ∑ i, f i t ω)=∑ i, integral d H (f i) := by
  exact StarEnergy.integral_sum (TreeRankData.single d 0) H f

theorem integral_nonneg (d : Data Ω S k) (H : ℕ) {f : ℕ → Ω → ℝ} (h : ∀ t ω, 0 ≤ f t ω) :
    0 ≤ integral d H f := StarEnergy.integral_nonneg (TreeRankData.single d 0) H h

def nodeMove (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) : ℝ :=
  integral d H (fun t ω => |amount d hk (t+1) ω v-amount d hk t ω v|)

def hiddenMove (d : Data Ω S k) (H : ℕ) (v : Vertex n) : ℝ :=
  integral d H (fun t ω => |(d.count (t+1) ω v:ℝ)-d.count t ω v|)

def movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, if v=0 then 0 else w (S.parent v)*nodeMove d hk H v

def hiddenCost (d : Data Ω S k) (H : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, if v=0 then 0 else w (S.parent v)*hiddenMove d H v

def allowance (S : Shape n) (k : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, w v*StarEnergy.allowance (Children S v) k

theorem local_movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) :
    (∑ i : Children S v, nodeMove d hk H i.val) ≤ nodeMove d hk H v+
      (10:ℝ)^63*EpochAlpha.ell k*(∑ i : Children S v, hiddenMove d H i.val)+
      (10:ℝ)^63*EpochAlpha.ell k*StarEnergy.allowance (Children S v) k := by
  have h := StarMovementBudget.movement (TreeRankData.star d v) hk H (fun t ω => amount d hk t ω v)
    (fun t ω => parent_le d hk t ω v)
  have hop (t : ℕ) (ω : Ω) :
      StarAllocator.output (TreeRankData.star d v) hk t ω (amount d hk t ω v)=fun i => amount d hk t ω i.val :=
    funext fun i => (child d hk t ω v i).symm
  simp only [hop,AllocationOutputs.variation,StarEnergy.cost,
    StarEnergy.integral_sum] at h
  unfold StarEnergy.countMove at h
  simp only [StarEnergy.integral_sum] at h
  exact h

theorem node_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (v : Vertex n) :
    0 ≤ nodeMove d hk H v := integral_nonneg d H fun _ _ => abs_nonneg _

theorem root_move (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) : nodeMove d hk H 0=0 := by
  simp [nodeMove,integral,TreeAllocator.root,average]

theorem movement_nonneg (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v) : 0 ≤ movement d hk H w := by
  apply sum_nonneg
  intro v _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw _) (node_nonneg d hk H v)

theorem global_movement (d : Data Ω S k) (hk : 1 ≤ k) (H : ℕ) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v)) :
    movement d hk H w ≤ 2*(10:ℝ)^63*EpochAlpha.ell k*hiddenCost d H w+
      2*(10:ℝ)^63*EpochAlpha.ell k*allowance S k w := by
  have h := sum_le_sum (s:=univ) (fun v _ => mul_le_mul_of_nonneg_left (local_movement d hk H v) (hw v))
  have hrewrite : (∑ v, w v*(nodeMove d hk H v+
      (10:ℝ)^63*EpochAlpha.ell k*(∑ i : Children S v, hiddenMove d H i.val)+
      (10:ℝ)^63*EpochAlpha.ell k*StarEnergy.allowance (Children S v) k)) =
      (∑ v, w v*nodeMove d hk H v)+(10:ℝ)^63*EpochAlpha.ell k*hiddenCost d H w+
      (10:ℝ)^63*EpochAlpha.ell k*allowance S k w := by
    simp only [mul_add,mul_left_comm (w _),sum_add_distrib,←mul_sum]
    rw [weighted_children]
    rfl
  rw [weighted_children,hrewrite] at h
  have hs := weight_separation S w (nodeMove d hk H) hsep (node_nonneg d hk H) (root_move d hk H)
  change 22*(∑ v,w v*nodeMove d hk H v) ≤ movement d hk H w at hs
  change movement d hk H w ≤ _ at h
  have hn := movement_nonneg d hk H w hw
  linarith only [h,hs,hn]

end UniformKServer.TreeAllocationMovement

end


end

end OAI
