import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalRound
import OAI.Combinatorics.KMedian.Rounding.RationalProposalBound

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type} [DecidableEq F] [Fintype F] {Δ n : ℕ}

theorem rational_conditional_round_drift (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
    {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
    let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
    μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  intro H μ
  let D := heavyActions (graphActions G) H
  let b := GroupCap.cap R d (integral Δ A)
  let b' := GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)
  have hb0 : 0 ≤ b := GroupCap.cap_nonneg d _ hR0 hd0
  have hbR : b ≤ 5*R := GroupCap.cap_le_radius R d _
  have hb'0 : 0 ≤ b' := GroupCap.cap_nonneg d _ hR0 hd0
  have hb' : b' ≤ b := GroupCap.cap_antitone R d subset_union_left
  have hy : mass g (localSet A S) ≤ 1 := by
    rw [localSet_mass A S hSA]
    exact (mass_mono hg.le hS).trans_eq hm₀
  have hbQ : b ≤ 5*((PhysicalPotential.cost g (fun i : A => d i.val.1) (localSet A S)+
      (1-mass g (localSet A S))*b)/g) := by
    rw [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1)]
    simpa only [mul_div_assoc] using local_cap_scale hg hS hm₀ (fun i _ => hd0 i.1) hb0 hbR hR
  have hbF : ∀ i ∈ forcedAlive A S H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_filter.mp hi).2)
  have hbH : ∀ i ∈ H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_image.mpr ⟨i,hi,rfl⟩))
  have hh := RationalBatchData.proposal_local_bound G (localSet A S) (forcedAlive A S H) Δ
    g β p φ hp hφ hupper enum (fun i => d i.val.1) hprob
    hG hg hg1 hunit hx0 hx1 hh0 hh1 hφ1 hsmall
    hy (forcedAlive_subset A S H) (heavy_alive_forced A S H) (fun i => hd0 i.val.1) hR0
    (fun i hi => hdR i.val (hS ((mem_localSet _ _ _).mp hi)))
    hbQ hb0 hbR hb'0 hb' hbF hbH
  dsimp only at hh
  change μ.real.expect _ ≤ _ at hh
  have hpoint : ∀ Z, potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))=
    potential (x*Real.exp (-h)) g (fun i : A => d i.val.1)
      (nextAliveAt D (coefficient x (mass g (localSet A S))) (fun i => d i.val.1)
        (localSet A S \ forcedAlive A S H) Z)
      (nextCap D (fun i => d i.val.1) b' Z) := by
    intro Z
    rw [round_cap A G H Z R d hG hown]
    unfold roundAlive
    rw [image_potential,localSet_mass A S hSA]
  have hequal := congrArg
    (fun v : Finset (HeavyAction (graphActions G) H) → ℝ =>
      μ.real.expect (fun Z => v Z-potential x g (fun i => d i.1) S b)) (funext hpoint)
  apply hequal.le.trans
  convert hh using 1 <;>
    (try simp only [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1),
    localSet_potential A S hSA x g b (fun i => d i.1),b,D,H,
    RationalBatchData.heavy_eq,RationalBatchData.graph_eq])
  all_goals rfl

end MetricKMedian.CopyState
end
end

end OAI
