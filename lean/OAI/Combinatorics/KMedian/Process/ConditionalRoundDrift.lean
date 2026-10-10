import Mathlib
import OAI.Combinatorics.KMedian.Process.LocalBatchUniform
import OAI.Combinatorics.KMedian.Process.PhysicalRound

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

theorem conditional_round_drift (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (H : Finset A) (q : HeavyAction (graphActions G) H → ℝ)
    {x g h φ R : ℝ} (d : F → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hp1 : 2*h*g ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hq : ∀ e, 2*h*g ≤ q e ∧ q e ≤ (1+φ)*(2*h*g))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let D := heavyActions (graphActions G) H
    let μ := PhysicalBatchLaw.law (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1
    μ.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      g*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*(φ+h)*R := by
  intro D μ
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
  have hh := actual_local_bound G H (localSet A S) (forcedAlive A S H) Δ q
    (fun i => d i.val.1) hG hg hg1 hunit hx0 hx1 hh0 hh1 hp1 hφ0 hφ1 hq0 hq1 hq hsmall
    hy (forcedAlive_subset A S H) (heavy_alive_forced A S H) (fun i => hd0 i.val.1) hR0
    (fun i hi => hdR i.val (hS ((mem_localSet _ _ _).mp hi)))
    hbQ hb0 hbR hb'0 hb' hbF hbH
  change μ.expect _ ≤ _ at hh
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
  simp_rw [hpoint]
  simpa only [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1),
    localSet_potential A S hSA x g b (fun i => d i.1),b,D] using hh

end MetricKMedian.CopyState
end
end

end OAI
