import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityShift

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  by_cases h:0≤B-x
  · rw [max_eq_left h];linarith
  · rw [max_eq_right (le_of_not_ge h)];linarith

theorem live_allocated_excess_defect (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mact) 0 := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ s.b₁ s.b₂ κ Mact hZ h₁ h₂ s.P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ s.P hP
  linarith

theorem live_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
        δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem source_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      ((∃z:O,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
          s.W₁ s.W₂ X₁ X₂≠0) →
        Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh) := by
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  rintro ⟨z,hne⟩
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem paired_width_defect_cost (shell edge₁ edge₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)
    (h₁:edge₁≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh)
    (h₂:edge₂≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(edge₁+edge₂)/2-(w+ell)≤δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
