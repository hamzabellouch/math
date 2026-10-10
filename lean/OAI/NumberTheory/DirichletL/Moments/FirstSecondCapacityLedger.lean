import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

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

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1<Z)(P:ι→ℝ)(hP:∀i,1≤P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0<P i:=fun i=>zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=>hp i)).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1<Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith

theorem allocated_excess_from_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)
    (P:ι→ℝ)(hP:∀i,1≤P i)
    (hs₁:1≤rawScale D a X₁ 0*b₁)(hs₂:1≤rawScale D a X₂ 1*b₂)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ b₁ b₂ κ Mact hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le
  · have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
    linarith
  · positivity

theorem live_allocated_excess (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact allocated_excess_from_parent D a Z X₁ X₂ s.b₁ s.b₂ κ A M Mnom Mact
    w ell δ θ hZ h₁ h₂ hκ s.P hP hs₁ hs₂ hparent hshift hactual hw hell hδ hθ hclip

theorem live_whole_removal (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      κ*(∑i∈removed,Real.logb Z (s.P i))≤w+ell+δ/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hactual hw hell hδ hθ hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  linarith

theorem paired_edge_cost (shell width₁ width₂ cost₁ cost₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)(hwidth₁:width₁≤δ₂)(hwidth₂:width₂≤δ₂)
    (hc₁:cost₁≤w+ell+δ₁/6+θ/3+κ*mesh)
    (hc₂:cost₂≤w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(width₁+width₂)/2+(cost₁+cost₂)/2-(w+ell)≤
      δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

theorem edge_loss_budget (δ₁ δ₂ θ κ mesh ξ η:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤η):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤7*ξ/2+η := by
  nlinarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
