import OAI.Analysis.CircleDomains.Selection.BlockCodeInvariants
import OAI.Analysis.CircleDomains.Topology.ConstantPhysicalPath

namespace OAI

/-! Normalize an arbitrary mixed paid chain into grouped old-jump blocks.
Consecutive true pieces are joined; a jump receives a zero-cost constant
true piece when needed. Total cost and all new disk labels are preserved. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I K : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_grouped_code_of_paid_chain
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B : Set X) (O : I → Set X) (W : K → Set X) (hW : ∀k, (W k ∩ B).Nonempty)
    (T : I → ℝ≥0∞) (r : ℝ≥0∞) (τ : ℝ)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain (physicalJumpEdge d ν N g m (Sum.elim O W)
      (Sum.elim T (fun k => fixedWidthJumpToll B m r τ (W k)))) x y c)
    (hx : x ∈ d.quotientDomain) (hy : y ∈ d.quotientDomain) :
    ∃n : ℕ, ∃P : BoundedBlockPattern I n, ∃Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B {x} {y} O P Z ∧ jumpBlockCost d B g m r τ T P Z = c ∧
      BlockPathsInDomain d P Z ∧ BlockDisksFrom d W P Z := by
  classical
  induction hc with
  | refl x =>
      obtain ⟨γ, θ, hγ, heq, hcost⟩ := exists_allowed_constant_physical_path d hdisj ν N hx g m (hm _ hx)
      let Γ : TaggedPhysicalPath d := (γ, θ)
      refine ⟨0, singlePiecePattern I, singlePieceBlock d Γ, ?_, ?_, ?_, ?_⟩
      · exact singlePieceBlock_valid d ν N B {x} {x} O Γ hγ
          ⟨heq ⊥, (heq ⊥).symm ▸ hx⟩ ⟨heq ⊤, (heq ⊤).symm ▸ hx⟩
      · rw [singlePieceBlock_cost]
        exact hcost
      · exact singlePieceBlock_inDomain d Γ ((heq ⊥).symm ▸ hx) ((heq ⊤).symm ▸ hx)
      · exact singlePieceBlock_disksFrom d Γ W
  | @cons x y z a b hedge _ ih =>
      rcases hedge with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hΓcost⟩ | ⟨i, hxV, hyV, ha⟩
      · obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyU hy
        have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
        obtain ⟨γ, hγ, hγ0, hγ1, hγcost⟩ := exists_allowed_joined_full_cost d hU ν N g hg m hm
          Γ (Z.paths 0 0) hΓ (hZ.allowed 0 0) (hΓ0.symm ▸ hxU) (hΓ1.symm ▸ hyU)
          (hdom 0 0).2 (hΓ1.trans hinit.symm) hpoint
        have hstart : γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
          ⟨hγ0.trans hΓ0, (hγ0.trans hΓ0).symm ▸ hxU⟩
        have hpcost : physicalTollCost d g m γ.1 = a + physicalTollCost d g m (Z.paths 0 0).1 := by
          rw [hγcost, hΓcost]
        refine ⟨n, P, replaceInitialTruePiece d P Z γ, ?_, ?_, ?_, ?_⟩
        · exact replaceInitialTruePiece_valid d ν N B {y} {x} {z} O P Z hZ γ hγ hstart hγ1
        · rw [replaceInitialTruePiece_cost d B g m r τ T P Z γ a hpcost, hZcost]
        · exact replaceInitialTruePiece_inDomain d P Z hdom γ hstart.2 (hγ1.symm ▸ (hdom 0 0).2)
        · exact replaceInitialTruePiece_disksFrom d W P Z hfrom γ
      · cases i with
        | inl i =>
            obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyV.2 hy
            have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
            obtain ⟨γ, θ, hγ, heq, hγcost⟩ := exists_allowed_constant_physical_path
              d hdisj ν N hxV.2 g m (hm _ hxV.2)
            let Γ : TaggedPhysicalPath d := (γ, θ)
            have hstart : Γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
              ⟨heq ⊥, (heq ⊥).symm ▸ hxV.2⟩
            have hleft : Γ.1.val ⊤ ∈ O i ∩ d.quotientDomain := (heq ⊤).symm ▸ hxV
            have hright : (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain := hinit.symm ▸ hyV
            refine ⟨n+1, prependOldJumpPattern P i, prependOldBlockJump d P Z Γ i, ?_, ?_, ?_, ?_⟩
            · exact prependOldBlockJump_valid d ν N B {y} {x} {z} O P Z hZ Γ hγ i hstart hleft hright
            · rw [prependOldBlockJump_cost, hγcost, zero_add, hZcost]
              exact congrArg (fun t => t + b) ha.symm
            · exact prependOldBlockJump_inDomain d P Z hdom Γ i hstart.2 hleft.2
            · exact prependOldBlockJump_disksFrom d W P Z hfrom Γ i
        | inr k =>
            obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyV.2 hy
            have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
            obtain ⟨γ, θ, hγ, heq, hγcost⟩ := exists_allowed_constant_physical_path
              d hdisj ν N hxV.2 g m (hm _ hxV.2)
            let Γ : TaggedPhysicalPath d := (γ, θ)
            have hstart : Γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
              ⟨heq ⊥, (heq ⊥).symm ▸ hxV.2⟩
            have hleft : Γ.1.val ⊤ ∈ W k := (heq ⊤).symm ▸ hxV.1
            have hright : (Z.paths 0 0).1.val ⊥ ∈ W k := hinit.symm ▸ hyV.1
            refine ⟨n+1, prependNewJumpPattern P, prependNewBlockJump d P Z Γ (W k), ?_, ?_, ?_, ?_⟩
            · exact prependNewBlockJump_valid d ν N B {y} {x} {z} O P Z hZ Γ hγ (W k)
                hstart hleft hright (hW k)
            · rw [prependNewBlockJump_cost, hγcost, zero_add, hZcost]
              exact congrArg (fun t => t + b) ha.symm
            · exact prependNewBlockJump_inDomain d P Z hdom Γ (W k) hstart.2 ((heq ⊤).symm ▸ hxV.2)
            · exact prependNewBlockJump_disksFrom d W P Z hfrom Γ k

end CircleDomainRigidity

end

end OAI
