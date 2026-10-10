import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes

namespace OAI

/-! Prepend one new jump and its initial true piece to a grouped chain.
The original first true piece follows the new jump unchanged. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev prependNewJumpPattern {I : Type*} {n : ℕ} (P : BoundedBlockPattern I n) :
    BoundedBlockPattern I (n+1) :=
  ⟨⟨P.1.val, by omega⟩, P.2.1,
    Fin.cons ⟨(P.2.2 0).val+1, by omega⟩ (fun b => ⟨(P.2.2 b.succ).val, by omega⟩)⟩

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def prependNewBlockJump (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    JumpBlockCode d (prependNewJumpPattern P) where
  paths := Fin.cons (Fin.cons γ (Z.paths 0)) (fun b => Z.paths b.succ)
  disks := Fin.cons (Fin.cons V (Z.disks 0)) (fun b => Z.disks b.succ)

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem prependNewBlockJump_finish (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    ∀b, ((prependNewBlockJump d P Z γ V).paths b
      (Fin.last ((prependNewJumpPattern P).2.2 b).val)).1.val ⊤ =
      (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ := by
  intro b
  refine Fin.cases ?_ (fun _ => rfl) b
  change ((Fin.cons γ (Z.paths 0) : Fin ((P.2.2 0).val+2) → TaggedPhysicalPath d)
    (Fin.last ((P.2.2 0).val+1))).1.val ⊤ = _
  rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem prependNewBlockJump_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (V : Set X) (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hleft : γ.1.val ⊤ ∈ V) (hright : (Z.paths 0 0).1.val ⊥ ∈ V)
    (hmeet : (V ∩ B).Nonempty) :
    IsJumpBlockCode d ν N B F' H O (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine Fin.cases ?_ (fun b j => hZ.allowed b.succ j) b
    intro j
    exact Fin.cases hγ (fun j => hZ.allowed 0 j) j
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊥ ∈ F' ∩ d.quotientDomain
      exact hstart
    · change (Z.paths b.succ 0).1.val ⊥ ∈
        blockAnchors F' H O P b.succ.castSucc ∩ d.quotientDomain
      rw [blockAnchors_internal]
      have h := hZ.start b.succ
      rw [blockAnchors_internal] at h
      exact h
  · intro b
    rw [prependNewBlockJump_finish]
    change (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
      blockAnchors F' H O P b.succ ∩ d.quotientDomain
    rw [show blockAnchors F' H O P b.succ = blockAnchors F H O P b.succ from rfl]
    exact hZ.finish b
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.left b.succ i) b
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hleft
    · change (Z.paths 0 i.castSucc).1.val ⊤ ∈ Z.disks 0 i
      exact hZ.left 0 i
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.right b.succ i) b
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hright
    · exact hZ.right 0 i
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.meets b.succ i) b
    intro i
    exact Fin.cases hmeet (fun i => hZ.meets 0 i) i

omit [MeasurableSpace X] in
theorem prependNewBlockJump_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    jumpBlockCost d B g m r τ T (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) =
      physicalTollCost d g m γ.1 + fixedWidthJumpToll B m r τ V +
        jumpBlockCost d B g m r τ T P Z := by
  let Z' := prependNewBlockJump d P Z γ V
  have hpath : (∑j, physicalTollCost d g m (Z'.paths 0 j).1) =
      physicalTollCost d g m γ.1 + ∑j, physicalTollCost d g m (Z.paths 0 j).1 := by
    change (∑j : Fin ((P.2.2 0).val+2), physicalTollCost d g m
      ((Fin.cons γ (Z.paths 0) : Fin ((P.2.2 0).val+2) → TaggedPhysicalPath d) j).1) = _
    rw [Fin.sum_univ_succ]
    rfl
  have hdisk : (∑i, fixedWidthJumpToll B m r τ (Z'.disks 0 i)) =
      fixedWidthJumpToll B m r τ V + ∑i, fixedWidthJumpToll B m r τ (Z.disks 0 i) := by
    change (∑i : Fin ((P.2.2 0).val+1), fixedWidthJumpToll B m r τ
      ((Fin.cons V (Z.disks 0) : Fin ((P.2.2 0).val+1) → Set X) i)) = _
    rw [Fin.sum_univ_succ]
    rfl
  have htail (b : Fin P.1.val) :
      (∑j, physicalTollCost d g m (Z'.paths b.succ j).1) =
        ∑j, physicalTollCost d g m (Z.paths b.succ j).1 := rfl
  have hdtail (b : Fin P.1.val) :
      (∑i, fixedWidthJumpToll B m r τ (Z'.disks b.succ i)) =
        ∑i, fixedWidthJumpToll B m r τ (Z.disks b.succ i) := rfl
  change ((∑b, ((∑j, physicalTollCost d g m (Z'.paths b j).1) +
      ∑i, fixedWidthJumpToll B m r τ (Z'.disks b i))) + ∑i, T (P.2.1 i)) =
    physicalTollCost d g m γ.1 + fixedWidthJumpToll B m r τ V +
      ((∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
        ∑i, fixedWidthJumpToll B m r τ (Z.disks b i))) + ∑i, T (P.2.1 i))
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ]
  rw [hpath, hdisk]
  simp_rw [htail, hdtail]
  ac_rfl

end CircleDomainRigidity

end

end OAI
