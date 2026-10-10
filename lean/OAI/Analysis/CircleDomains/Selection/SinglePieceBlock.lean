import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes

namespace OAI

/-! A single true path as a grouped chain with no old or new jumps. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev singlePiecePattern (I : Type*) : BoundedBlockPattern I 0 :=
  ⟨⟨0, by omega⟩, Fin.elim0, fun _ => ⟨0, by omega⟩⟩

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def singlePieceBlock (d : PathCodeData X Y) (γ : TaggedPhysicalPath d) :
    JumpBlockCode d (singlePiecePattern I) where
  paths := fun _ _ => γ
  disks := fun _ i => Fin.elim0 i

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem singlePieceBlock_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) (γ : TaggedPhysicalPath d)
    (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (hstart : γ.1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hend : γ.1.val ⊤ ∈ H ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F H O (singlePiecePattern I) (singlePieceBlock d γ) := by
  refine ⟨fun _ _ => hγ, ?_, ?_, fun _ i => Fin.elim0 i,
    fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i⟩
  · intro b
    have hb : b = 0 := by
      apply Fin.ext
      have hlt : b.val < 1 := b.isLt
      omega
    subst b
    simpa [singlePieceBlock] using hstart
  · intro b
    have hb : b = 0 := by
      apply Fin.ext
      have hlt : b.val < 1 := b.isLt
      omega
    subst b
    change γ.1.val ⊤ ∈ H ∩ d.quotientDomain
    exact hend

omit [MeasurableSpace X] in
@[simp] theorem singlePieceBlock_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (γ : TaggedPhysicalPath d) :
    jumpBlockCost d B g m r τ T (singlePiecePattern I) (singlePieceBlock d γ) =
      physicalTollCost d g m γ.1 := by
  simp [jumpBlockCost, singlePiecePattern, singlePieceBlock]

end CircleDomainRigidity

end

end OAI
