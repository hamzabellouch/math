import OAI.Analysis.CircleDomains.Selection.InitialBlockPiece
import OAI.Analysis.CircleDomains.Selection.PrependOldBlockJump
import OAI.Analysis.CircleDomains.Selection.SinglePieceBlock
import OAI.Analysis.CircleDomains.Selection.ReanchorBlockCode

namespace OAI

/-! Domain-endpoint and disk-origin invariants for normalization of mixed
paid chains into grouped jump codes. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

variable {X Y I K : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] {n : ℕ}

def BlockPathsInDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) : Prop :=
  ∀b j, (Z.paths b j).1.val ⊥ ∈ d.quotientDomain ∧ (Z.paths b j).1.val ⊤ ∈ d.quotientDomain

def BlockDisksFrom (d : PathCodeData X Y) (W : K → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) : Prop := ∀b i, ∃k, Z.disks b i = W k

theorem jumpBlockCode_initial_eq
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P)
    {x : X} (hZ : IsJumpBlockCode d ν N B {x} H O P Z) : (Z.paths 0 0).1.val ⊥ = x := by
  have h := (hZ.start 0).1
  simpa only [Fin.castSucc_zero, blockAnchors_zero, mem_singleton_iff] using h

theorem jumpBlockCode_terminal_eq
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P)
    {y : X} (hZ : IsJumpBlockCode d ν N B F {y} O P Z) :
    (Z.paths (Fin.last P.1.val) (Fin.last (P.2.2 (Fin.last P.1.val)).val)).1.val ⊤ = y := by
  have h := (hZ.finish (Fin.last P.1.val)).1
  simpa only [Fin.succ_last, blockAnchors_last, mem_singleton_iff] using h

omit [MeasurableSpace X] in
theorem singlePieceBlock_inDomain (d : PathCodeData X Y) (γ : TaggedPhysicalPath d)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (singlePiecePattern I) (singlePieceBlock d γ) := fun _ _ => ⟨h0, h1⟩

omit [MeasurableSpace X] in
theorem singlePieceBlock_disksFrom (d : PathCodeData X Y) (γ : TaggedPhysicalPath d) (W : K → Set X) :
    BlockDisksFrom d W (singlePiecePattern I) (singlePieceBlock d γ) := fun _ i => Fin.elim0 i

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d P (replaceInitialTruePiece d P Z γ) := by
  intro b
  refine Fin.cases ?_ (fun b j => hZ b.succ j) b
  intro j
  exact Fin.cases ⟨h0, h1⟩ (fun j => hZ 0 j.succ) j

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) : BlockDisksFrom d W P (replaceInitialTruePiece d P Z γ) := hZ

omit [MeasurableSpace X] in
theorem prependNewBlockJump_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d) (V : Set X)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) := by
  intro b
  refine Fin.cases ?_ (fun b j => hZ b.succ j) b
  intro j
  exact Fin.cases ⟨h0, h1⟩ (fun j => hZ 0 j) j

omit [MeasurableSpace X] in
theorem prependNewBlockJump_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) (k : K) :
    BlockDisksFrom d W (prependNewJumpPattern P) (prependNewBlockJump d P Z γ (W k)) := by
  intro b
  refine Fin.cases ?_ (fun b i => hZ b.succ i) b
  intro i
  exact Fin.cases ⟨k, rfl⟩ (fun i => hZ 0 i) i

omit [MeasurableSpace X] in
theorem prependOldBlockJump_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d) (i : I)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  intro b
  exact Fin.cases (fun _ => ⟨h0, h1⟩) (fun b j => hZ b j) b

omit [MeasurableSpace X] in
theorem prependOldBlockJump_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) (i : I) :
    BlockDisksFrom d W (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  intro b
  exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ b j) b

end CircleDomainRigidity

end

end OAI
