import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes
import OAI.Analysis.CircleDomains.Modulus.JoinedDomainCost

namespace OAI

/-! Replace the first true piece of a grouped chain. This operation is
used when consecutive true edges are joined during chain normalization. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def replaceInitialTruePiece (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) : JumpBlockCode d P where
  paths := Fin.cons (Fin.cons γ (fun j => Z.paths 0 j.succ)) (fun b => Z.paths b.succ)
  disks := Z.disks

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem replaceInitialTruePiece_end (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d)
    (hend : γ.1.val ⊤ = (Z.paths 0 0).1.val ⊤) :
    ∀b j, ((replaceInitialTruePiece d P Z γ).paths b j).1.val ⊤ = (Z.paths b j).1.val ⊤ := by
  intro b
  refine Fin.cases ?_ (fun b j => ?_) b
  · intro j
    exact Fin.cases hend (fun _ => rfl) j
  · rfl

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem replaceInitialTruePiece_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hend : γ.1.val ⊤ = (Z.paths 0 0).1.val ⊤) :
    IsJumpBlockCode d ν N B F' H O P (replaceInitialTruePiece d P Z γ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hZ.meets⟩
  · intro b
    refine Fin.cases ?_ (fun b j => hZ.allowed b.succ j) b
    intro j
    exact Fin.cases hγ (fun j => hZ.allowed 0 j.succ) j
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa [replaceInitialTruePiece] using hstart
    · simpa only [replaceInitialTruePiece, Fin.cons_succ, Fin.castSucc_succ,
        blockAnchors, Fin.cons_succ] using hZ.start b.succ
  · intro b
    rw [replaceInitialTruePiece_end d P Z γ hend]
    simpa only [blockAnchors, Fin.cons_succ] using hZ.finish b
  · intro b i
    rw [replaceInitialTruePiece_end d P Z γ hend]
    exact hZ.left b i
  · intro b
    refine Fin.cases (fun i => ?_) (fun b i => hZ.right b.succ i) b
    exact hZ.right 0 i

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (a : ℝ≥0∞)
    (hc : physicalTollCost d g m γ.1 = a + physicalTollCost d g m (Z.paths 0 0).1) :
    jumpBlockCost d B g m r τ T P (replaceInitialTruePiece d P Z γ) =
      a + jumpBlockCost d B g m r τ T P Z := by
  simp only [jumpBlockCost, replaceInitialTruePiece, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rw [hc]
  ac_rfl

end CircleDomainRigidity

end

end OAI
