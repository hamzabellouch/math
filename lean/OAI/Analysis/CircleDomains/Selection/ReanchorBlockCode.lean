import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes

namespace OAI

/-! The outer anchors of a grouped chain may be changed when its actual
first and last endpoints lie in the new anchors. Internal jumps are untouched. -/

open Set MeasureTheory

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] {n : ℕ}

theorem reanchor_jumpBlockCode
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H F' H' : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (hstart : (Z.paths 0 0).1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hend : (Z.paths (Fin.last P.1.val) (Fin.last (P.2.2 (Fin.last P.1.val)).val)).1.val ⊤ ∈
      H' ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F' H' O P Z := by
  refine ⟨hZ.allowed, ?_, ?_, hZ.left, hZ.right, hZ.meets⟩
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa using hstart
    · rw [blockAnchors_internal]
      have h := hZ.start b.succ
      rw [blockAnchors_internal] at h
      exact h
  · intro b
    refine Fin.lastCases ?_ (fun b => ?_) b
    · simpa only [Fin.succ_last, blockAnchors_last] using hend
    · rw [Fin.succ_castSucc, blockAnchors_internal]
      have h := hZ.finish b.castSucc
      rw [Fin.succ_castSucc, blockAnchors_internal] at h
      exact h

end CircleDomainRigidity

end OAI
