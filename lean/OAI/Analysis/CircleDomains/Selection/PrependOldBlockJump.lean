import OAI.Analysis.CircleDomains.Selection.PrependNewBlockJump

namespace OAI

/-! Prepend an old jump, creating a new first block with one true piece.
The old disk label and its toll are retained exactly. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev prependOldJumpPattern {I : Type*} {n : ℕ} (P : BoundedBlockPattern I n) (i : I) :
    BoundedBlockPattern I (n+1) :=
  ⟨⟨P.1.val+1, by omega⟩, Fin.cons i P.2.1,
    Fin.cons ⟨0, by omega⟩ (fun b => ⟨(P.2.2 b).val, by omega⟩)⟩

theorem blockAnchors_prependOld_tail {X I : Type*} {n : ℕ}
    (F H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (i : I)
    (k : Fin (P.1.val+2)) :
    blockAnchors F H O (prependOldJumpPattern P i) k.succ = blockAnchors (O i) H O P k := by
  have hlabels : (fun j => O ((prependOldJumpPattern P i).2.1 j)) =
      Fin.cons (O i) (fun j => O (P.2.1 j)) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [blockAnchors, Fin.cons_succ, hlabels]
  rw [← Fin.cons_snoc_eq_snoc_cons]

theorem blockAnchors_change_first_succ {X I : Type*} {n : ℕ}
    (F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (k : Fin (P.1.val+1)) :
    blockAnchors F H O P k.succ = blockAnchors F' H O P k.succ := rfl

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def prependOldBlockJump (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (i : I) :
    JumpBlockCode d (prependOldJumpPattern P i) where
  paths := Fin.cons (fun _ => γ) Z.paths
  disks := Fin.cons Fin.elim0 Z.disks

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem prependOldBlockJump_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (i : I) (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hleft : γ.1.val ⊤ ∈ O i ∩ d.quotientDomain)
    (hright : (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F' H O (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact Fin.cases (fun _ => hγ) (fun b j => hZ.allowed b j) b
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊥ ∈ F' ∩ d.quotientDomain
      exact hstart
    · rw [Fin.castSucc_succ, blockAnchors_prependOld_tail]
      refine Fin.cases ?_ (fun b => ?_) b
      · change (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain
        exact hright
      · change (Z.paths b.succ 0).1.val ⊥ ∈
          blockAnchors (O i) H O P b.succ.castSucc ∩ d.quotientDomain
        rw [blockAnchors_internal]
        have h := hZ.start b.succ
        rw [blockAnchors_internal] at h
        exact h
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊤ ∈ blockAnchors F' H O (prependOldJumpPattern P i) (0 : Fin (P.1.val+2)).succ ∩ _
      rw [blockAnchors_prependOld_tail, blockAnchors_zero]
      exact hleft
    · rw [blockAnchors_prependOld_tail]
      change (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
        blockAnchors (O i) H O P b.succ ∩ d.quotientDomain
      rw [blockAnchors_change_first_succ (O i) F H O P]
      exact hZ.finish b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.left b j) b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.right b j) b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.meets b j) b

omit [MeasurableSpace X] in
theorem prependOldBlockJump_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (i : I) :
    jumpBlockCost d B g m r τ T (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) =
      physicalTollCost d g m γ.1 + T i + jumpBlockCost d B g m r τ T P Z := by
  let Z' := prependOldBlockJump d P Z γ i
  have hpath : (∑j, physicalTollCost d g m (Z'.paths 0 j).1) =
      physicalTollCost d g m γ.1 := by
    change (∑j : Fin 1, physicalTollCost d g m γ.1) = _
    simp
  have hdisk : (∑k, fixedWidthJumpToll B m r τ (Z'.disks 0 k)) = 0 := by
    change (∑k : Fin 0, fixedWidthJumpToll B m r τ (Z'.disks 0 k)) = 0
    simp
  have htail (b : Fin (P.1.val+1)) :
      (∑j, physicalTollCost d g m (Z'.paths b.succ j).1) =
        ∑j, physicalTollCost d g m (Z.paths b j).1 := rfl
  have hdtail (b : Fin (P.1.val+1)) :
      (∑k, fixedWidthJumpToll B m r τ (Z'.disks b.succ k)) =
        ∑k, fixedWidthJumpToll B m r τ (Z.disks b k) := rfl
  have hlabel : (∑k, T ((prependOldJumpPattern P i).2.1 k)) =
      T i + ∑k, T (P.2.1 k) := by
    change (∑k : Fin (P.1.val+1), T ((Fin.cons i P.2.1 : Fin (P.1.val+1) → I) k)) = _
    rw [Fin.sum_univ_succ]
    rfl
  change ((∑b, ((∑j, physicalTollCost d g m (Z'.paths b j).1) +
      ∑k, fixedWidthJumpToll B m r τ (Z'.disks b k))) +
        ∑k, T ((prependOldJumpPattern P i).2.1 k)) =
    physicalTollCost d g m γ.1 + T i +
      ((∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
        ∑k, fixedWidthJumpToll B m r τ (Z.disks b k))) + ∑k, T (P.2.1 k))
  conv_lhs => rw [Fin.sum_univ_succ]
  rw [hpath, hdisk, hlabel]
  simp_rw [htail, hdtail]
  simp only [add_zero]
  ac_rfl

end CircleDomainRigidity

end

end OAI
