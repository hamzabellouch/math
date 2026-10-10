import OAI.Computability.SpaceSimulation.Evaluation.Ready

namespace OAI

namespace Fifths
namespace Circuit
namespace Ready
open Modulus Bin Fifths.Comp
variable {I U X : Type}

section
variable {C : I → Circuit} {x : I → List X} {S a : I → ℕ}
  {R : ∀ i, (C i).Pool} {f g : ∀ i, (C i).Frame}

theorem endCode (r : Comp x S a (fun i => (C i).packPool (R i))) :
    Comp x S a (fun i => (C i).flow.packMove ((R i),FlowMove.finish)) :=
  r.pair ((Comp.constant r.source 0).pair
    ((Comp.constant r.source 0).pair (Comp.constant r.source 0)))

theorem carryCode (r : Comp x S a (fun i => (C i).packPool (R i)))
    (s : Comp x S a (fun i => (C i).packFrame (f i))) :
    Comp x S a (fun i => (C i).flow.packMove ((R i),FlowMove.cont (f i))) := by
  change Comp x S a (fun i => Bin.pair ((C i).packPool (R i)) (Bin.pair 1
    (Bin.pair ((C i).packFrame (f i)) 0)))
  exact r.pair ((Comp.constant r.source 1).pair (s.pair (Comp.constant r.source 0)))

theorem callCode (r : Comp x S a (fun i => (C i).packPool (R i)))
    (s : Comp x S a (fun i => (C i).packFrame (f i)))
    (t : Comp x S a (fun i => (C i).packFrame (g i))) :
    Comp x S a (fun i => (C i).flow.packMove ((R i),FlowMove.call (f i) (g i))) := by
  simp only [Flow.packMove,Flow.tag,Flow.arg1,Flow.arg2,flow]
  exact r.pair ((Comp.constant r.source 2).pair (s.pair t))
end

section
variable {C : I → Circuit} {x : I → List X} {S cp : I → ℕ}
set_option maxHeartbeats 1500000 in
theorem byPc (b : Ready C x S cp) (ok : ∀ i, (C i).Good)
    (r : U → I) (a : U → ℕ)
    (R : ∀ i, (C (r i)).Pool) (f : ∀ i, (C (r i)).Frame)
    (CP : ReComp x S r a (fun i => cp (r i)))
    (RC : ReComp x S r a (fun i => (C (r i)).packPool (R i)))
    (FC : ReComp x S r a (fun i => (C (r i)).packFrame (f i)))
    (k : Pc) :
    ReComp x S r a (fun i => (C (r i)).flow.packMove ((C (r i)).atPc (R i) (f i) k)) := by
  let D := fun i => C (r i)
  let Q := fun i => (f i).x
  let M := ReComp x S r a
  let sc := fun i => (f i).s.val
  let z := fun i => (f i).z.val
  let y := fun i => (f i).y.val
  let j := fun i => (f i).i.val
  let t := fun i => (f i).r.val
  have fr : M (fun i => (D i).packX (Q i)) := Comp.left FC
  have w₁ : M sc := Comp.left (Comp.right (Comp.right FC))
  have f₂ := Comp.right (Comp.right (Comp.right FC))
  have w₂ : M z := f₂.left
  have w₃ : M y := f₂.right.left
  have w₄ : M j := f₂.right.right.left
  have w₅ : M t := f₂.right.right.right.left
  have w₆ := f₂.right.right.right.right.left
  have w₇ := f₂.right.right.right.right.right
  have p := Comp.trans CP (b.modulusN.pull r)
  have pn := Comp.trans CP (b.countOf.pull r)
  have q := Comp.trans CP (b.widthOf.pull r)
  have vv := b.fitRegisters.pull r
  have origin : M (fun _ => 0) := Comp.constant p.source 0
  have zero := valZero p
  have e0 (v : ∀ i : U, (D i).Request)
      (l : M (fun i => (D i).packX (v i))) :
      M (fun i => (D i).packFrame ((D i).fEntry (v i))) :=
    formComp vv p q _ l pn origin origin origin origin origin zero zero
  let u0 := fun i => (Q i).node
  have kT := Comp.left fr
  have kN := Comp.left (Comp.right fr)
  have HH := slotMap Slot.H kT
  have AA := slotMap Slot.A kT
  have np := b.nav r u0 CP kN
  have psc := valCast p w₁
  have pr := valCast p w₅
  have B₁ : ∀ i, z i ≤ (D i).width+1 := fun i => Nat.le_of_lt_succ (f i).z.isLt
  have B₂ : ∀ i, y i ≤ 2^(D i).width := fun i => Nat.le_of_lt_succ (f i).y.isLt
  have B₃ : ∀ i, j i ≤ (D i).count := fun i => Nat.le_of_lt_succ (f i).i.isLt
  have A := b.children r u0 _ CP kN w₄ B₃
  cases k with
  | entry =>
    have inc := jump vv p q (Comp.right (Comp.right fr)) np.2.2.2
    have rt := plusComp vv p q RC kT inc
    have e := formComp vv p q .outer fr pn origin origin origin origin origin zero zero
    have v := Comp.iteB np.1 (endCode rt) (carryCode RC e)
    apply v.congr
    intro i
    change (if (D i).base (Q i).node then _ else _) =
      (D i).flow.packMove ((D i).atPc (R i) (f i) _)
    cases h : (D i).base (Q i).node <;>
      (simp only [h,Bool.false_eq_true,↓reduceIte,atPc,Q] at *; rfl)
  | outer =>
    have h := e0 (fun i => (Q i).otherH (sc i)) (HH.pair (Comp.pair np.2.2.1 psc))
    have g := formComp vv p q .coord fr pn w₁ origin origin origin origin zero zero
    have v := Comp.iteB (Comp.lt w₁ p) (callCode RC h g) (endCode RC)
    apply v.congr
    intro i
    dsimp only [atPc]
    split <;> rename_i ex
    · split
      · rfl
      · rename_i ho
        exact (ho (of_decide_eq_true ex)).elim
    · split
      · rename_i ho
        exact (ex (decide_eq_true ho)).elim
      · rfl
  | coord =>
    have h := e0 (fun i => ((Q i).otherH (sc i)).undo)
      (HH.pair (Comp.pair np.2.2.1 (fieldNeg p psc)))
    have g := formComp vv p q .guess fr pn w₁ w₂ origin origin origin zero zero
    have l := formComp vv p q .outer fr pn (Comp.plus1 w₁) origin origin origin origin zero zero
    have v := Comp.iteB (Comp.lt w₂ q.plus1) (carryCode RC g) (callCode RC h l)
    refine v.congr (fun i => ?_)
    dsimp only [atPc]
    split <;> rename_i ex
    · split
      · rfl
      · rename_i ho
        exact (ho (of_decide_eq_true ex)).elim
    · split
      · rename_i ho
        exact (ex (decide_eq_true ho)).elim
      · rfl
  | guess =>
    have fs := chooseSlot RC HH
    have h : M (fun i => ((D i).EG (u0 i) (z i) (y i)
        (R i (Slot.H (Q i).target))).val) := by
      apply lookupOne vv p q (fun i => (D i).G (u0 i) (z i) (y i)) fs
      intro V k e j P Q w
      exact valCast (P.trans (p.pull k))
        (b.proposeOf (fun i => r (k i)) (fun i => u0 (k i)) _ _ _
          (Comp.trans P (Comp.pull CP k)) (P.trans (kN.pull k))
          (P.trans (Comp.pull w₂ k)) (P.trans (Comp.pull w₃ k)) Q
          (fun i => B₁ (k i)) (fun i => B₂ (k i)) w)
    have e := formComp vv p q .factor fr pn w₁ w₂ w₃ origin origin h zero
    have l := formComp vv p q .coord fr pn w₁ (Comp.plus1 w₂) origin origin origin zero zero
    have powb := (Comp.constant p.source 2).pow np.2.1 ((fitBitsD vv).mono
      (fun i => Nat.pow_le_pow_right (by omega) ((ok (r i)).small (u0 i))))
    apply (Comp.iteB (Comp.lt w₃ powb) (carryCode RC e) (carryCode RC l)).congr
    intro i
    dsimp only [atPc]
    split <;> rename_i ex
    · split
      · rfl
      · rename_i ho
        exact (ho (of_decide_eq_true ex)).elim
    · split
      · rename_i ho
        exact (ex (decide_eq_true ho)).elim
      · rfl
  | factor =>
    have v := formComp vv p q .sample fr pn w₁ w₂ w₃ w₄ origin w₆ zero
    have w := fieldNeg p (fieldPow p psc (p.minus1.sub
      (Comp.trans CP (b.uniformDegree.pull r))))
    have h := fieldMul p (fieldMul p (Comp.right (Comp.right fr)) w) w₆
    have f := formComp vv p q .guess fr pn w₁ w₂ (Comp.plus1 w₃) origin origin zero zero
    apply (Comp.iteB (Comp.lt w₄ pn) (carryCode RC v)
      (carryCode (plusComp vv p q RC kT (jumpOne vv p q h w₂)) f)).congr
    intro i
    dsimp only [atPc]
    split <;> rename_i ex
    · split
      · rfl
      · rename_i ho
        exact (ho (of_decide_eq_true ex)).elim
    · split
      · rename_i ho
        exact (ex (decide_eq_true ho)).elim
      · rfl
  | sample =>
    have g := e0 (fun i => (Q i).otherA (j i) (t i)) (AA.pair (Comp.pair A pr))
    have h := formComp vv p q .checkA fr pn w₁ w₂ w₃ w₄ w₅ w₆ w₇
    have l := formComp vv p q .factor fr pn w₁ w₂ w₃ (Comp.plus1 w₄) origin
      (fieldMul p w₆ w₇) zero
    apply (Comp.iteB (Comp.lt w₅ p) (callCode RC g h) (carryCode RC l)).congr
    intro i
    dsimp only [atPc]
    split <;> rename_i ex
    · split
      · rfl
      · rename_i ho
        exact (ho (of_decide_eq_true ex)).elim
    · split
      · rename_i ho
        exact (ex (decide_eq_true ho)).elim
      · rfl
  | checkA =>
    have fs := chooseSlot RC HH
    have fa := chooseSlot RC AA
    have h : M (fun i => ((D i).ET (u0 i) (z i) (y i) (j i)
        (R i (Slot.H (Q i).target)) (R i (Slot.A (Q i).target))).val) := by
      apply lookupTwo vv p q (fun i => (D i).test (u0 i) (z i) (y i) (j i)) fs fa
      intro V k e u v P Q t l c
      exact valCast (P.trans (p.pull k))
        (b.allowOf (fun i => r (k i)) (fun i => u0 (k i)) _ _ _ _ _
          (Comp.trans P (Comp.pull CP k)) (P.trans (kN.pull k))
          (P.trans (Comp.pull w₂ k)) (P.trans (Comp.pull w₃ k)) (P.trans (Comp.pull w₄ k))
          Q t (fun i => B₁ (k i)) (fun i => B₂ (k i)) (fun i => B₃ (k i)) l c)
    have w := fieldNeg p (fieldPow p pr (p.minus1.sub q))
    have l := formComp vv p q .sample fr pn w₁ w₂ w₃ w₄ (Comp.plus1 w₅) w₆
      (fieldAdd p w₇ (fieldMul p w h))
    have g := e0 (fun i => ((Q i).otherA (j i) (t i)).undo)
      (AA.pair (Comp.pair A (fieldNeg p pr)))
    exact callCode RC g l
end
end Ready
end Circuit
end Fifths

end OAI
