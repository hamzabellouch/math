import OAI.Computability.SpaceSimulation.Evaluation.Next
import OAI.Computability.SpaceSimulation.Evaluation.Schedule

namespace OAI

namespace Fifths
namespace Circuit
open Bin Fifths.Comp Modulus
variable {I X : Type} {C : I → Circuit} {x : I → List X} {S cp : I → ℕ}

set_option maxHeartbeats 300000
attribute [local irreducible] Bin.pair Modulus.chosen
private theorem pic : Function.Injective Pc.code := by
  intro a b h
  cases a <;> cases b <;> simp_all only [Pc.code] <;> contradiction

theorem Ready.flow_uniform (c : Ready C x S cp) (g : ∀ i, (C i).Good) :
    Flow.uniform (fun i => (C i).flow) x S cp := by
  let v := Flow.Points (fun i => (C i).flow)
  let r := fun i : v => i.1
  let D := fun i : v => C (r i)
  let R : ∀ i : v, (D i).Pool := fun i => i.2.1
  let f : ∀ i : v, (D i).Frame := fun i => i.2.2
  let a := fun i : v => (D i).flow.input (cp (r i)) (R i) (f i)
  have s : Fits (fun i : v => S (r i)) a :=
    (c.widthOf.source.pull r).pair ((c.poolSpace R).pair (c.frameSpace f))
  have h := Comp.refl (x := fun i => x (r i)) s
  have p₁ : Comp.ReComp x S r a (fun i => cp (r i)) := h.left
  have p₂ : Comp.ReComp x S r a (fun i => (D i).packPool (R i)) := h.right.left
  have p₃ : Comp.ReComp x S r a (fun i => (D i).packFrame (f i)) := h.right.right
  have z : ReComp x S r a (fun i => (f i).pc.code) := Comp.left (Comp.right p₃)
  exact chooseCase Pc.code pic
    (fun i k => (D i).flow.packMove ((D i).atPc (R i) (f i) k))
    z (fun k => c.byPc g _ _ _ _ p₁ p₂ p₃ k)

/-- Compute the designated word using only the requested budget.
All sizes in `Ready`, `Scaled` and `Comp` are uniform. -/
theorem evaluate (c : Ready C x S cp) (g : ∀ i, (C i).Good)
    (B : ∀ i, (C i).Node → ℕ) (funding : ∀ i, (C i).Meter (B i))
    (v : ∀ i, (C i).Node)
    (w : Comp x S cp (fun i => (v i).val))
    (h : Scaled S (fun i => B i (v i))) :
    Comp x S cp (fun i => (C i).semantic (v i)) := by
  let q : ∀ i, (C i).Request := fun i => ⟨v i,1,0⟩
  let R : ∀ i, (C i).Pool := fun _ _ _ => 0
  let f := fun i => (C i).fEntry (q i)
  let t := fun i => (q i).result (R i)
  have e := Flow.uniform_result (c.flow_uniform g) R t f _ h
    (fun i => (C i).answers (B i) (g i) (funding i) (v i) (q i) rfl (R i))
  let P := fun i => (C i).P
  have cp₁ := c.modulusN
  have d := c.fitRegisters
  have b : Comp x S cp (fun i => (C i).packPool (R i)) := by
    apply combinePool
    intro s
    apply vector d cp₁ c.widthOf _
    intro U r a j v _ _
    exact valZero (Comp.trans v (cp₁.pull r))
  have o := Comp.constant (x := x) w.source 0
  have m : Comp x S cp (fun i => (C i).packX (q i)) :=
    o.pair (w.pair (valOne cp₁))
  have f₁ : Comp x S cp (fun i => (C i).packFrame (f i)) :=
    formComp d cp₁ c.widthOf _ m c.countOf o o o o o (valZero cp₁) (valZero cp₁)
  have s₁ : Comp x S cp (fun i => (C i).flow.input (cp i) (R i) (f i)) :=
    (Comp.refl w.source).pair (b.pair f₁)
  have m₀ : Comp x S cp (fun i => (C i).packPool (t i)) :=
    s₁.trans e
  have L (i : I) (k : ℕ) : t i 0 k =
      (C i).P.aug (C i).width ((C i).semantic (v i)) k := by
    simp [q,R,t,Request.result,plus,multiple,value]
  have H : Comp x S cp (fun i => Radix.pack 2 (fun k => (t i 0 k).val) (C i).width) := by
    refine digits (Comp.constant w.source 2) c.widthOf (fitBitsD d)
      (fun i => by omega) (fun i k => (t i 0 k).val)
      (fun i k _ => ?_) ?_
    · rw [L, aug_val]; exact aug_bounded ..
    · intro e g v
      let a := fun i : Before (fun i => (C i).width) => i.1.1
      exact coord (d.pull a) (g.trans (cp₁.pull a))
        (g.trans ((which m₀ 0).pull a)) v (fun i => i.2.le)
  exact H.congr fun i => by simp [L, Modulus.fromAug,(g i).bounded]

end Circuit
end Fifths

end OAI
