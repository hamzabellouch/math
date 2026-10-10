import OAI.Computability.SpaceSimulation.OneTape.Caps
import OAI.Computability.SpaceSimulation.OneTape.Growth

namespace OAI

/-!
One-tape simulation in two-fifths-power space, following OpenAI's
“Simulating One-Tape Time in Two-Fifths-Power Space”. The capped and
unknown-time bounds include all intermediate work storage and keep the
accessor and simulator fixed independently of the input and time cap.
-/

namespace Fifths
namespace Single
open Entry Cost
variable {X : Type} (M : Single X)

/-- Ordinary capped access condition. Log is binary (Cost.Log n =
log base two of (n+2)). Real constants. -/
def Access (A : M.Sym) (p q : ℝ) (x : List X) (T : ℕ) : Prop :=
  ∀ (h : M.Tag) (l : ℤ), Inside T l →
    ∃ s : ℕ, (s:ℝ) ≤ p * (Log T)^q ∧
      A.Within (binaryIn x (M.arg T h l)) (M.sensor x h l) s

/-- Widen all promised runs of the accessor to a pointwise
integer bound. Parameter is integer so tight floors immaterial. -/
theorem accessed (A : M.Sym) (p q : ℝ) (hp : 1 ≤ p) :
    ∃ d c : ℕ, ∀ (x : List X) (T : ℕ), M.Access A p q x T →
      M.Gives A x T (c*(bound d T + 1)) := by
  obtain ⟨d,c,h⟩ := absorbs p q hp
  refine ⟨d,c,?_⟩
  intro x T e g u a
  obtain ⟨s,g,l⟩ := e g u a
  exact l.mono (by exact_mod_cast g.trans (h T))

/-- With binary cap as a separate read-only argument. Single
simulator for all promised input/cap pairs. Real pointwise space
bound (in particular a soft-O bound). `exponent` = 2/5. -/
theorem capped [Fintype X] (A : M.Sym) (p q : ℝ) (hp : 1 ≤ p) (_hq : 1 ≤ q) :
    ∃ (N : TM X Unit M.Outcome) (e : ℕ) (c : ℝ), 0 < c ∧
      ∀ (x : List X) (T : ℕ), 2 ≤ T → M.Access A p q x T →
        ∃ b : ℕ, N.Within (binaryIn x (fun _ => T)) (M.outcome x T) b ∧
          (b:ℝ) ≤ c*(T:ℝ)^exponent*(Log T)^e := by
  classical
  obtain ⟨d,c,H⟩ := M.accessed A p q hp
  let I := {i : List X × ℕ // 2 ≤ i.2 ∧ M.Access A p q i.1 i.2}
  let x := fun i : I => i.val.1
  let T := fun i : I => i.val.2
  let S := fun i : I => bound d (T i)
  let f := fun i : I => M.outcome (x i) (T i)
  let e : M.Outcome ↪ ℕ := ⟨Entry.code,Entry.code_inj _⟩
  have l : Comp x S T (fun i => e (f i)) :=
    M.cappedRegister A d (Comp.refl (capFits d T)) (Scaled.refl S)
      ⟨c,fun i => H (x i) (T i) i.property.2⟩
  obtain ⟨N,u,w⟩ := Comp.withBinary (M.finish M.beginState) e l
  refine ⟨N,d+2,((u:ℝ)+1)*2*factor d,?_,?_⟩
  · have := fpos d; positivity
  intro x t g h
  exact ⟨_,w (⟨(x,t),g,h⟩ : I),scaledReal d u g⟩

/-- Simulator with no cap input, an actual time t being used only
to state the bound. If already halted at t, reports that outcome;
under the promises, halts within the stated space. -/
theorem unknown [Fintype X] (A : M.Sym) (p q : ℝ) (hp : 1 ≤ p) (_hq : 1 ≤ q) :
    ∃ (N : TM X Empty M.Outcome) (e : ℕ) (c : ℝ), 0 < c ∧
      ∀ (x : List X), (∀ T, 2 ≤ T → M.Access A p q x T) →
        ∀ (t : ℕ), (M.outcome x t).2 = true →
          ∃ b, N.Within (files x) (M.outcome x t) b ∧
            (b:ℝ) ≤ c*((t:ℝ)+2)^exponent*(Log t)^e := by
  classical
  obtain ⟨d,c,H⟩ := M.accessed A p q hp
  let I := {i : List X × ℕ //
    (∀ T, 2 ≤ T → M.Access A p q i.1 T) ∧ (M.outcome i.1 i.2).2 = true}
  let x := fun i : I => i.val.1
  let t := fun i : I => i.val.2
  let S := fun i : I => bound d (t i + 2)
  let f := fun i : I => M.outcome (x i) (t i)
  let e : M.Outcome ↪ ℕ := ⟨Entry.code,Entry.code_inj _⟩
  have l : Comp x S (fun _ => 0) (fun i => e (f i)) :=
    M.noCapRegister A d c (fun i : I => i.property.2)
      (fun (i : I) T p => H (x i) T (i.property.1 T p))
  obtain ⟨N,u,w⟩ := Comp.withoutBinary (M.finish M.beginState) e l
  refine ⟨N,d+2,((u:ℝ)+1)*2*factor d*2^(d+2),?_,?_⟩
  · have := fpos d; positivity
  intro x h t q
  exact ⟨_,w (⟨(x,t),h,q⟩ : I),scaledShift d u t⟩

end Single
end Fifths

end OAI
