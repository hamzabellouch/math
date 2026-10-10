import OAI.Computability.SpaceSimulation.Register.Comp
import OAI.Computability.SpaceSimulation.Stack.PortIO
import OAI.Computability.SpaceSimulation.Stack.ToTM

namespace OAI

namespace Fifths
variable {X I J K Y : Type}

/-- Arguments individually binary. -/
def binaryIn (pub : List X) (f : J → ℕ) : Inputs X J :=
  ⟨pub, fun j => (f j).bits⟩

namespace SM
open Bin

-- From an injective natural coding on a fixed finite alphabet.
noncomputable def decode (base : Y) (e : Y ↪ ℕ) (l : List Bool) : Y := by
  classical exact if h : ∃ y, e y = val l then Classical.choose h else base

theorem decode_code (base : Y) (e : Y ↪ ℕ) (y : Y) :
    decode base e (e y).bits = y := by
  classical
  unfold decode
  split
  next h => exact e.injective ((Classical.choose_spec h).trans (val_bits _))
  next h => exact (h ⟨y,(val_bits _).symm⟩).elim

def charLength [Fintype Y] (e : Y → ℕ) :=
  ∑ y : Y, (e y).size
theorem char_le [Fintype Y] (e : Y → ℕ) (y) : (e y).size ≤ charLength e :=
  Finset.single_le_sum (f := fun y => (e y).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

noncomputable def emit [DecidableEq K] [Fintype Y] (k : K) (base : Y) (e : Y ↪ ℕ) :
    SM X J K Y :=
  understand k (charLength e) (decode base e)

theorem exec_emit [DecidableEq K] [Fintype Y] (k : K) {i : Inputs X J} {s : Store J K}
    (base : Y) (e : Y ↪ ℕ) (y : Y) (h : s.st k = (e y).bits)
    {B} (o : s.ok B) : (emit k base e).Exec i B s (s.set k []) y := by
  have a : (s.st k).length ≤ charLength e := by rw [h,Nat.size_eq_bits_len]; exact char_le _ _
  unfold emit
  simpa only [h, decode_code] using exec_understand (i := i) k _ (decode base e) o a

/-- Uniform conversion with new constant. -/
theorem scaledTM [Fintype K] (M : SM X J K Y) {x : I → Inputs X J} {y : I → Y}
    {S : I → ℕ} (c : ℕ)
    (r : ∀ i, ∃ t, M.Exec (x i) (c*(S i+1)) (.init (fun _ => [])) t (y i)) :
    ∃ d, ∀ i, M.toTM.Within (x i) (y i) (d*(S i+1)) := by
  let q := M.multiplier
  refine ⟨q*(c+1), fun i => ?_⟩
  obtain ⟨t,h⟩ := r i
  apply (M.toTM_within h).mono
  change q * (c*(S i+1)+1) ≤ q*(c+1)*(S i+1)
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  rw [add_mul]; omega
end SM

namespace Comp
open Bin Function
variable [Fintype Y] {x : I → List X} {y : I → Y} {S a : I → ℕ}

/-- Binary result of a uniform register computation can also be
returned directly in finite control. -/
theorem withBinary (base : Y) (d : Y ↪ ℕ) (h : Comp x S a (fun i => d (y i))) :
    ∃ (M : TM X Unit Y) (c : ℕ), ∀ i,
      M.Within (binaryIn (x i) (fun _ => a i)) (y i) (c*(S i+1)) := by
  classical
  obtain ⟨K,p,M,c,r⟩ := h
  have := p
  let k : Unit ⊕ K := .inl ()
  let N := (SM.loader k).seq ((M.withArgs Unit).seq (SM.emit k base d))
  refine ⟨N.toTM, SM.scaledTM N c (fun i => ?_)⟩
  let u := binaryIn (x i) (fun (_ : Unit) => a i)
  let B := c*(S i+1)
  have g : (M.withArgs Unit).Exec u B
      (SM.storeArgs (J := Unit) (fun _ => 0) (singleton K (a i)))
      (SM.storeArgs (J := Unit) (fun _ => 0) (singleton K (d (y i)))) () :=
    M.args_exec (fun _ => 0) (r i)
  have v := SM.exec_loader u k (show (u.arg ()).length ≤ B from g.startOk k)
  have e : SM.just k (u.arg ()) 0 = SM.storeArgs (J := Unit) (fun _ => 0) (singleton K (a i)) := by
    refine Store.ext' rfl ?_
    rintro (t|t)
    · cases t; simp only [SM.just, k, ↓reduceIte]
      rfl
    · simp only [SM.just, k, Sum.inr_ne_inl, ite_false]
      rfl
  rw [e] at v
  exact ⟨_,SM.exec_seq v (SM.exec_seq g (SM.exec_emit k base d _ rfl g.endOk))⟩

theorem withoutBinary (base : Y) (d : Y ↪ ℕ)
    (h : Comp x S (fun _ => 0) (fun i => d (y i))) :
    ∃ (M : TM X Empty Y) (c : ℕ), ∀ i, M.Within (files (x i)) (y i) (c*(S i+1)) := by
  classical
  obtain ⟨K,p,M,c,r⟩ := h
  have := p
  let k : Unit ⊕ K := .inl ()
  let N := M.seq (SM.emit k base d)
  refine ⟨N.toTM, SM.scaledTM N c (fun i => ?_)⟩
  have e : singleton K 0 = Store.init (fun _ => []) := by
    refine Store.ext' rfl ?_
    rintro (t|t) <;> simp [Fifths.Comp.singleton,file,Store.init,Store.extra]
  rw [← e]
  exact ⟨_, SM.exec_seq (r i) (SM.exec_emit k base d _ rfl (r i).endOk)⟩
end Comp
end Fifths

end OAI
