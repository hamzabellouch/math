import OAI.Computability.SpaceSimulation.Register.Comp

namespace OAI

/-! Conditional and iteration rules. Iteration does not require a
computable iteration bound. Needs a uniform continuation check. -/

namespace Fifths
variable {X I : Type}

namespace Comp
variable {x : I → List X} {S a b c : I → ℕ} {B : I → Bool}

/-- Get a finite truth flag without erasing the register argument.
Pair the computed boolean and the argument; check first bit for zero
of first paired natural. -/
theorem flag (h : Comp x S a (fun i => (B i).toNat)) :
    Works (fun i => files (x i)) S (fun i => file (a i)) (fun i => file (a i)) B := by
  have g := h.pair (Comp.refl h.source)
  let k : Unit ⊕ Unit := .inl ()
  let t : Unit ⊕ Unit := .inr ()
  let f := fun i => Bin.pair (B i).toNat (a i)
  let M : SM X Empty (Unit ⊕ Unit) Bool :=
    (SM.peek (fun _ s => s k == some false)).bind fun y =>
      (SM.projS k t).seq (SM.pure y)
  refine Works.seq (b := fun i => file (f i)) g ?_
  obtain ⟨d,r⟩ := g.target
  refine ⟨Unit,inferInstance,M,d,fun i => ?_⟩
  let v := singleton Unit (f i)
  let n := d*(S i+1)
  let w := singleton Unit (a i)
  have o : v.ok n := Store.ok_extra.mpr (file_ok.mpr (r i))
  have e : v.st k = Bin.frame (B i).toNat.bits (a i).bits := Bin.pair_bits ..
  have b : (v.see k == some false) = B i := by
    unfold Store.see
    rw [e]; cases B i <;> simp
  have p := SM.exec_projS (i := files (x i)) k t (by simp [k,t]) o _ _ e rfl
  have j : v.set k (a i).bits = w := singleton_set Unit _ _
  rw [j] at p
  have u : (SM.peek (fun (_ : Reads X Empty) (s : Unit ⊕ Unit → Option Bool) =>
      s k == some false)).Exec (files (x i)) n v v (B i) := b ▸ SM.exec_peek o
  show M.Exec (files (x i)) _ v w _
  unfold M
  refine SM.exec_bind _ _ u (SM.exec_seq p (SM.exec_pure p.endOk))

theorem casesB (h : Comp x S a (fun i => (B i).toNat))
    (yes : Comp (fun i : {i // B i = true} => x i) (fun i => S i)
      (fun i => a i) (fun i => b i))
    (no : Comp (fun i : {i // B i = false} => x i) (fun i => S i)
      (fun i => a i) (fun i => b i)) :
    Comp x S a b :=
  Works.branch h.flag yes no

theorem iteB (h : Comp x S a (fun i => (B i).toNat))
    (yes : Comp x S a b) (no : Comp x S a c) :
    Comp x S a (fun i => if B i then b i else c i) := by
  apply h.casesB
  · exact (yes.pull _).congr (fun i => by simp [i.property])
  · exact (no.pull _).congr (fun i => by simp [i.property])

end Comp

/-- Iterates before and through stop. -/
abbrev Before (n : I → ℕ) := { v : I × ℕ // v.2 < n v.1 }
abbrev Through (n : I → ℕ) := { v : I × ℕ // v.2 ≤ n v.1 }

namespace Works
theorem fixed {X J I L Y : Type} {u : I → Inputs X J} {S : I → ℕ}
    {s : I → Store J L} (h : FitsStore S s) (y : Y) :
    Works u S s s (fun _ => y) := by
  obtain ⟨d,r⟩ := h
  exact Works.direct (SM.pure y) _ (fun i => SM.exec_pure (r i))

theorem eq_targets {X J I L Y : Type} {u : I → Inputs X J} {S : I → ℕ}
    {s t w : I → Store J L} {y v : I → Y} (h : Works u S s t y)
    (f : ∀ i, t i = w i) (g : ∀ i, y i = v i) :
    Works u S s w v := by rwa [← funext f, ← funext g]
end Works

namespace Comp
variable {x : I → List X} {S : I → ℕ}

theorem loop (n : I → ℕ) (v : I → ℕ → ℕ)
    (step : Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1)
      (fun i => v i.1.1 i.1.2) (fun i => v i.1.1 (i.1.2+1)))
    (keep : Comp (fun i : Through n => x i.1.1) (fun i => S i.1.1)
      (fun i => v i.1.1 i.1.2)
      (fun i => (decide (i.1.2 < n i.1.1)).toNat)) :
    Comp x S (fun i => v i 0) (fun i => v i (n i)) := by
  let b : Through n → Bool := fun i => decide (i.1.2 < n i.1.1)
  let s : Through n → Store Empty Unit := fun i => file (v i.1.1 i.1.2)
  let w : Through n → Store Empty Unit :=
    fun i => file (if b i then v i.1.1 (i.1.2 + 1) else v i.1.1 i.1.2)
  let y : Through n → Option Unit := fun i => if b i then none else some ()
  let u := fun (i : Through n) => files (x i.1.1)
  let d := fun (i : Through n) => S i.1.1
  have body : Works u d s w y := by
    have guard : Works u d s s b := keep.flag
    refine Works.branch guard ?_ ?_
    · let e : {i // b i = true} → Before n := fun i =>
        ⟨i.1.1, of_decide_eq_true i.2⟩
      have p := step.pull e
      have g : Works (fun i : {i // b i = true} => u i) (fun i => d i) (fun i => s i)
          (fun i => file (v (e i).1.1 ((e i).1.2 + 1))) (fun _ => ()) := p
      exact (Works.seq g (Works.fixed g.target (none : Option Unit))).eq_targets
        (fun i => by simp [w,i.2,e]) (fun i => by simp [y,i.2])
    · have p := guard.pull (fun i : {i // b i = false} => i.val)
      exact (Works.fixed (u := fun i : {i // b i = false} => u i)
        p.target (some ())).eq_targets (fun i => by simp [s,w,i.2])
          (fun i => by simp [y,i.2])
  obtain ⟨K,h,M,c,r⟩ := body
  refine ⟨K,h,M.loop,c,fun i => ?_⟩
  suffices a : ∀ l j, j+l = n i →
      M.loop.Exec (files (x i)) (c*(S i+1))
        (singleton K (v i j)) (singleton K (v i (n i))) () from a (n i) 0 (by omega)
  intro l
  induction l with
  | zero =>
    intro j eqn
    have g : j = n i := by simpa using eqn
    subst j
    exact M.loop_stop (show M.Exec _ _ _ _ (some ()) from by
      simpa [u,b,d,s,w,y,singleton] using r ⟨(i,n i), le_rfl⟩)
  | succ l ih =>
    intro j eqn
    have e : j < n i := by omega
    refine M.loop_continue ?_ (ih (j+1) (by omega))
    simpa [u,b,d,s,w,y,singleton,e] using r ⟨(i,j), e.le⟩

end Comp
end Fifths

end OAI
