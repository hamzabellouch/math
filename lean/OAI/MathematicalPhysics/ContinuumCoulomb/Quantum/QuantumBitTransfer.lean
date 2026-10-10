import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TM2Composition

namespace OAI

/-! Transfer a bit-coded word between the verifier machine and the Boolean
prefix tapes. Only the bit register is added to the finite control. -/

namespace ContinuumCoulomb.QuantumBitTransfer
open Turing
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def loop (src dst : K) (read : Γ src → Bool) (write : Bool → Γ dst)
    (label : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option Bool) :=
  .pop src (fun s h => (s.1,h.map read))
    (.branch (fun s => s.2.isSome)
      (.push dst (fun s => write (s.2.getD false)) (.goto fun _ => label))
      (match exit with | none => .halt | some l => .goto fun _ => l))

private theorem update_src (src dst : K) (hne : src ≠ dst)
    (base : ∀ k, List (Γ k)) (xs ys : List (Γ src)) (zs : List (Γ dst)) :
    Function.update (tapesAt src dst base xs zs) src ys = tapesAt src dst base ys zs := by
  funext k
  by_cases hs : k=src
  · subst k
    simp [tapesAt,hne]
  · by_cases hd : k=dst
    · subst k
      simp [tapesAt,Ne.symm hne]
    · simp [tapesAt,hs,hd]

private theorem update_dst (src dst : K) (base : ∀ k, List (Γ k))
    (xs : List (Γ src)) (ys zs : List (Γ dst)) :
    Function.update (tapesAt src dst base xs ys) dst zs = tapesAt src dst base xs zs := by
  funext k
  by_cases h : k=dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt,h]

theorem step_empty (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (ys : List (Γ dst)) (state : σ) (r : Option Bool) :
    TM2.step program ⟨some label,(state,r),tapesAt src dst base [] ys⟩=
      some ⟨exit,(state,none),tapesAt src dst base [] ys⟩ := by
  change some (TM2.stepAux (program label) _ _)=_
  rw [hl]
  cases exit <;> simp [loop,TM2.stepAux,tapesAt_src,hne,update_src]

theorem step_cons (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (x : Γ src) (xs : List (Γ src)) (ys : List (Γ dst))
    (state : σ) (r : Option Bool) :
    TM2.step program ⟨some label,(state,r),tapesAt src dst base (x::xs) ys⟩=
      some ⟨some label,(state,some (read x)),
        tapesAt src dst base xs (write (read x)::ys)⟩ := by
  change some (TM2.stepAux (program label) _ _)=_
  rw [hl]
  simp [loop,TM2.stepAux,tapesAt_src,tapesAt_dst,hne,update_src,update_dst]

theorem transfer_steps (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (xs : List (Γ src)) (ys : List (Γ dst))
    (state : σ) (r : Option Bool) :
    (fun c => c.bind (TM2.step program))^[xs.length+1]
      (some ⟨some label,(state,r),tapesAt src dst base xs ys⟩)=
      some ⟨exit,(state,none),
        tapesAt src dst base [] (xs.reverse.map (write ∘ read)++ys)⟩ := by
  induction xs generalizing ys r with
  | nil =>
    simpa only [List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some,
      List.reverse_nil,List.map_nil,List.nil_append] using
      step_empty src dst hne read write label exit program hl base ys state r
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (fun c => c.bind (TM2.step program))^[xs.length+1]
      (TM2.step program ⟨some label,(state,r),tapesAt src dst base (x::xs) ys⟩)=_
    rw [step_cons src dst hne read write label exit program hl,ih]
    simp only [List.reverse_cons,List.map_append,List.map_singleton,
      List.append_assoc,List.singleton_append,Function.comp_apply]

def transfer (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (state : σ) (r : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label,(state,r),base⟩
      (some ⟨exit,(state,none),tapesAt src dst base []
        ((base src).reverse.map (write ∘ read)++base dst)⟩) ((base src).length+1) where
  steps := (base src).length+1
  evals_in_steps := by
    change (fun c : Option (TM2.Cfg Γ Λ (σ × Option Bool)) => c.bind (TM2.step program))^[
      (base src).length+1] (some ⟨some label,(state,r),base⟩)=_
    simpa only [tapesAt_self] using
      transfer_steps src dst hne read write label exit program hl base (base src) (base dst) state r
  steps_le_m := le_rfl

end ContinuumCoulomb.QuantumBitTransfer

end OAI
