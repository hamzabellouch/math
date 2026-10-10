import OAI.Computability.Scheduling.SchedulingCosts

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev BestState (n : ℕ) := (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))
def bestNext : Uniform (fun (n : ℕ) (x : BestState n) => x.2.1+1) :=
  (snd.comp fst).comp (Realizer.succ.uniform ℕ)
def bestAttempt : Uniform (fun (n : ℕ) (x : BestState n) =>
    (ThreeMachine.StackCompiler.scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))) :=
  ((((fst.comp fst).pair (bestNext.pair (fst.comp snd))).comp scheduleMatrix).pair bestNext).comp swap.optionMap

def bestRetain : Uniform (fun (n : ℕ) (x : BestState n) =>
    if x.2.2.isSome then x.2.2 else
    (ThreeMachine.StackCompiler.scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))) :=
  (((snd.comp snd).comp optionIsSome).pair id).comp ((snd.comp snd).choose bestAttempt)

theorem time_bestMatrixStep (n : ℕ) (x : BestState n) :
    bestMatrixStep.time n x = (fst.pair (bestNext.pair bestRetain)).time n x := by
  simp only [bestMatrixStep,time_congr,bestNext,bestRetain,bestAttempt]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestNext : Poly s (fun j => Uniform.bestNext.time (n j) ((U j,M j),(k j,o j))) 2 := by
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → Option (β i)} {g : ∀ i, α i → γ i}

theorem time_attach_le (R : Uniform f) (K : Uniform g) (i : I) (x : α i) :
    ((R.pair K).comp swap.optionMap).time i x ≤
      10000000000*(R.time i x+K.time i x+volume x+volume (f i x)+volume (g i x)+1) := by
  have hmem : ∀ b ∈ f i x, volume b ≤ volume (f i x) := by
    intro b hb
    rw [show f i x = Option.some b from hb,volume_some]
    omega
  have h := time_optionMap (swap : Uniform (fun i (a : β i × γ i) => (a.2,a.1))) i
    (f i x) (g i x) (100*(volume (f i x)+volume (g i x)+1))
    (volume (f i x)+volume (g i x)+1) (by
      intro b hb
      have := hmem b hb
      simp only [swap,time_pair,time_fst,time_snd,volume_pair]
      omega) (by
      intro b hb
      have := hmem b hb
      simp only [volume_pair]
      omega)
  simp only [time_comp,time_pair,volume_pair]
  omega
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u5} {J : Type u6} {s : J → ℕ} {α : I → Type u7} {β : I → Type u8} {γ : I → Type u9}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}
variable (R : Uniform f) (S : Uniform g) (idx : J → I) (x : ∀ j, α (idx j)) {d : ℕ}

theorem compTimeSame (hR : Poly s (fun j => R.time (idx j) (x j)) d)
    (hS : Poly s (fun j => S.time (idx j) (f (idx j) (x j))) d)
    (hV : Poly s (fun j => volume (f (idx j) (x j))) d) :
    Poly s (fun j => (R.comp S).time (idx j) (x j)) d := by
  simp only [Uniform.time_comp]
  have h := hV.add (const s 1)
  have ht := (const s 10).mul h
  simpa only [Nat.zero_add,Nat.max_zero,Nat.max_self] using (hR.add hS).add ht

variable {g' : ∀ i, α i → γ i}
theorem pairTimeSame (S : Uniform g') (hR : Poly s (fun j => R.time (idx j) (x j)) d)
    (hS : Poly s (fun j => S.time (idx j) (x j)) d)
    (hX : Poly s (fun j => volume (x j)) d)
    (hF : Poly s (fun j => volume (f (idx j) (x j))) d)
    (hG : Poly s (fun j => volume (g' (idx j) (x j))) d) :
    Poly s (fun j => (R.pair S).time (idx j) (x j)) d := by
  simp only [Uniform.time_pair]
  have h := ((hX.add hF).add hG).add (const s 1)
  have ht := (const s 20).mul h
  simpa only [Nat.zero_add,Nat.max_zero,Nat.max_self] using (hR.add hS).add ht
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

theorem bestAttempt : Poly s (fun j => Uniform.bestAttempt.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  let P : Uniform (fun (n : ℕ) (x : Uniform.BestState n) => (x.1.1,(x.2.1+1,x.1.2))) :=
    (Uniform.fst.comp Uniform.fst).pair (Uniform.bestNext.pair (Uniform.fst.comp Uniform.snd))
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hN := bestNext s n U M k o hn hk ho
  have hP : Poly s (fun j => P.time (n j) ((U j,M j),(k j,o j))) 2 := by
    dsimp only [P]
    poly_auto
  have hV : Poly s (fun j => volume (U j,(k j+1,M j))) 2 := by poly_auto
  have hST : Poly s (fun j => Uniform.scheduleMatrix.time (n j) (U j,(k j+1,M j))) 150010 := by
    have hs : Poly s (fun j => n j+(k j+1)) 1 := hn.add hsucc
    exact Poly.reparam (r := 1) (d := 150010) scheduleMatrix
      (fun j => ⟨n j,(U j,(k j+1,M j))⟩) hs
  have hSC := Poly.compTimeSame P Uniform.scheduleMatrix n (fun j => ((U j,M j),(k j,o j)))
    (hP.lift (show 2 ≤ 150010 by decide)) hST (hV.lift (show 2 ≤ 150010 by decide))
  apply Poly.of_le (fun j => Uniform.time_attach_le (P.comp Uniform.scheduleMatrix) Uniform.bestNext
    (n j) ((U j,M j),(k j,o j)))
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestRetain : Poly s (fun j => Uniform.bestRetain.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hAV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t)))) 2 := by
    apply Poly.of_le (fun j => volume_tableBody (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)) (k j+1))
    have hvn := Poly.volumeNat hsucc
    exact (hS.add hvn).add (Poly.const s 1)
  have hA := bestAttempt s n U M k o hn hk ho
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestMatrixStep :
    Poly s (fun j => Uniform.bestMatrixStep.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hAV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t)))) 2 := by
    apply Poly.of_le (fun j => volume_tableBody (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)) (k j+1))
    have hvn := Poly.volumeNat hsucc
    exact (hS.add hvn).add (Poly.const s 1)
  have hRV := Poly.volumeIte (fun j => (o j).isSome = true) o
    (fun j => (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t))) ho hAV
  have hN := bestNext s n U M k o hn hk ho
  have hR := bestRetain s n U M k o hn hk ho
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u10} {J : Type u11} {s : J → ℕ} {α : I → Type u12} [∀ i, Coding (α i)]
abbrev StrictIterPool (m : J → ℕ) := Σ j, Fin (m j)
theorem iterateTimeStrict {f : ∀ i, α i → α i} (R : Uniform f)
    (idx : J → I) (m : J → ℕ) (a : ∀ j, α (idx j)) {l t v : ℕ}
    (hm : Poly s m l)
    (ht : Poly (fun p : StrictIterPool m => s p.1)
      (fun p => R.time (idx p.1) ((f (idx p.1))^[p.2.1] (a p.1))) t)
    (hv : Poly (fun p : IterPool m => s p.1)
      (fun p => volume ((f (idx p.1))^[p.2.1] (a p.1))) v) :
    Poly s (fun j => R.iterate.time (idx j) (m j,a j)) (l+Max.max t (Max.max v l)) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_iterate_le R (idx j) (m j) (a j)
    (C*(s j+2)^t) (D*(s j+2)^v)
    (fun k hk => hC ⟨j,⟨k,hk⟩⟩) (fun k hk => hD ⟨j,⟨k,by omega⟩⟩))
  poly_bound
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
theorem bestMatrix (hn : Poly s n 1) :
    Poly s (fun j => Uniform.bestMatrix.time (n j) (U j,M j)) 150011 := by
  let a (j : J) : (Universe (n j) × Matrix (n j)) × (ℕ × Option (ℕ × (Fin (n j) → ℕ))) :=
    ((U j,M j),(0,none))
  have hnp := hn.precomp (Sigma.fst : Poly.IterPool n → J)
  have hkp : Poly (fun p : Poly.IterPool n => s p.1) (fun p => p.2.1) 1 :=
    Poly.of_le (fun p : Poly.IterPool n => Nat.le_of_lt_succ p.2.isLt) hnp
  have hbest := Poly.volumeBest (fun p : Poly.IterPool n => s p.1) (fun p => n p.1)
    (fun p => p.2.1) (fun p => M p.1) hnp hkp
  have hstep := bestMatrixStep (fun p : Poly.IterPool n => s p.1) (fun p => n p.1)
    (fun p => U p.1) (fun p => M p.1) (fun p => p.2.1) (fun p => ThreeMachine.StackCompiler.bestMatrix (M p.1) p.2.1)
    hnp hkp hbest
  have hti : Poly (fun p : Poly.IterPool n => s p.1)
      (fun p => Uniform.bestMatrixStep.time (n p.1)
        (ThreeMachine.StackCompiler.bestMatrixStep^[p.2.1] (a p.1))) 150010 := by
    simpa only [a,bestMatrix_iterate] using hstep
  have hvi : Poly (fun p : Poly.IterPool n => s p.1)
      (fun p => volume (ThreeMachine.StackCompiler.bestMatrixStep^[p.2.1] (a p.1))) 2 := by
    simp only [a,bestMatrix_iterate]
    poly_auto
  have hIter := Poly.iterateTime Uniform.bestMatrixStep n n a hn hti hvi
  have hB := Poly.volumeBest s n n M hn hn
  dsimp only [a] at hIter
  simp only [Uniform.bestMatrix,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,
    Uniform.time_fst,Uniform.time_snd,Function.comp_apply]
  simp only [bestMatrix_iterate]
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
