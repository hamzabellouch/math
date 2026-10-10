import OAI.Computability.Scheduling.StateBounds

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev StatesInput (n : ℕ) := Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))
def statesC : Uniform (fun n (x : (Finset (Fin n) × Finset (Fin n)) ×
    (Universe n × Finset (Fin n))) => Algorithm.State.candidate x.2.2 x.1.1 x.1.2) :=
  ((snd.comp fst).pair ((snd.comp snd).pair ((fst.comp fst).pair (fst.comp snd)))).comp stateCandidate
def statesF : Uniform (fun n (x : StatesInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def statesZ : Uniform (fun n (x : StatesInput n) => x.2.2.2.1) := snd.comp (snd.comp (snd.comp fst))
def statesW : Uniform (fun n (x : StatesInput n) => x.2.2.2.2) := snd.comp (snd.comp (snd.comp snd))
def statesPairs := (statesF.pair statesZ).comp product
def statesS := (statesPairs.pair (fst.pair statesW)).comp statesC.map
def statesP : Uniform (fun n (x : Algorithm.State (Fin n) ×
    (Universe n × (Matrix n × Finset (Fin n)))) =>
    decide (x.1.Compatible (matrixRel x.2.2.1) x.2.2.2)) :=
  ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateCompatible
theorem time_states (n : ℕ) (x : StatesInput n) :
    states.time n x =
    ((statesS.pair (fst.pair ((snd.comp fst).pair statesW))).comp statesP.filter).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem statesC : Poly (fun x : Σ n, (Finset (Fin n) × Finset (Fin n)) ×
    (Universe n × Finset (Fin n)) => x.1)
    (fun x => Uniform.statesC.time x.1 x.2) 5 := by poly_auto
theorem statesP : Poly (fun x : Σ n, Algorithm.State (Fin n) ×
    (Universe n × (Matrix n × Finset (Fin n))) => x.1)
    (fun x => Uniform.statesP.time x.1 x.2) 5 := by poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
theorem statesPairs
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.statesPairs.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 60020 := by
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  poly_auto

theorem statesS
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.statesS.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 60020 := by
  have hp := statesPairs n U M fs zs W hf hz
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  poly_auto

theorem states
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.states.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 120008 := by
  have hS := statesS n U M fs zs W hf hz
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev BlockAppendCellInput (n : ℕ) := Fin n ×
  (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def appendCellS : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def appendCellT : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def appendCellTest : Uniform (fun n (x : BlockAppendCellInput n) => decide (x.1 ∈ x.2.1)) :=
  (fst.pair (snd.comp fst)).comp setMem
def appendCellLeft : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1.time x.1) :=
  (((appendCellS.comp blockTime).pair fst).comp functionGet)
def appendCellRight : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1.length+x.2.2.2.time x.1) :=
  (((appendCellS.comp blockLength).pair (((appendCellT.comp blockTime).pair fst).comp functionGet)).comp
    (Realizer.add.uniform ℕ))
def appendCell : Uniform (fun n (x : BlockAppendCellInput n) =>
    if x.1 ∈ x.2.1 then x.2.2.1.time x.1 else x.2.2.1.length+x.2.2.2.time x.1) :=
  (appendCellTest.ite appendCellLeft appendCellRight).congr (fun _ _ => by simp)
abbrev BlockAppendInput (n : ℕ) := Universe n ×
    (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def appendLength : Uniform (fun n (x : BlockAppendInput n) => x.2.2.1.length+x.2.2.2.length) :=
  ((((snd.comp (snd.comp fst)).comp blockLength).pair
      ((snd.comp (snd.comp snd)).comp blockLength)).comp (Realizer.add.uniform ℕ))
def blockAppendNamed : Uniform (fun n (x : BlockAppendInput n) =>
    Algorithm.Block.append x.2.1 x.2.2.1 x.2.2.2) :=
  (appendLength.pair appendCell.vectorMap).comp blockMake
theorem time_blockAppend (n : ℕ) (x : BlockAppendInput n) :
    blockAppend.time n x = blockAppendNamed.time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.BlockAppendCellInput (n j))
theorem appendCellLeft
    (hb : Poly n (fun j => volume (x j).2.2.1) 2)
    (hc : Poly n (fun j => volume (x j).2.2.2) 2) :
    Poly n (fun j => Uniform.appendCellLeft.time (n j) (x j)) 4 := by poly_auto

theorem appendCellRight
    (hb : Poly n (fun j => volume (x j).2.2.1) 2)
    (hc : Poly n (fun j => volume (x j).2.2.2) 2) :
    Poly n (fun j => Uniform.appendCellRight.time (n j) (x j)) 4 := by poly_auto

theorem appendCell
    (hb : Poly n (fun j => volume (x j).2.2.1) 2)
    (hc : Poly n (fun j => volume (x j).2.2.2) 2) :
    Poly n (fun j => Uniform.appendCell.time (n j) (x j)) 4 := by
  have hL := appendCellLeft n x hb hc
  have hR := appendCellRight n x hb hc
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
def appendVector := appendCell.vectorMap
theorem time_blockAppendNamed (n : ℕ) (x : BlockAppendInput n) :
    blockAppendNamed.time n x = ((appendLength.pair appendVector).comp blockMake).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (W : ∀ j, Finset (Fin (n j)))
variable (b c : ∀ j, Algorithm.Block (Fin (n j)))

theorem appendLength
    (hb : Poly n (fun j => volume (b j)) 2)
    (hc : Poly n (fun j => volume (c j)) 2) :
    Poly n (fun j => Uniform.appendLength.time (n j) (U j,(W j,(b j,c j)))) 4 := by
  poly_auto

theorem appendVector
    (hb : Poly n (fun j => volume (b j)) 2)
    (hc : Poly n (fun j => volume (c j)) 2) :
    Poly n (fun j => Uniform.appendVector.time (n j) (U j,(W j,(b j,c j)))) 5 := by
  have hcell := appendCell (fun p : Poly.ListPool (fun j => List.finRange (n j)) => n p.1)
    (fun p => (p.2.1,(W p.1,(b p.1,c p.1)))) (hb.precomp Sigma.fst) (hc.precomp Sigma.fst)
  poly_auto

theorem blockAppend
    (hb : Poly n (fun j => volume (b j)) 2)
    (hc : Poly n (fun j => volume (c j)) 2) :
    Poly n (fun j => Uniform.blockAppend.time (n j) (U j,(W j,(b j,c j)))) 5 := by
  have hL := appendLength n U W b c hb hc
  have hV := appendVector n U W b c hb hc
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev AdvanceInput (n : ℕ) := Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def advanceU : Uniform (fun n (x : AdvanceInput n) => x.1) := fst
def advanceV : Uniform (fun n (x : AdvanceInput n) => x.2.1) := snd.comp fst
def advanceS : Uniform (fun n (x : AdvanceInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def advanceT : Uniform (fun n (x : AdvanceInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def advanceB : Uniform (fun n (x : AdvanceInput n) =>
    Algorithm.Block.append x.2.1.left x.2.2.1 Algorithm.Block.triple) :=
  (advanceU.pair ((advanceV.comp stateLeft).pair
    (advanceS.pair (advanceU.comp blockTriple)))).comp blockAppend
theorem time_stateAdvance (n : ℕ) (x : AdvanceInput n) :
    stateAdvance.time n x =
      ((advanceU.pair (((advanceU.pair advanceV).comp stateUpto).pair
        (advanceB.pair advanceT))).comp blockAppend).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}
theorem volumeAppendTriple (W : ∀ j, Finset (Fin (n j))) (b : ∀ j, Algorithm.Block (Fin (n j)))
    (hn : Poly s n d) (hb : ∀ j, BlockSmall (b j)) :
    Poly s (fun j => volume (Algorithm.Block.append (W j) (b j) Algorithm.Block.triple)) (2*d) := by
  apply of_le (g := fun j => 4*(n j+1)*(n j+2))
  · intro j
    apply volume_block_bound _ (n j+1)
    · change (b j).length+1 ≤ n j+1
      exact Nat.add_le_add_right (hb j).1 1
    · intro a
      simp only [Algorithm.Block.append,Algorithm.Block.triple]
      have := (hb j).1; have := (hb j).2 a
      split_ifs <;> omega
  · poly_bound
end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Algorithm.Block (Fin (n j)))
theorem advanceB (hb : Poly n (fun j => volume (b j)) 2)
    (hc : Poly n (fun j => volume (c j)) 2) :
    Poly n (fun j => Uniform.advanceB.time (n j) (U j,(v j,(b j,c j)))) 5 := by
  have htriple : Poly n (fun j => volume (Algorithm.Block.triple : Algorithm.Block (Fin (n j)))) 2 := by poly_auto
  have h := blockAppend n U (fun j => (v j).left) b (fun _ => Algorithm.Block.triple) hb htriple
  poly_auto

theorem stateAdvance (hb : ∀ j, BlockSmall (b j)) (hc : ∀ j, BlockSmall (c j)) :
    Poly n (fun j => Uniform.stateAdvance.time (n j) (U j,(v j,(b j,c j)))) 7 := by
  have hbV := Poly.volumeSmallBlock b (Poly.size n) hb
  have hcV := Poly.volumeSmallBlock c (Poly.size n) hc
  have hB := advanceB n U v b c hbV hcV
  have hBVol := Poly.volumeAppendTriple (fun j => (v j).left) b (Poly.size n) hb
  have hA := blockAppend n U (fun j => (v j).upto)
    (fun j => Algorithm.Block.append (v j).left (b j) Algorithm.Block.triple) c hBVol hcV
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

theorem volume_option_mem_le {α : Type u3} [Coding α] {o : Option α} {a : α} (ha : a ∈ o) :
    volume a ≤ volume o := by cases o <;> simp_all [volume_some]

theorem volume_find_le {α : Type u4} [Coding α] (xs : List α) (p : α → Bool) :
    volume (xs.find? p) ≤ volume xs+2 := volume_option_le _ _ (fun _a ha =>
      volume_mem_le (List.mem_of_find?_eq_some ha))

theorem volume_lookup_le {K V : Type} [Coding K] [Coding V] [DecidableEq K]
    (xs : List (K × V)) (k : K) : volume (Algorithm.lookup xs k) ≤ volume xs+2 :=
  volume_option_le _ _ (fun v hv => by
    have h := volume_mem_le (Algorithm.lookup_mem hv)
    rw [volume_pair] at h; omega)

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_mapSndOption_le (i : I) (o : Option (α i × β i)) :
    (snd : Uniform (fun i (x : α i × β i) => x.2)).mapOption.time i o ≤
      1000000000*(volume o+1) := by
  let R : Uniform (fun i (x : (α i × β i) × Unit) => x.1.2) := fst.comp snd
  have hm := time_optionMap R i o ()
    (100*(volume o+1)) (volume o) (by
      intro a ha
      have hv := volume_option_mem_le ha
      simp only [R,time_comp,time_fst,time_snd,volume_prod,volume_unit]
      rw [volume_pair] at hv
      omega) (by
      intro a ha
      have hv := volume_option_mem_le ha
      rw [volume_prod] at hv
      dsimp only
      omega)
  simp only [mapOption,time_congr,time_comp,time_pair,time_id,time_unit,Function.comp_apply,volume_pair,volume_unit]
  dsimp only [R] at hm
  simp only [volume_unit] at hm
  nlinarith [volume_pos o]

theorem time_lookup_le [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2)))
    (i : I) (xs : List (α i × β i)) (k : α i) (T : ℕ)
    (hT : ∀ a ∈ xs, E.time i (a.1,k) ≤ T) :
    (lookup E).time i (xs,k) ≤ 100000000000*(xs.length+1)*(T+volume xs+volume k+1) := by
  let P := (((fst.comp fst).pair snd).comp E : Uniform (fun i (x : (α i × β i) × α i) => decide (x.1.1=x.2)))
  have hp : ∀ a ∈ xs, P.time i (a,k) ≤ T+100*(volume xs+volume k+1) := by
    intro a ha
    have h := hT a ha
    have hv := volume_mem_le ha
    simp only [P,time_comp,time_pair,time_fst,time_snd,Function.comp_apply,volume_prod]
    rw [volume_pair] at hv
    omega
  have hf := time_find? P i xs k (T+100*(volume xs+volume k+1)) hp
  have hm := time_mapSndOption_le i (xs.find? (fun a => decide (a.1=k)))
  have hv := volume_find_le xs (fun a => decide (a.1=k))
  simp only [lookup,time_congr,time_comp,Function.comp_apply]
  change P.find?.time i (xs,k)+_+10*(volume (xs.find? (fun a => decide (a.1=k)))+1) ≤ _
  nlinarith [volume_pos xs,volume_pos k]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform
theorem time_lookup_setEq_le {n : ℕ}
    (xs : List (Finset (Fin n) × Algorithm.Block (Fin n))) (k : Finset (Fin n)) :
    (lookupA (β := fun n => Algorithm.Block (Fin n)) setEq).time n (xs,k) ≤ 100000000000*(xs.length+1)*
      (Classical.choose Costs.setEq*(n+2)^4+volume xs+volume k+1) := by
  apply time_lookup_le setEq
  intro a _ha
  exact Classical.choose_spec Costs.setEq ⟨n,(a.1,k)⟩
theorem time_lookup_stateEq_le {n : ℕ}
    (xs : List (Algorithm.State (Fin n) × Algorithm.Block (Fin n))) (k : Algorithm.State (Fin n)) :
    (lookupA (β := fun n => Algorithm.Block (Fin n)) stateEq).time n (xs,k) ≤ 100000000000*(xs.length+1)*
      (Classical.choose Costs.stateEq*(n+2)^4+volume xs+volume k+1) := by
  apply time_lookup_le stateEq
  intro a _ha
  exact Classical.choose_spec Costs.stateEq ⟨n,(a.1,k)⟩
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev TryInput (n : ℕ) := Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))
def tryU : Uniform (fun n (x : TryInput n) => x.1) := fst
def tryT : Uniform (fun n (x : TryInput n) => x.2.1) := snd.comp fst
def tryA : Uniform (fun n (x : TryInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def tryV : Uniform (fun n (x : TryInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def tryW := (tryU.pair (tryA.comp fst)).comp stateUpto
def tryL := tryV.comp stateLeft
def tryP := (tryW.pair tryL).comp setSubset
def tryDiff := (tryL.pair tryW).comp setDiff
def tryO := (tryT.pair tryDiff).comp (lookupA setEq)
def tryWork := (tryO.pair (tryU.pair tryA)).comp advanceLast.optionMap
theorem time_tryAdvance (n : ℕ) (x : TryInput n) :
    tryAdvance.time n x = (tryP.ite tryWork none).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (c : ∀ j, Algorithm.Block (Fin (n j)))
theorem advanceLast (hb : ∀ j, BlockSmall (u j).2) (hc : ∀ j, BlockSmall (c j)) :
    Poly n (fun j => Uniform.advanceLast.time (n j) (c j,(U j,u j))) 7 := by
  have h := stateAdvance n U (fun j => (u j).1) (fun j => (u j).2) c hb hc
  have hvC := Poly.volumeSmallBlock c (Poly.size n) hc
  have hvB := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
