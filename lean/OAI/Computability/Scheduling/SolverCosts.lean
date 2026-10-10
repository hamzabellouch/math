import OAI.Computability.Scheduling.TransitionCosts

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (v : ∀ j, Algorithm.State (Fin (n j)))

theorem tryW
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryW.time (n j) (U j,(tab j,(u j,v j)))) 30002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto

theorem tryL
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryL.time (n j) (U j,(tab j,(u j,v j)))) 30002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto

theorem tryP
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryP.time (n j) (U j,(tab j,(u j,v j)))) 30002 := by
  have hW := tryW n U tab u v hl ht hb
  have hL := tryL n U tab u v hl ht hb
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto

theorem tryDiff
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryDiff.time (n j) (U j,(tab j,(u j,v j)))) 30002 := by
  have hW := tryW n U tab u v hl ht hb
  have hL := tryL n U tab u v hl ht hb
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto

theorem tryO
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryO.time (n j) (U j,(tab j,(u j,v j)))) 60002 := by
  have hD := tryDiff n U tab u v hl ht hb
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  poly_auto

theorem tryWork
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryWork.time (n j) (U j,(tab j,(u j,v j)))) 60002 := by
  have hO := tryO n U tab u v hl ht hb
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV : Poly n (fun j => volume (u j).2) 2 := Poly.volumeSmallBlock _ (Poly.size n) hb
  have hL : Poly n (fun j => volume (Algorithm.lookup (tab j) ((v j).left \ (u j).1.upto))) 2 :=
    Poly.volumeSmallLookup tab _ (Poly.size n) ht
  have ha := advanceLast (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      ((v j).left \ (u j).1.upto)).toList) => n p.1) (fun p => U p.1)
    (fun p => u p.1) (fun p => p.2.1) (fun p => hb p.1) (fun p =>
      ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2)))
  have hAv : Poly (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      ((v j).left \ (u j).1.upto)).toList) => n p.1)
      (fun p => volume ((u p.1).1.advance (u p.1).2 p.2.1)) 2 := by
    apply Poly.volumeAdvance _ _ _ (Poly.size _) (fun p => hb p.1)
    intro p
    exact ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2))
  poly_auto
theorem tryAdvance
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.tryAdvance.time (n j) (U j,(tab j,(u j,v j)))) 60002 := by
  have hp := tryP n U tab u v hl ht hb
  have hw := tryWork n U tab u v hl ht hb
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  have hAv : Poly (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      ((v j).left \ (u j).1.upto)).toList) => n p.1)
      (fun p => volume ((u p.1).1.advance (u p.1).2 p.2.1)) 2 := by
    apply Poly.volumeAdvance _ _ _ (Poly.size _) (fun p => hb p.1)
    intro p
    exact ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2))
  have hWV := Poly.volumeOptionMap (s := n) (fun j c => (u j).1.advance (u j).2 c)
    (fun j => Algorithm.lookup (tab j) ((v j).left \ (u j).1.upto)) hAv
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))

theorem finishing
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.finishing.time (n j) (u j,(U j,tab j))) 60002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  have hL : Poly n (fun j => volume (Algorithm.lookup (tab j) (u j).1.right)) 2 :=
    Poly.volumeSmallLookup tab _ (Poly.size n) ht
  have ha := advanceLast (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      (u j).1.right).toList) => n p.1) (fun p => U p.1)
    (fun p => u p.1) (fun p => p.2.1) (fun p => hb p.1) (fun p =>
      ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2)))
  have hAv : Poly (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      (u j).1.right).toList) => n p.1)
      (fun p => volume ((u p.1).1.advance (u p.1).2 p.2.1)) 2 := by
    apply Poly.volumeAdvance _ _ _ (Poly.size _) (fun p => hb p.1)
    intro p
    exact ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2))
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev SolveInput (n : ℕ) := Universe n × (Matrix n ×
  (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))
def solveU : Uniform (fun n (x : SolveInput n) => x.1) := fst
def solveM : Uniform (fun n (x : SolveInput n) => x.2.1) := snd.comp fst
def solveT : Uniform (fun n (x : SolveInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def solveF : Uniform (fun n (x : SolveInput n) => x.2.2.2.1) := snd.comp (snd.comp (snd.comp fst))
def solveZ : Uniform (fun n (x : SolveInput n) => x.2.2.2.2.1) := snd.comp (snd.comp (snd.comp (snd.comp fst)))
def solveW : Uniform (fun n (x : SolveInput n) => x.2.2.2.2.2) := snd.comp (snd.comp (snd.comp (snd.comp snd)))
def solveS : Uniform (fun n (x : SolveInput n) =>
    Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := (solveU.pair (solveM.pair (solveF.pair (solveZ.pair solveW)))).comp states
def solveMarks : Uniform (fun n (x : SolveInput n) =>
    Algorithm.markings x.2.2.1 (Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) n) := ((solveU.comp universeNumber).pair (solveU.pair (solveT.pair solveS))).comp markings
def solveOut : Uniform (fun n (x : SolveInput n) =>
    Algorithm.firstResult (fun u => (Algorithm.lookup x.2.2.1 u.1.right).map (u.1.finish u.2))
      (Algorithm.markings x.2.2.1 (Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) n)) := (solveMarks.pair (solveU.pair solveT)).comp finishing.firstResultA
theorem time_solve (n : ℕ) (x : SolveInput n) :
    solve.time n x = ((solveW.comp setIsEmpty).ite (solveU.comp (blockEmpty.comp some)) solveOut).time n x := by
  simp only [solve, time_congr, solveOut, solveMarks, solveS, solveU, solveM, solveT, solveF, solveZ, solveW]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}
theorem volumeSolve (M : ∀ j, Matrix (n j)) (tab : ∀ j, Table (n j))
    (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
    (hn : Poly s n d) (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly s (fun j => volume (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j) (W j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by poly_bound)
  intro j b h
  have hs := blockSmall_of_good (Algorithm.solve_good _ (ht j) _ _ h)
    (Algorithm.solve_bounded _ (hb j) _ _ h)
  exact volume_block_le b hs.1 hs.2
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}
theorem volumeSolveOut (M : ∀ j, Matrix (n j)) (tab : ∀ j, Table (n j))
    (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
    (hn : Poly s n d) (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly s (fun j => volume (Algorithm.firstResult
      (fun u => (Algorithm.lookup (tab j) u.1.right).map (u.1.finish u.2))
      (Algorithm.markings (tab j) (Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)) (n j)))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 100*(n j+2)^2) (2*d) from by poly_bound)
  intro j b h
  obtain ⟨⟨u,bb⟩,hmem,hm⟩ := Algorithm.firstResult_some h
  obtain ⟨t,ht',rfl⟩ := Option.map_eq_some_iff.mp hm
  have hmark : MarksSmall (Algorithm.markings (tab j)
      (Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)) (n j)) := markings_small (matrixRel (M j)) (ht j) (hb j)
    (fun _ hu => Algorithm.states_compatible _ hu) (n j)
  have htSmall : TableSmall (tab j) := fun a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  exact volume_advance_le u bb t (hmark u bb hmem) (htSmall _ _ (Algorithm.lookup_mem ht'))
end ThreeMachine.StackCompiler.Poly
end

end OAI
