import OAI.Computability.Scheduling.FamilyCosts

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
theorem layerStep
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.layerStep.time (n j) ((U j,(M j,(fs j,zs j))),tab j)) 150009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hBody := layerBody (fun p : Poly.ListPool fs => n p.1) (fun p => U p.1) (fun p => M p.1)
    (fun p => tab p.1) (fun p => fs p.1) (fun p => zs p.1) (fun p => p.2.1)
    (hl.precomp Sigma.fst) (hf.precomp Sigma.fst) (hz.precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hb p.1)
  have hV := Poly.volumeSolve (fun p : Poly.ListPool fs => M p.1) (fun p => tab p.1)
    (fun p => fs p.1) (fun p => zs p.1) (fun p => p.2.1)
    ((Poly.size n).precomp Sigma.fst) (fun p => ht p.1) (fun p => hb p.1)
  have hA : Poly (fun p : Poly.ListPool fs => n p.1) (fun p => volume p.2.1) 2 := by poly_auto
  have hE : Poly n (fun j => volume ((U j,(M j,(fs j,zs j))),tab j)) 30002 := by poly_auto
  have hTable := Poly.tableOfTime Uniform.layerBody n fs (fun j => ((U j,(M j,(fs j,zs j))),tab j))
    hf hBody hV hA hfv hE
  have hExact : Poly n (fun j => Uniform.layerBody.tableOfA.time (n j)
      (fs j,((U j,(M j,(fs j,zs j))),tab j))) 150009 := hTable
  have ho (j : J) : TableSmall (Algorithm.tableOf (fs j)
      (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j))) := by
    intro W b h
    have hs := (Algorithm.mem_tableOf _ _ W b).mp h
    exact blockSmall_of_good (Algorithm.solve_good _ (ht j) _ _ hs.2)
      (Algorithm.solve_bounded _ (hb j) _ _ hs.2)
  have hOL : Poly n (fun j => (Algorithm.tableOf (fs j)
      (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j))).length) 30000 :=
    Poly.of_le (fun j => Algorithm.tableOf_length _ _) hf
  have hOV := Poly.volumeTable _ (Poly.size n) hOL ho
  poly_auto

theorem layers
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.layers.time (n j) (n j,(U j,(M j,(fs j,zs j))))) 150010 := by
  let e j : Uniform.LayerEnv (n j) := (U j,(M j,(fs j,zs j)))
  let a j : Uniform.LayerEnv (n j) × Table (n j) := (e j,[(∅,Algorithm.Block.empty)])
  have hlen : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => (Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1).length) 30000 := by
    apply Poly.of_le (fun p : Poly.IterPool n => Algorithm.layers_length _ _ _ _)
    have hf' := hf.precomp (fun p : Poly.IterPool n => p.1)
    poly_auto
  have ht := layerStep (fun p : Poly.IterPool n => n p.1) (fun p => U p.1) (fun p => M p.1)
    (fun p => Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1)
    (fun p => fs p.1) (fun p => zs p.1) hlen (hf.precomp Sigma.fst) (hz.precomp Sigma.fst)
    (fun p => Algorithm.layers_good _ _ _ _) (fun p => Algorithm.layers_bounded _ _ _ _)
  have hvTab := Poly.volumeTable _ ((Poly.size n).precomp (fun p : Poly.IterPool n => p.1)) hlen
    (fun p => layers_small _ _ _ _)
  have hfV := Poly.volumeSetList fs (Poly.size n) hf
  have hzV := Poly.volumeSetList zs (Poly.size n) hz
  have hti : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => Uniform.layerStep.time (n p.1)
        ((Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1))) 150009 := by
    convert ht using 1
    funext p
    rw [show (Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1) =
      (e p.1,Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1) from layerStep_iterate (e p.1) p.2.1]
  have hvi : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => volume ((Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1))) 30002 := by
    have hf' := hfV.precomp (fun p : Poly.IterPool n => p.1)
    have hz' := hzV.precomp (fun p : Poly.IterPool n => p.1)
    have hn' := (Poly.size n).precomp (fun p : Poly.IterPool n => p.1)
    simp only [show ∀ p : Poly.IterPool n, (Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1) =
      (e p.1,Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1) from fun p => layerStep_iterate (e p.1) p.2.1]
    dsimp only [e]
    poly_auto
  have hInitV := Poly.volumeTable (fun j => ([(∅,Algorithm.Block.empty)] : Table (n j)))
    (Poly.size n) (Poly.const n 1) (fun j => layers_small (matrixRel (M j)) (fs j) (zs j) 0)
  have hIter := Poly.iterateTime Uniform.layerStep n n a (Poly.size n) hti hvi
  have hFinalV := hvTab.precomp (fun j => ⟨j,⟨n j,by omega⟩⟩)
  dsimp only [a, e] at hIter
  simp only [Uniform.layers, Uniform.time_congr, Uniform.time_comp, Uniform.time_pair,
    Uniform.time_fst, Uniform.time_snd, Function.comp_apply]
  simp only [layerStep_iterate]
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

def fullLayers (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    Algorithm.layers (matrixRel x.2)
      (effectiveFamily (matrixRel x.2) (jobRank (matrixRel x.2))
        (reverseJobRank (matrixRel x.2)) (List.finRange n) K)
      ((tripleList (List.finRange n)).map Subtype.val) n) :=
  (((fst.comp universeNumber).pair (fst.pair (snd.pair ((family K).pair (fst.comp triples))))).comp layers)
theorem time_fullSolveK (K n : ℕ) (x : Universe n × Matrix n) :
    (fullSolveK K).time n x = (((fullLayers K).pair (fst.comp universeSet)).comp (lookupA setEq)).time n x := by
  simp only [fullSolveK,time_congr,fullLayers]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
theorem fullLayers (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.fullLayers K).time x.1 x.2) 150010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let fs (x : Σ n, Universe n × Matrix n) := effectiveFamily (matrixRel x.2.2)
    (jobRank (matrixRel x.2.2)) (reverseJobRank (matrixRel x.2.2)) (List.finRange x.1) K
  let zs (x : Σ n, Universe n × Matrix n) := (tripleList (List.finRange x.1)).map Subtype.val
  have hf : Poly n (fun x => (fs x).length) 30000 :=
    (Poly.lengthFamily (s := n) (n := n) (d := 1) (fun x : Σ n, Universe n × Matrix n => x.2.2) K (Poly.size n)).lift (by omega)
  have hz : Poly n (fun x => (zs x).length) 3 := by
    simpa only [zs,List.length_map] using Poly.lengthTriples (Poly.size n)
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hF := familyBound K hk
  have hL := layers n (fun x => x.2.1) (fun x => x.2.2) fs zs hf hz
  poly_auto

theorem fullSolveK (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.fullSolveK K).time x.1 x.2) 150010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let fs (x : Σ n, Universe n × Matrix n) := effectiveFamily (matrixRel x.2.2)
    (jobRank (matrixRel x.2.2)) (reverseJobRank (matrixRel x.2.2)) (List.finRange x.1) K
  let zs (x : Σ n, Universe n × Matrix n) := (tripleList (List.finRange x.1)).map Subtype.val
  let tab (x : Σ n, Universe n × Matrix n) := Algorithm.layers (matrixRel x.2.2) (fs x) (zs x) x.1
  have hf : Poly n (fun x => (fs x).length) 30000 :=
    (Poly.lengthFamily (s := n) (n := n) (d := 1) (fun x : Σ n, Universe n × Matrix n => x.2.2) K (Poly.size n)).lift (by omega)
  have hlen : Poly n (fun x => (tab x).length) 30000 := by
    apply Poly.of_le (fun x => Algorithm.layers_length _ _ _ _)
    poly_auto
  have hFL := fullLayers K hk
  have htv := Poly.volumeTable tab (Poly.size n) hlen (fun x => layers_small _ _ _ _)
  have hov := Poly.volumeSmallLookup tab (fun _ => Finset.univ) (Poly.size n) (fun x => layers_small _ _ _ _)
  poly_auto
theorem fullSolve : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.fullSolve.time x.1 x.2) 150010 := fullSolveK 10000 (by omega)
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
theorem paddedSolve : Poly
    (fun x : Σ i : ℕ × ℕ, Cardinal i.2 × Matrix i.1 => x.1.1+x.1.2)
    (fun x => Uniform.paddedSolve.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, Cardinal i.2 × Matrix i.1) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def scheduleRestriction : Uniform (fun (i : ℕ × ℕ) (x : Algorithm.Block (Fin (3*i.2)) × Universe i.1) =>
    (fun v : Fin i.1 => (List.ofFn x.1.time).getD v.val 0)) :=
  (snd.pair (fst.comp (blockTime.reindex (fun i : ℕ × ℕ => 3*i.2)))).comp
    (restrictTime.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
def scheduleCandidate : Uniform (fun (i : ℕ × ℕ) (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
    (Algorithm.fullSolve (paddedOrder (matrixRel x.2.2) (3*i.2))).map
      (fun (b : Algorithm.Block (Fin (3*i.2))) => (fun v : Fin i.1 => (List.ofFn b.time).getD v.val 0))) :=
  ((snd.comp paddedSolve).pair fst).comp scheduleRestriction.optionMap
theorem time_scheduleMatrixFixed (i : ℕ × ℕ) (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) :
    scheduleMatrixFixed.time i x =
      (((((fst.comp (universeNumber.reindex Prod.fst)).pair
        ((snd.comp fst).comp (cardinalValue Prod.snd) |>.comp (Realizer.triple.uniform (ℕ × ℕ)))).comp
        (Realizer.le.uniform (ℕ × ℕ))).pair id).comp (scheduleCandidate.choose none)).time i x := by
  simp only [scheduleMatrixFixed,time_congr,scheduleCandidate,scheduleRestriction]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem scheduleRestriction : Poly
    (fun x : Σ i : ℕ × ℕ, Algorithm.Block (Fin (3*i.2)) × Universe i.1 => x.1.1+x.1.2+volume x.2.1)
    (fun x => Uniform.scheduleRestriction.time x.1 x.2) 10 := by
  let s (x : Σ i : ℕ × ℕ, Algorithm.Block (Fin (3*i.2)) × Universe i.1) := x.1.1+x.1.2+volume x.2.1
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hv : Poly s (fun x => volume x.2.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
abbrev ScheduleInput (i : ℕ × ℕ) := Universe i.1 × (Cardinal i.2 × Matrix i.1)
theorem candidateVolume {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))
    (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume ((Algorithm.fullSolve (paddedOrder (matrixRel (M j)) (3*T j))).map
      (fun b => (fun v : Fin (n j) => (List.ofFn b.time).getD v.val 0)))) 3 := by
  have h3 : Poly s (fun j => 3*T j) 1 := by poly_auto
  let o (j : J) := Algorithm.fullSolve (paddedOrder (matrixRel (M j)) (3*T j))
  have hO : Poly s (fun j => volume (o j)) 2 := Poly.volumeFullSolve _ h3
  have hP := Poly.volumePool (fun j => (o j).toList) (Poly.volumeOptionToList o hO)
  have hBT := Poly.blockTime (fun p : Poly.ListPool (fun j => (o j).toList) => p.2.1) hP
  have hR := Poly.volumeRestricted (n := fun p : Poly.ListPool (fun j => (o j).toList) => n p.1)
    (fun p : Poly.ListPool (fun j => (o j).toList) => p.2.1.time)
    (hn.precomp Sigma.fst) hBT
  exact Poly.volumeOptionMap (fun (j : J) (b : Algorithm.Block (Fin (3*T j))) => (fun v : Fin (n j) => (List.ofFn b.time).getD v.val 0)) o hR

theorem scheduleCandidate : Poly
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => x.1.1+x.1.2)
    (fun x => Uniform.scheduleCandidate.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, ScheduleInput i) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have h3 : Poly s (fun x => 3*x.1.2) 1 := by poly_auto
  let o (x : Σ i : ℕ × ℕ, ScheduleInput i) := Algorithm.fullSolve (paddedOrder (matrixRel x.2.2.2) (3*x.1.2))
  have hO : Poly s (fun x => volume (o x)) 2 := Poly.volumeFullSolve _ h3
  have hP := Poly.volumePool (fun x => (o x).toList) (Poly.volumeOptionToList o hO)
  have hT := Poly.blockTime (fun p : Poly.ListPool (fun x => (o x).toList) => p.2.1) hP
  have hR := Poly.volumeRestricted (n := fun p : Poly.ListPool (fun x => (o x).toList) => p.1.1.1)
    (fun p : Poly.ListPool (fun x => (o x).toList) => p.2.1.time)
    (hn.precomp Sigma.fst) hT
  have hnp := hn.precomp (Sigma.fst : Poly.ListPool (fun x => (o x).toList) → _)
  have hmp := hm.precomp (Sigma.fst : Poly.ListPool (fun x => (o x).toList) → _)
  have hRC : Poly (fun p : Poly.ListPool (fun x => (o x).toList) => s p.1)
      (fun p => Uniform.scheduleRestriction.time p.1.1 (p.2.1,p.1.2.1)) 20 := by
    have hs : Poly (fun p : Poly.ListPool (fun x => (o x).toList) => s p.1)
        (fun p => p.1.1.1+p.1.1.2+volume p.2.1) 2 := by
      exact (hnp.add hmp).add hP
    exact Poly.reparam (r := 2) (d := 10) scheduleRestriction
      (fun p : Poly.ListPool (fun x => (o x).toList) => ⟨p.1.1,(p.2.1,p.1.2.1)⟩) hs
  have hU := Poly.volumeUniverse hn (fun x => x.2.1)
  have hOpt := Poly.optionMapTime (fun x : Σ i, ScheduleInput i => x.1) (fun x => x.2.1) o
    Uniform.scheduleRestriction hRC hO hU hR
  poly_auto

theorem scheduleMatrixFixed : Poly
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => x.1.1+x.1.2)
    (fun x => Uniform.scheduleMatrixFixed.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, ScheduleInput i) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have h3 : Poly s (fun x => 3*x.1.2) 1 := by poly_auto
  have hO := Poly.volumeFullSolve
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => paddedOrder (matrixRel x.2.2.2) (3*x.1.2)) h3
  have hV := candidateVolume s (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2.2.2) hn hm
  poly_auto

theorem scheduleMatrix : Poly
    (fun x : Σ n, Universe n × (ℕ × Matrix n) => x.1+x.2.2.1)
    (fun x => Uniform.scheduleMatrix.time x.1 x.2) 150010 := by
  let s (x : Σ n, Universe n × (ℕ × Matrix n)) := x.1+x.2.2.1
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.2.2.1) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
