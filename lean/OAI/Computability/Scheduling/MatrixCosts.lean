import OAI.Computability.Scheduling.TableCosts

namespace OAI

universe u1 u2 u3 u4 u5

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

theorem solveS
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.solveS.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have h := states n U M fs zs W hf hz
  poly_auto

theorem solveMarks
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solveMarks.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  let sts j := Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)
  have hsl : Poly n (fun j => (sts j).length) 30003 := by
    apply Poly.of_le (fun j => Algorithm.states_length _ _ _ _)
    poly_bound
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j) :=
    fun j _ hu => Algorithm.states_compatible _ hu
  have hS := solveS n U M tab fs zs W hl hf hz hts
  have hMarks := markings n U M tab sts W hl hsl ht hb hs
  poly_auto

theorem solveOut
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solveOut.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  let sts j := Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)
  have hsl : Poly n (fun j => (sts j).length) 30003 := by
    apply Poly.of_le (fun j => Algorithm.states_length _ _ _ _)
    poly_bound
  have hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j) :=
    fun j _ hu => Algorithm.states_compatible _ hu
  let ms j := Algorithm.markings (tab j) (sts j) (n j)
  have hml : Poly n (fun j => (ms j).length) 30003 :=
    Poly.of_le (fun j => Algorithm.markings_length _ _ _) hsl
  have hms (j) : MarksSmall (ms j) := markings_small _ (ht j) (hb j) (hs j) _
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hms
  have hMB := Poly.volumeSmallBlock (fun p : Poly.ListPool ms => p.2.1.2)
    ((Poly.size n).precomp Sigma.fst) (fun p => hms p.1 _ _ p.2.2)
  have hMarks := solveMarks n U M tab fs zs W hl hf hz ht hb
  have hFinish := finishing (fun p : Poly.ListPool ms => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => p.2.1) (hl.precomp Sigma.fst) (fun p => hts p.1)
    (fun p => hms p.1 _ _ p.2.2)
  have hAv : Poly (fun p : Poly.ListPool ms => n p.1)
      (fun p => volume ((Algorithm.lookup (tab p.1) p.2.1.1.right).map
        (p.2.1.1.finish p.2.1.2))) 2 := by
    apply Poly.volumeOption _ (show Poly (fun p : Poly.ListPool ms => n p.1)
      (fun p => 100*(n p.1+2)^2) 2 from by poly_bound)
    intro p b hb'
    obtain ⟨t,ht',rfl⟩ := Option.map_eq_some_iff.mp hb'
    exact volume_advance_le _ _ _ (hms p.1 _ _ p.2.2) (hts p.1 _ _ (Algorithm.lookup_mem ht'))
  poly_auto

theorem solve
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solve.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hOut := solveOut n U M tab fs zs W hl hf hz ht hb
  have hOV := Poly.volumeSolveOut M tab fs zs W (Poly.size n) ht hb
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev LayerEnv (n : ℕ) := Universe n × (Matrix n × (List (Finset (Fin n)) × List (Finset (Fin n))))
def layerBody : Uniform (fun n (x : Finset (Fin n) × (LayerEnv n × Table n)) =>
    Algorithm.solve (matrixRel x.2.1.2.1) x.2.2 x.2.1.2.2.1 x.2.1.2.2.2 x.1) :=
  ((snd.comp (fst.comp fst)).pair ((snd.comp (fst.comp (snd.comp fst))).pair
      ((snd.comp snd).pair ((snd.comp (fst.comp (snd.comp (snd.comp fst)))).pair
        ((snd.comp (fst.comp (snd.comp (snd.comp snd)))).pair fst))))).comp solve
theorem time_layerStep (n : ℕ) (x : LayerEnv n × Table n) :
    layerStep.time n x =
      (fst.pair (((fst.comp (snd.comp (snd.comp fst))).pair id).comp layerBody.tableOfA)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

theorem layerStep_iterate {n : ℕ} (e : Uniform.LayerEnv n) (k : ℕ) :
    (fun p : Uniform.LayerEnv n × Table n =>
      (p.1,Algorithm.tableOf p.1.2.2.1 (Algorithm.solve (matrixRel p.1.2.1) p.2 p.1.2.2.1 p.1.2.2.2)))^[k]
        (e,[(∅,Algorithm.Block.empty)]) =
        (e,Algorithm.layers (matrixRel e.2.1) e.2.2.1 e.2.2.2 k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))
theorem layerBody
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.layerBody.time (n j) (W j,((U j,(M j,(fs j,zs j))),tab j))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hS := solve n U M tab fs zs W hl hf hz ht hb
  poly_auto
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

theorem volume_list_getD_le {α : Type u1} [Coding α] (xs : List α) (k : ℕ) (a : α) :
    volume (xs.getD k a) ≤ volume xs+volume a := by
  rw [List.getD_eq_getElem?_getD]
  cases h : xs[k]? with
  | none => simp only [Option.getD_none]; omega
  | some b =>
    simp only [Option.getD_some]
    have hv := volume_mem_le (List.mem_of_getElem? h)
    omega

theorem volume_list_getElem?_le {α : Type u2} [Coding α] (xs : List α) (k : ℕ) :
    volume xs[k]? ≤ volume xs+2 := by
  apply volume_option_le
  intro a ha
  exact volume_mem_le (List.mem_of_getElem? ha)

namespace Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]
theorem time_getElemD_le (i : I) (xs : List (α i)) (k : ℕ) (a : α i) :
    getElemD.time i ((xs,k),a) ≤ 1000000000*(k+1)*(volume xs+volume a+k+1) := by
  have hG := time_getElem?_le i xs k
  have hD := time_getD_le i xs[k]? a
  have hV := volume_list_getElem?_le xs k
  simp only [getElemD,time_congr,time_comp,onFst,time_pair,time_fst,time_snd,
    volume_prod,volume_nat,Function.comp_apply]
  nlinarith [volume_pos xs,volume_pos a]
theorem time_matrixRows (n : ℕ) (M : Matrix n) :
    matrixRows.time n M = volume M+2 := rfl
end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u5} (s n : J → ℕ) (M : ∀ j, Matrix (n j))
theorem matrixReadNat (a b : J → ℕ) (hn : Poly s n 1) (ha : Poly s a 1) (hb : Poly s b 1) :
    Poly s (fun j => Uniform.matrixReadNat.time (n j) (M j,(a j,b j))) 100 := by
  have hrows : Poly s (fun j => volume ((List.ofFn (M j)).map List.ofFn)) 2 := by
    have he (j) : volume ((List.ofFn (M j)).map List.ofFn) = volume (M j) := by
      change (enc ((List.ofFn (M j)).map List.ofFn)).size = (enc (M j)).size
      rw [enc_map_eq List.ofFn (fun _ => rfl)]
      rfl
    simp only [he]
    exact Poly.volumeMatrix hn M
  have hrow : Poly s (fun j => volume (((List.ofFn (M j)).map List.ofFn).getD (a j) [])) 2 := by
    apply Poly.of_le (fun j => ?_) (hrows.add (Poly.const s 1))
    simpa only [volume_nil] using volume_list_getD_le ((List.ofFn (M j)).map List.ofFn) (a j) []
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def paddedCell : Uniform (fun (i : ℕ × ℕ) (x : (Fin i.2 × Fin i.2) × Matrix i.1) =>
      readMatrix x.2 x.1.1.val x.1.2.val) :=
    (snd.pair (((fst.comp fst).comp (finValue Prod.snd)).pair
      ((fst.comp snd).comp (finValue Prod.snd)))).comp (matrixReadNat.reindex Prod.fst)
theorem time_paddedMatrix (i : ℕ × ℕ) (x : Universe i.2 × Matrix i.1) :
    paddedMatrix.time i x = (matrixMapAny Prod.snd paddedCell).time i x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem paddedCell : Poly (fun x : Σ i : ℕ × ℕ, (Fin i.2 × Fin i.2) × Matrix i.1 => x.1.1+x.1.2)
    (fun x => Uniform.paddedCell.time x.1 x.2) 100 := by
  let s (x : Σ i : ℕ × ℕ, (Fin i.2 × Fin i.2) × Matrix i.1) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have ha := Poly.finVal hm (fun x => x.2.1.1)
  have hb := Poly.finVal hm (fun x => x.2.1.2)
  have hc := matrixReadNat s (fun x => x.1.1) (fun x => x.2.2)
    (fun x => x.2.1.1.val) (fun x => x.2.1.2.val) hn ha hb
  simp only [Uniform.paddedCell, Uniform.time_comp, Uniform.time_pair, Uniform.time_fst, Uniform.time_snd,
    Uniform.time_finValue, Uniform.time_reindex, Function.comp_apply]
  poly_auto

theorem paddedMatrix : Poly (fun x : Σ i : ℕ × ℕ, Universe i.2 × Matrix i.1 => x.1.1+x.1.2)
    (fun x => Uniform.paddedMatrix.time x.1 x.2) 1000 := by
  let s (x : Σ i : ℕ × ℕ, Universe i.2 × Matrix i.1) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
