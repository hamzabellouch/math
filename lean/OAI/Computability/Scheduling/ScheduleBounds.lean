import OAI.Computability.Scheduling.MatrixCosts

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u1} {s n B : J → ℕ} {d e : ℕ}
theorem volumeBoundedFunction (f : ∀ j, Fin (n j) → ℕ)
    (hn : Poly s n d) (hB : Poly s B e) (hf : ∀ j v, f j v ≤ B j) :
    Poly s (fun j => volume (f j)) (d+e) := by
  apply of_le (g := fun j => 1+(n j)*(2*B j+1+1))
    (fun j => volume_function_le (f j) (2*B j+1) (by
        intro v; rw [volume_nat]; have := hf j v; omega))
  poly_bound

theorem volumePredecessors (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.predecessorCount (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.predecessorCount (matrixRel (M j))) hn hn
    (fun j v => by
      dsimp [Structure.predecessorCount]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))
  simpa only [two_mul] using h

theorem volumeRank (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.jobRank (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.jobRank (matrixRel (M j))) hn hn
    (fun j v => (Structure.jobRank_bounds (matrixRel (M j)) v).2)
  simpa only [two_mul] using h

theorem volumeReverseRank (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.reverseJobRank (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.reverseJobRank (matrixRel (M j))) hn hn
    (fun j v => (Structure.reverseJobRank_bounds (matrixRel (M j)) v).2)
  simpa only [two_mul] using h
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

theorem fullSolve_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    {b : Block (Fin n)} (h : Algorithm.fullSolve r = some b) : BlockSmall b := by
  exact layers_small r _ _ _ _ _ (Algorithm.lookup_mem h)

theorem scheduleMatrix_bound {n T : ℕ} (M : Matrix n) {t : Fin n → ℕ}
    (h : scheduleMatrix M T = some t) (v : Fin n) : t v ≤ 3*T := by
  simp only [scheduleMatrix] at h
  split_ifs at h with hn
  · obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp h
    exact (fullSolve_small _ hb).2 _

theorem bestMatrix_bound {n k : ℕ} (M : Matrix n) {a : ℕ × (Fin n → ℕ)}
    (h : bestMatrix M k = some a) : a.1 ≤ k ∧ ∀ v, a.2 v ≤ 3*k := by
  induction k with
  | zero => simp only [bestMatrix] at h; contradiction
  | succ k ih =>
    simp only [bestMatrix] at h
    cases he : bestMatrix M k with
    | some b =>
      simp only [he,Option.some.injEq] at h
      subst a
      have hi := ih he
      exact ⟨by omega,fun v => by have := hi.2 v; omega⟩
    | none =>
      rw [he] at h
      obtain ⟨t,ht,ha⟩ := Option.map_eq_some_iff.mp h
      cases ha
      exact ⟨le_rfl,fun v => scheduleMatrix_bound M ht v⟩

theorem answerMatrix_length {n : ℕ} (M : Matrix n) (d : Option ℕ) :
    ((answerMatrix M d).getD []).length ≤ n := by
  cases d with
  | none =>
    simp only [answerMatrix]
    cases bestMatrix M n <;> simp only [Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.length_nil,List.length_ofFn,Nat.zero_le,le_refl]
  | some T =>
    simp only [answerMatrix]
    cases scheduleMatrix M T <;> simp only [Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.length_nil,List.length_ofFn,Nat.zero_le,le_refl]

theorem answerMatrix_bound {n : ℕ} (M : Matrix n) (d : Option ℕ) {a : ℕ}
    (h : a ∈ (answerMatrix M d).getD []) : a ≤ 3*(n+d.getD 0) := by
  cases d with
  | none =>
    simp only [answerMatrix,Option.getD_none] at h ⊢
    cases he : bestMatrix M n with
    | none => simp only [he,Option.map_none,Option.getD_none,List.not_mem_nil] at h
    | some b =>
      simp only [he,Option.map_some,Option.getD_some,List.mem_ofFn] at h
      obtain ⟨v,rfl⟩ := h
      have hb := (bestMatrix_bound M he).2 v
      omega
  | some T =>
    simp only [answerMatrix,Option.getD_some] at h ⊢
    cases he : scheduleMatrix M T with
    | none => simp only [he,Option.map_none,Option.getD_none,List.not_mem_nil] at h
    | some t =>
      simp only [he,Option.map_some,Option.getD_some,List.mem_ofFn] at h
      obtain ⟨v,rfl⟩ := h
      have ht := scheduleMatrix_bound M he v
      omega

namespace Poly
variable {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))
theorem volumeSchedule (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume (scheduleMatrix (M j) (T j))) 2 := by
  apply volumeOption _ (show Poly s (fun j => 1+n j*(6*T j+2)) 2 from by poly_bound)
  intro j t ht
  exact volume_function_le t (6*T j+1) (by
    intro v; rw [volume_nat]; have := scheduleMatrix_bound (M j) ht v; omega)

theorem volumeBest (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume (bestMatrix (M j) (T j))) 2 := by
  apply volumeOption _ (show Poly s (fun j => (2*T j+1)+(1+n j*(6*T j+2))+1) 2 from by poly_bound)
  intro j a ha
  have hb := bestMatrix_bound (M j) ha
  have hv := volume_function_le a.2 (6*T j+1) (by
    intro v; rw [volume_nat]; have := hb.2 v; omega)
  rw [volume_prod,volume_nat]
  have he : 6*T j+1+1=6*T j+2 := by omega
  rw [he] at hv
  omega
end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Realizer
theorem time_triple_le (n : ℕ) : triple.time n ≤ 100000000000*(n+1)^2 := by
  have h1 := time_add_le n n
  have h2 := time_add_le (n+n) n
  simp only [triple,time_congr,time_comp,time_pair,time_id,volume_prod,volume_nat,Function.comp_apply,id_eq]
  nlinarith
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u2}
theorem time_cardinalMap (d : I → ℕ) {g : ℕ → ℕ} (R : Realizer g) (i : I) (x : Cardinal (d i)) :
    (cardinalMap d R).time i x = R.time (d i) := rfl
theorem time_cardinalValue (d : I → ℕ) (i : I) (x : Cardinal (d i)) :
    (cardinalValue d).time i x = volume x+2 := rfl
theorem time_makeUniverse (n : ℕ) (x : Cardinal n) :
    makeUniverse.time n x = Realizer.range.time n := rfl

def restrictCell : Uniform (fun (i : ℕ × ℕ) (x : Fin i.1 × (Fin i.2 → ℕ)) =>
      (List.ofFn x.2).getD x.1.val 0) :=
    ((((snd.comp (functionListAny Prod.snd)).pair (fst.comp (finValue Prod.fst))).pair zero).comp getElemD)
theorem time_restrictTime (i : ℕ × ℕ) (x : Universe i.1 × (Fin i.2 → ℕ)) :
    restrictTime.time i x = (restrictCell.vectorMapAny Prod.fst).time i x := rfl
theorem time_recode_input {H : Type u3} {α : I → Type u4} {β : I → Type u5} {δ : H → Type u6} {ε : H → Type u7}
    [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ j, Coding (δ j)] [∀ j, Coding (ε j)]
    {g : ∀ j, δ j → ε j} (R : Uniform g) (f : ∀ i, α i → β i)
    (h : ∀ i x, ∃ j y, enc y = enc x ∧ enc (g j y) = enc (f i x))
    (i : I) (x : α i) (j : H) (y : δ j) (hy : enc x = enc y) :
    (R.recode f h).time i x = R.time j y := congrArg R.charge hy
theorem time_scheduleMatrix (n : ℕ) (x : Universe n × (ℕ × Matrix n)) :
    scheduleMatrix.time n x = scheduleMatrixFixed.time (n,x.2.1) (x.1,(Cardinal.mk (),x.2.2)) := by
  unfold scheduleMatrix
  apply time_recode_input
  rfl
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)
theorem restrictCell (v : ∀ j, Fin (n j)) (hn : Poly s n 1) (_hm : Poly s m 1)
    (hv : Poly s (fun j => volume (r j)) 2) :
    Poly s (fun j => Uniform.restrictCell.time (n j,m j) (v j,r j)) 3 := by
  have ha := Poly.finVal hn v
  simp only [Uniform.restrictCell, Uniform.time_comp, Uniform.time_pair, Uniform.time_fst,
    Uniform.time_snd, Uniform.time_functionListAny, Uniform.time_finValue, Uniform.time_zero,
    Function.comp_apply, volume_ofFn]
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)
theorem restrictTime (U : ∀ j, Universe (n j)) (hn : Poly s n 1) (hm : Poly s m 1)
    (hv : Poly s (fun j => volume (r j)) 2) :
    Poly s (fun j => Uniform.restrictTime.time (n j,m j) (U j,r j)) 5 := by
  have hC := restrictCell (fun p : Poly.ListPool (fun j => List.finRange (n j)) => s p.1)
    (fun p => n p.1) (fun p => m p.1) (fun p => r p.1) (fun p => p.2.1)
    (hn.precomp Sigma.fst) (hm.precomp Sigma.fst) (hv.precomp Sigma.fst)
  have hV : Poly (fun p : Poly.ListPool (fun j => List.finRange (n j)) => s p.1)
      (fun p => volume ((List.ofFn (r p.1)).getD p.2.1.val 0)) 2 := by
    apply Poly.of_le (fun p : Poly.ListPool (fun j => List.finRange (n j)) => volume_list_getD_le (List.ofFn (r p.1)) p.2.1.val 0)
    simp only [volume_ofFn,volume_nat]
    have hp := hv.precomp (Sigma.fst : Poly.ListPool (fun j => List.finRange (n j)) → J)
    poly_auto
  poly_auto
theorem restrictTimeBound : Poly
    (fun x : Σ i : ℕ × ℕ, Universe i.1 × (Fin i.2 → ℕ) => x.1.1+x.1.2+volume x.2.2)
    (fun x => Uniform.restrictTime.time x.1 x.2) 5 := by
  let s (x : Σ i : ℕ × ℕ, Universe i.1 × (Fin i.2 → ℕ)) := x.1.1+x.1.2+volume x.2.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hv : Poly s (fun x => volume x.2.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  exact restrictTime s (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2.2) (fun x => x.2.1)
    hn hm (hv.lift (by omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n m : J → ℕ} {d e : ℕ}
theorem volumeRestricted (r : ∀ j, Fin (m j) → ℕ) (hn : Poly s n d)
    (hv : Poly s (fun j => volume (r j)) e) :
    Poly s (fun j => volume (fun v : Fin (n j) => (List.ofFn (r j)).getD v.val 0)) (d+e) := by
  have hB : Poly s (fun j => volume (r j)+1) e := by
    simpa only [Nat.max_zero] using hv.add (Poly.const s 1)
  apply Poly.of_le (fun j => volume_function_le
    (fun v : Fin (n j) => (List.ofFn (r j)).getD v.val 0) (volume (r j)+1) (by
      intro v
      simpa only [volume_ofFn,volume_nat,Nat.mul_zero,Nat.zero_add] using
        volume_list_getD_le (List.ofFn (r j)) v.val 0))
  poly_auto

theorem volumeFullSolve (r : ∀ j, Fin (n j) → Fin (n j) → Prop) [∀ j, DecidableRel (r j)]
    (hn : Poly s n d) : Poly s (fun j => volume (Algorithm.fullSolve (r j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by poly_bound)
  intro j b h
  exact volume_block_le b (fullSolve_small (r j) h).1 (fullSolve_small (r j) h).2
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev PredecessorInput (n : ℕ) := Fin n × (Matrix n × Fin n)
def predecessorCell : Uniform (fun n (x : PredecessorInput n) => x.2.1 x.1 x.2.2) :=
  ((snd.comp fst).pair (fst.pair (snd.comp snd))).comp matrixGet
theorem time_predecessorCount (n : ℕ) (x : Universe n × (Matrix n × Fin n)) :
    predecessorCount.time n x =
      ((((fst.comp universeSet).pair snd).comp predecessorCell.setFilter).comp setCard).time n x := rfl
abbrev PredecessorsInput (n : ℕ) := Fin n × (Universe n × Matrix n)
def predecessorsBody : Uniform (fun n (x : PredecessorsInput n) =>
    Structure.predecessorCount (matrixRel x.2.2) x.1) :=
  ((snd.comp fst).pair ((snd.comp snd).pair fst)).comp predecessorCount
theorem time_predecessors (n : ℕ) (x : Universe n × Matrix n) :
    predecessors.time n x = ((fst.pair id).comp predecessorsBody.vectorMap).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem predecessorCell : Poly (fun x : Σ n, Uniform.PredecessorInput n => x.1)
    (fun x => Uniform.predecessorCell.time x.1 x.2) 3 := by poly_auto
theorem predecessorCount :
    Poly (fun x : Σ n, Universe n × (Matrix n × Fin n) => x.1)
      (fun x => Uniform.predecessorCount.time x.1 x.2) 4 := by poly_auto
theorem predecessorsBody : Poly (fun x : Σ n, Uniform.PredecessorsInput n => x.1)
    (fun x => Uniform.predecessorsBody.time x.1 x.2) 4 := by poly_auto
theorem predecessors :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => Uniform.predecessors.time x.1 x.2) 5 := by
  have hv := Poly.volumePredecessors (fun x : Σ n, Universe n × Matrix n => x.2.2)
    (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
noncomputable section
namespace ThreeMachine.StackCompiler.Uniform
abbrev RankCellInput (n : ℕ) := Fin n × ((Fin n → ℕ) × Fin n)
def rankCellA : Uniform (fun n (x : RankCellInput n) => x.2.1 x.1) :=
  ((snd.comp fst).pair fst).comp functionGet
def rankCellB : Uniform (fun n (x : RankCellInput n) => x.2.1 x.2.2) :=
  ((snd.comp fst).pair (snd.comp snd)).comp functionGet
def rankCellLT := (rankCellA.pair rankCellB).comp natLT
def rankCellEQ := (rankCellA.pair rankCellB).comp (Realizer.eqNat.uniform ℕ)
def rankCellFinLT : Uniform (fun n (x : RankCellInput n) => decide (x.1 < x.2.2)) :=
  ((fst.comp finVal).pair ((snd.comp snd).comp finVal)).comp natLT
def rankCell := rankCellLT.orD (rankCellEQ.andD rankCellFinLT)
theorem time_rankFromCounts (n : ℕ) (x : Universe n × ((Fin n → ℕ) × Fin n)) :
    rankFromCounts.time n x =
      (((((fst.comp universeSet).pair snd).comp rankCell.setFilter).comp setCard).comp
        (Realizer.succ.uniform ℕ)).time n x := by
  simp only [rankFromCounts, time_congr, rankCell, rankCellLT, rankCellEQ, rankCellFinLT, rankCellA, rankCellB]
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
theorem time_natLT_le {I : Type u8} (i : I) (a b : ℕ) :
    (natLT (I := I)).time i (a,b) ≤ 100000000000*(a+b+1)^2 := by
  have h := Realizer.time_le_le b a
  have hn := Realizer.time_not_le (decide (b ≤ a))
  have hv := volume_bool (decide (b ≤ a))
  simp only [natLT,time_congr,time_comp,swap,time_pair,time_fst,time_snd,
    time_uniform,volume_prod,volume_nat]
  have hs : a+b+1 ≤ (a+b+1)^2 := le_self_pow (by omega) (by decide)
  nlinarith
theorem time_finVal (n : ℕ) (v : Fin n) : finVal.time n v = volume v+2 := rfl
end ThreeMachine.StackCompiler.Uniform
end

end

end OAI
