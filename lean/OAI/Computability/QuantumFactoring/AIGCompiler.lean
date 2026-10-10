import Mathlib
import OAI.Computability.QuantumFactoring.BooleanVector

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

open BooleanNetwork Std.Sat

namespace AIGCompiler

variable {n : ℕ} (g : AIG (Fin n))

def graphWire (i : Fin g.decls.size) : Fin (n + g.decls.size) := Fin.natAdd n i

def faninNet (f : AIG.Fanin) : BooleanNetwork (n + g.decls.size) 1 :=
  let v := if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩) else constant false
  if f.invert then v.bnot else v

lemma fanin_count (f : AIG.Fanin) : (faninNet g f).net.count ≤ 2 := by
  have hv : (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1).net.count ≤ 1 := by
    by_cases h : f.gate < g.decls.size
    · rw [dite_eq_left h]; simp
    · rw [dite_eq_right h]; simp
  unfold faninNet
  generalize (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1) = v at *
  cases hf : f.invert
  · change v.net.count ≤ 2
    omega
  · change v.bnot.net.count ≤ 2
    rw [count_bnot]
    omega

lemma fanin_eval (f : AIG.Fanin) (h : f.gate < g.decls.size) (x : Fin (n+g.decls.size) → Bool) :
    (faninNet g f).eval x 0 = Bool.xor (x (graphWire g ⟨f.gate,h⟩)) f.invert := by
  simp only [faninNet, dite_eq_left h]
  cases f.invert <;> simp

def nodeNet (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) 1 :=
  match g.decls[i.val] with
  | .false => constant false
  | .atom v => bit (Fin.castAdd g.decls.size v)
  | .gate a b => (faninNet g a).band (faninNet g b)

lemma node_count (i : Fin g.decls.size) : (nodeNet g i).net.count ≤ 5 := by
  unfold nodeNet
  cases g.decls[i.val] with
  | false => simp
  | atom v => simp
  | gate a b =>
    rw [count_band]
    have := fanin_count g a
    have := fanin_count g b
    omega

def nodeDenote (x : Fin n → Bool) (i : Fin g.decls.size) : Bool :=
  AIG.denote x ⟨g, ⟨i.val, false, i.isLt⟩⟩

lemma node_eval (i : Fin g.decls.size) (x : Fin n → Bool)
    (y : Fin (n+g.decls.size) → Bool)
    (hi : ∀ j, y (j.castAdd g.decls.size) = x j)
    (hg : ∀ j : Fin g.decls.size, j.val < i.val → y (graphWire g j) = nodeDenote g x j) :
    (nodeNet g i).eval y 0 = nodeDenote g x i := by
  unfold nodeNet nodeDenote
  cases h : g.decls[i.val] with
  | false => simpa only [eval_constant] using (AIG.denote_idx_false (assign := x) (invert := false) h).symm
  | atom v => simpa only [eval_bit, hi, Bool.xor_false] using (AIG.denote_idx_atom (assign := x) (invert := false) h).symm
  | gate a b =>
    have hab := g.hdag i.isLt h
    dsimp only
    rw [eval_band, fanin_eval g a (by omega), fanin_eval g b (by omega),
      hg ⟨a.gate, by omega⟩ hab.1, hg ⟨b.gate, by omega⟩ hab.2]
    have he := (AIG.denote_idx_gate (assign := x) (invert := false) h).symm
    simpa only [AIG.denote, nodeDenote, Bool.xor_false] using he

def nodeStep (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) (n+g.decls.size) :=
  assign (graphWire g i) (nodeNet g i)

def partialGraph (g : AIG (Fin n)) : (k : ℕ) → k ≤ g.decls.size →
    BooleanNetwork (n+g.decls.size) (n+g.decls.size)
  | 0, _ => select id
  | k+1, h => (partialGraph g k (by omega)).comp (nodeStep g ⟨k, by omega⟩)

lemma graph_count (k : ℕ) (h : k ≤ g.decls.size) : (partialGraph g k h).net.count ≤ 5*k := by
  induction k with
  | zero => simp [partialGraph]
  | succ k ih =>
    rw [partialGraph, count_comp, nodeStep, count_assign]
    have := node_count g ⟨k, by omega⟩
    have := ih (by omega)
    omega

lemma graph_input (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool) (j : Fin n) :
    (partialGraph g k h).eval x (j.castAdd g.decls.size) = x (j.castAdd g.decls.size) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign, Function.update_of_ne, ih]
    intro he
    have := congrArg Fin.val he
    simp [graphWire] at this
    omega

lemma graph_value (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool)
    (j : Fin g.decls.size) (hj : j.val < k) :
    (partialGraph g k h).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign]
    by_cases hjk : j.val = k
    · have hj' : j = ⟨k, by omega⟩ := Fin.ext hjk
      rw [hj', Function.update_self]
      apply node_eval g
      · exact fun i => graph_input g k (by omega) x i
      · exact fun i hi => ih (by omega) i (by simpa using hi)
    · rw [Function.update_of_ne]
      · exact ih (by omega) j (by omega)
      · intro he
        have := congrArg Fin.val he
        simp [graphWire] at this
        omega

/-- The circuit interpreter's own, already verified, AIG semantics is preserved
by a retained-trace network of at most five nodes per AIG declaration. -/
theorem graph_correct (x : Fin (n+g.decls.size) → Bool) (j : Fin g.decls.size) :
    (partialGraph g g.decls.size le_rfl).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j :=
  graph_value g _ le_rfl x j j.isLt

/-- Compile designated references of an AIG, starting only with its input bits.
All graph slots and their retained evaluation traces are genuine ancillas. -/
def compile {m : ℕ} (refs : Fin m → AIG.Ref g) : BooleanNetwork n m :=
  ((padRight n g.decls.size).comp (partialGraph g g.decls.size le_rfl)).comp
    (vector (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert)))

lemma compile_count {m : ℕ} (refs : Fin m → AIG.Ref g) :
    (compile g refs).net.count ≤ 6*g.decls.size + 2*m := by
  rw [compile, count_comp, count_comp, count_padRight]
  have hg := graph_count g g.decls.size le_rfl
  have hv := count_vector_le (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert))
    (fun i => fanin_count g (AIG.Fanin.mk (refs i).gate (refs i).invert))
  omega

lemma compile_correct {m : ℕ} (refs : Fin m → AIG.Ref g) (x : Fin n → Bool) (i : Fin m) :
    (compile g refs).eval x i = AIG.denote x ⟨g, refs i⟩ := by
  rw [compile, eval_comp, eval_comp, eval_vector, fanin_eval g _ (by simpa using (refs i).hgate),
    graph_correct, eval_padRight]
  have he : (fun j : Fin n => Fin.append x (fun _ : Fin g.decls.size => false)
      (j.castAdd g.decls.size)) = x := by funext j; exact Fin.append_left ..
  rw [he]
  simp only [nodeDenote, AIG.denote, Bool.xor_false, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

/-- The whole output BitVec of a native, already verified, arithmetic bitblaster
is now a Boolean network with a linear overhead in its AIG graph size. -/
def compileVec {w : ℕ} (refs : AIG.RefVec g w) : BooleanNetwork n w :=
  compile g (fun i => refs.get i.val i.isLt)

lemma compileVec_correct {w : ℕ} (refs : AIG.RefVec g w) (x : Fin n → Bool) (i : Fin w) :
    (compileVec g refs).eval x i = AIG.denote x ⟨g, refs.get i.val i.isLt⟩ :=
  compile_correct ..

lemma compileVec_count {w : ℕ} (refs : AIG.RefVec g w) :
    (compileVec g refs).net.count ≤ 6*g.decls.size + 2*w := compile_count ..

end AIGCompiler
end ExactQuantumFactoring


end

end OAI
