import OAI.Computability.Scheduling.RankCosts

namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]
theorem time_finEmpty (i : I) (xs : List (α i)) : finEmpty.time i xs = 2 := rfl
theorem time_finCons (k : ℕ) (i : I) (x : α i × (Fin k → α i)) :
    (finCons k).time i x = volume x+2 := rfl

def assignmentsInner (k : ℕ) : Uniform (fun i (x : α i × List (Fin k → α i)) =>
    x.2.map (fun f => (Fin.cons x.1 f : Fin (k+1) → α i))) :=
  ((snd.pair fst).comp (swap.comp (finCons k)).map)
def assignmentsStep (k : ℕ) : Uniform (fun i (x : List (α i) × List (Fin k → α i)) =>
    x.1.flatMap (fun a => x.2.map (fun f => (Fin.cons a f : Fin (k+1) → α i)))) := (assignmentsInner k).flatMap
theorem time_assignments_succ (k : ℕ) (i : I) (xs : List (α i)) :
    (assignments (k+1)).time i xs =
      (((id.pair (assignments k)).comp (assignmentsStep k))).time i xs := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (k : ℕ)

theorem assignmentsInner (ys : ∀ j, List (Fin k → Finset (Fin (n j))))
    (a : ∀ j, Finset (Fin (n j))) (hl : Poly n (fun j => (ys j).length) (3*k)) :
    Poly n (fun j => (Uniform.assignmentsInner (α := fun n => Finset (Fin n)) k).time (n j) (a j,ys j)) (6*k+5) := by
  have hv : Poly n (fun j => volume (ys j)) (3*k+2) := by poly_auto
  have hdegree :
      max
        (max
          (max (max (max (max (2 * 1) (3 * k + 2)) 0) (max (max (2 * 1) (3 * k + 2)) 0))
            (0 + max (max (max (max (2 * 1) (3 * k + 2)) (3 * k + 2)) (2 * 1)) 0))
          (3 * k + max 2 (max (3 * k + 2) (max (2 * 1) (3 * k + 2)))))
        (0 + max (max (3 * k + 2) (2 * 1)) 0) ≤ 6 * k + 5 := by omega
  poly_auto

theorem assignmentsStep (xs : ∀ j, List (Finset (Fin (n j))))
    (ys : ∀ j, List (Fin k → Finset (Fin (n j))))
    (hl : Poly n (fun j => (xs j).length) 3)
    (hL : Poly n (fun j => (ys j).length) (3*k)) :
    Poly n (fun j => (Uniform.assignmentsStep (α := fun n => Finset (Fin n)) k).time (n j) (xs j,ys j)) (9*k+10) := by
  have hv : Poly n (fun j => volume (ys j)) (3*k+2) := by poly_auto
  have hx : Poly n (fun j => volume (xs j)) 5 := by poly_auto
  have hI := assignmentsInner (fun p : Poly.ListPool xs => n p.1) k
    (fun p => ys p.1) (fun p => p.2.1) (hL.precomp Sigma.fst)
  have hdegree : 3 + (3 * k + 2) +
      max (6 * k + 5) (max 5 (max (3 * k + 2) (3 + (3 * k + 2)))) ≤ 9 * k + 10 := by omega
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (xs : ∀ j, List (Finset (Fin (n j))))
theorem assignments (hl : Poly n (fun j => (xs j).length) 3) (k : ℕ) :
    Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) k).time (n j) (xs j)) (9*k+10) := by
  have hx : Poly n (fun j => volume (xs j)) 5 := by poly_auto
  induction k with
  | zero =>
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) 0).time (n j) (xs j)) 10
    poly_auto
  | succ k ih =>
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) (k+1)).time (n j) (xs j)) (9*(k+1)+10)
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) k).time (n j) (xs j)) (9*k+10) at ih
    have hL : Poly n (fun j => (Structure.assignments (xs j) k).length) (3*k) := by
      simpa only [Structure.assignments_length] using hl.pow k
    have hV : Poly n (fun j => volume (Structure.assignments (xs j) k)) (3*k+2) := by poly_auto
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) (k+1)).time (n j) (xs j)) (9*(k+1)+10)
    have hStep := assignmentsStep n k xs (fun j => Structure.assignments (xs j) k) hl hL
    have hdegree :
      max (max (max (max 5 (9 * k + 10)) (0 + max (max (max 5 5) (3 * k + 2)) 0)) (9 * k + 10))
        (0 + max (max 5 (3 * k + 2)) 0) ≤ 9 * (k + 1) + 10 := by omega
    poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable {K : ℕ} (r : ∀ j, Fin K → Finset (Fin (n j)))

theorem evalTemplate (p : Formula (Fin K)) :
    Poly n (fun j => (Uniform.evalTemplate p).time (n j) (U j,r j)) 4 := by
  induction p with
  | leaf a b => cases b <;> simp only [Uniform.evalTemplate,Bool.false_eq_true,↓reduceDIte] <;> poly_auto
  | conj p q ihp ihq => poly_auto
  | disj p q ihp ihq => poly_auto

theorem evalTemplates (ps : List (Formula (Fin K))) :
    Poly n (fun j => (Uniform.evalTemplates ps).time (n j) (U j,r j)) 4 := by
  induction ps with
  | nil => poly_auto
  | cons p ps ih =>
    have hc := evalTemplate n U r p
    have hl : Poly n (fun j => (ps.map (Formula.evalFinset (r j))).length) 0 := by
      simpa only [List.length_map] using Poly.const n ps.length
    poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def atomSetsC : Uniform (fun n (_ : Universe n × Matrix n) => [∅, (Finset.univ : Finset (Fin n))]) :=
  (((fst.comp setEmpty).pair (((fst.comp universeSet).pair nil).comp cons)).comp cons)
def atomSetsT := ((thresholds Bool.false).pair (thresholds true)).comp append
def atomSetsD := ((cones Bool.false (List.finRange 5)).pair (cones true (List.finRange 5))).comp append
theorem time_atomSets (n : ℕ) (x : Universe n × Matrix n) :
    atomSets.time n x = ((atomSetsC.pair atomSetsT).comp append |>.pair atomSetsD |>.comp append).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type}
theorem lengthThresholds (n : J → ℕ) (M : ∀ j, Matrix (n j)) (frame : Bool) :
    Poly n (fun j => ([Bool.false,true].flatMap (fun upper => (List.range (n j+2)).map
      (fun k => Finset.univ.filter (fun v => if upper then
        (if frame then reverseJobRank (matrixRel (M j)) else jobRank (matrixRel (M j))) v ≤ k
        else k ≤ (if frame then reverseJobRank (matrixRel (M j)) else jobRank (matrixRel (M j))) v)))).length) 1 := by
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.length_map,List.length_range]
  poly_auto

theorem lengthCones (n : J → ℕ) (M : ∀ j, Matrix (n j)) (frame : Bool) (ks : List (Fin 5)) :
    Poly n (fun j => (ks.flatMap (fun k => ((tripleList (List.finRange (n j))).map Subtype.val).map
      (coneSet (M j) frame k))).length) 3 := by
  have htr := Poly.lengthTriples (Poly.size n)
  have he (j : J) :
      (ks.flatMap (fun k => ((tripleList (List.finRange (n j))).map Subtype.val).map
        (coneSet (M j) frame k))).length = ks.length*(tripleList (List.finRange (n j))).length := by
    simp [List.length_flatMap]
  apply Poly.of_le (fun j => (he j).le)
  poly_bound

theorem thresholds (frame : Bool) :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => (Uniform.thresholds frame).time x.1 x.2) 6 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let r (x : Σ n, Universe n × Matrix n) :=
    if frame then Structure.reverseJobRank (matrixRel x.2.2) else Structure.jobRank (matrixRel x.2.2)
  have hv : Poly n (fun x => volume (r x)) 2 := by
    cases frame
    · exact Poly.volumeRank (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
    · exact Poly.volumeReverseRank (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
  have hF := thresholdSets n Bool.false (fun x => x.2.1) r hv
  have hT := thresholdSets n true (fun x => x.2.1) r hv
  poly_auto

theorem atomSetsC : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSetsC.time x.1 x.2) 3 := by poly_auto
theorem atomSetsT : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSetsT.time x.1 x.2) 6 := by
  have hF := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) Bool.false
  have hT := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) true
  poly_auto
theorem atomSetsD : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSetsD.time x.1 x.2) 100 := by
  have hF := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) Bool.false (List.finRange 5)
  have hT := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) true (List.finRange 5)
  poly_auto
theorem atomSets : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSets.time x.1 x.2) 100 := by
  have htF := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) Bool.false
  have htT := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) true
  have hF := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) Bool.false (List.finRange 5)
  have hT := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) true (List.finRange 5)
  poly_auto

theorem evalTemplatesCanonical {K : ℕ} (ps : List (Formula (Fin K))) :
    Poly (fun x : Σ n, Universe n × (Fin K → Finset (Fin n)) => x.1)
      (fun x => (Uniform.evalTemplates ps).time x.1 x.2) 4 :=
  evalTemplates (fun x : Σ n, Universe n × (Fin K → Finset (Fin n)) => x.1) (fun x => x.2.1) (fun x => x.2.2) ps

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure
def familyAssignments (K : ℕ) := atomSets.comp (assignments K)
def familyEval (K : ℕ) := swap.comp (evalTemplates (Formula.templates K))
def familyFlatten (K : ℕ) := (familyEval K).flatMap
theorem time_family (K n : ℕ) (x : Universe n × Matrix n) :
    (family K).time n x = (((familyAssignments K).pair fst).comp (familyFlatten K)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
theorem familyAssignments (K : ℕ) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.familyAssignments K).time x.1 x.2) (max (max 100 (9*K+10)) 5) := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let xs (x : Σ n, Universe n × Matrix n) :=
    (Atomic.alphabet (List.finRange x.1)).map
      (Atomic.finsetEval (matrixRel x.2.2) (Structure.jobRank (matrixRel x.2.2)) (Structure.reverseJobRank (matrixRel x.2.2)))
  have hl : Poly n (fun x => (xs x).length) 3 := by
    simpa only [xs,List.length_map] using Poly.lengthAlphabet (Poly.size n)
  have hA := assignments n xs hl K
  have hAL : Poly n (fun x => (Structure.assignments (xs x) K).length) (3*K) := by
    simpa only [Structure.assignments_length] using hl.pow K
  have hAV : Poly n (fun x => volume (Structure.assignments (xs x) K)) (3*K+2) := by poly_auto
  poly_auto
theorem familyEval (K : ℕ) : Poly (fun x : Σ n, (Fin K → Finset (Fin n)) × Universe n => x.1)
    (fun x => (Uniform.familyEval K).time x.1 x.2) 4 := by
  poly_auto

theorem familyFlatten {J : Type} (K : ℕ) (n : J → ℕ) (U : ∀ j, Universe (n j))
    (xs : ∀ j, List (Fin K → Finset (Fin (n j))))
    (hl : Poly n (fun j => (xs j).length) 30000) :
    Poly n (fun j => (Uniform.familyFlatten K).time (n j) (xs j,U j)) 60004 := by
  let P := Σ j, {a : Fin K → Finset (Fin (n j)) // a ∈ xs j}
  let sp (p : P) := n p.1
  have ht : Poly sp (fun p => (Uniform.familyEval K).time (n p.1) (p.2.1,U p.1)) 4 := by
    exact (familyEval K).precomp (fun p : P => (⟨n p.1,(p.2.1,U p.1)⟩ : Σ m, (Fin K → Finset (Fin m)) × Universe m))
  have hx : Poly n (fun j => volume (xs j)) 30002 := by poly_auto
  have he : Poly n (fun j => volume (U j)) 2 := by poly_auto
  have hlout : Poly sp (fun p => ((Formula.templates K).map (Formula.evalFinset p.2.1)).length) 0 := by
    simpa only [List.length_map] using Poly.const sp (Formula.templates K).length
  have hv : Poly sp (fun p => volume ((Formula.templates K).map (Formula.evalFinset p.2.1))) 2 := by
    poly_auto
  exact (Poly.flatMapTime (α := fun n => Fin K → Finset (Fin n)) n xs U (Uniform.familyEval K) hl ht hx he hv).lift (by decide)

theorem familyBound (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.family K).time x.1 x.2) 90010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let xs (x : Σ n, Universe n × Matrix n) :=
    (Atomic.alphabet (List.finRange x.1)).map
      (Atomic.finsetEval (matrixRel x.2.2) (Structure.jobRank (matrixRel x.2.2)) (Structure.reverseJobRank (matrixRel x.2.2)))
  have hl : Poly n (fun x => (xs x).length) 3 := by
    simpa only [xs,List.length_map] using Poly.lengthAlphabet (Poly.size n)
  have hAL : Poly n (fun x => (Structure.assignments (xs x) K).length) 30000 := by
    simpa only [Structure.assignments_length] using (hl.pow K).lift (Nat.mul_le_mul_left 3 hk)
  have hAV : Poly n (fun x => volume (Structure.assignments (xs x) K)) 30002 := by poly_auto
  have hA := (familyAssignments K).lift (show max (max 100 (9*K+10)) 5 ≤ 90010 by omega)
  have hF := familyFlatten K n (fun x => x.2.1) (fun x => Structure.assignments (xs x) K) hAL
  poly_auto
theorem family : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.family 10000).time x.1 x.2) 90010 := familyBound 10000 (by omega)

end ThreeMachine.StackCompiler.Costs
end

section

end

end OAI
