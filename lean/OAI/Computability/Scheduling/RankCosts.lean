import OAI.Computability.Scheduling.ScheduleBounds

namespace OAI

universe u1 u2

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.RankCellInput (n j))
theorem rankCellLT (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellLT.time (n j) (x j)) 4 := by poly_auto
theorem rankCellEQ (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellEQ.time (n j) (x j)) 4 := by poly_auto
theorem rankCellFinLT (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellFinLT.time (n j) (x j)) 4 := by
  simp only [Uniform.rankCellFinLT, Uniform.time_comp, Uniform.time_pair, Uniform.time_fst, Uniform.time_snd, Uniform.time_finVal, Function.comp_apply]
  poly_auto
theorem rankCell (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCell.time (n j) (x j)) 4 := by
  have h1 := rankCellLT n x h
  have h2 := rankCellEQ n x h
  have h3 := rankCellFinLT n x h
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
theorem rankFromCounts (U : ∀ j, Universe (n j)) (r : ∀ j, Fin (n j) → ℕ)
    (v : ∀ j, Fin (n j)) (h : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => Uniform.rankFromCounts.time (n j) (U j,(r j,v j))) 5 := by
  have hc := rankCell (fun p : Poly.ListPool (fun j => (Finset.univ : Finset (Fin (n j))).sort (· ≤ ·)) => n p.1)
    (fun p => (p.2.1,(r p.1,v p.1))) (h.precomp Sigma.fst)
  poly_auto

theorem rank : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.rank.time x.1 x.2) 6 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  have hv := Poly.volumePredecessors (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
  have hC := rankFromCounts (fun p : Poly.ListPool (fun x : Σ n, Universe n × Matrix n => List.finRange x.1) => p.1.1)
    (fun p => p.1.2.1) (fun p => Structure.predecessorCount (matrixRel p.1.2.2))
    (fun p => p.2.1) (hv.precomp Sigma.fst)
  poly_auto

theorem reverseRank (U : ∀ j, Universe (n j)) (r : ∀ j, Fin (n j) → ℕ)
    (h : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => Uniform.reverseRank.time (n j) (U j,r j)) 5 := by poly_auto

theorem ranks (frame : Bool) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.ranks frame).time x.1 x.2) 6 := by
  cases frame
  · poly_auto
  · have hv := Poly.volumeRank (fun x : Σ n, Universe n × Matrix n => x.2.2)
      (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
    have hr := reverseRank (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.1)
      (fun x => Structure.jobRank (matrixRel x.2.2)) hv
    poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev ThresholdInput (n : ℕ) := Fin n × (ℕ × (Fin n → ℕ))
def thresholdA : Uniform (fun n (x : ThresholdInput n) => x.2.2 x.1) :=
  ((snd.comp snd).pair fst).comp functionGet
def thresholdB : Uniform (fun n (x : ThresholdInput n) => x.2.1) := snd.comp fst
def thresholdP (upper : Bool) : Uniform (fun n (x : ThresholdInput n) =>
    decide (if upper then x.2.2 x.1 ≤ x.2.1 else x.2.1 ≤ x.2.2 x.1)) := by
  cases upper
  · exact (thresholdB.pair thresholdA).comp (Realizer.le.uniform ℕ)
  · exact (thresholdA.pair thresholdB).comp (Realizer.le.uniform ℕ)
def thresholdF (upper : Bool) : Uniform (fun n (x : ℕ × (Universe n × (Fin n → ℕ))) =>
    Finset.univ.filter (fun v => decide (if upper then x.2.2 v ≤ x.1 else x.1 ≤ x.2.2 v) = true)) :=
  (((snd.comp fst).comp universeSet).pair (fst.pair (snd.comp snd))).comp (thresholdP upper).setFilter
def thresholdN : Uniform (fun n (_ : Universe n × (Fin n → ℕ)) => List.range (n+2)) :=
  (((fst.comp universeNumber).pair (constant 2)).comp (Realizer.add.uniform ℕ)).comp (Realizer.range.uniform ℕ)
theorem time_thresholdSets (upper : Bool) (n : ℕ) (x : Universe n × (Fin n → ℕ)) :
    (thresholdSets upper).time n x = ((thresholdN.pair id).comp (thresholdF upper).map).time n x := by
  cases upper <;> rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
theorem thresholdP (upper : Bool) (x : ∀ j, Uniform.ThresholdInput (n j))
    (hk : Poly n (fun j => (x j).2.1) 1) (hr : Poly n (fun j => volume (x j).2.2) 2) :
    Poly n (fun j => (Uniform.thresholdP upper).time (n j) (x j)) 4 := by
  cases upper <;> poly_auto

theorem thresholdF (upper : Bool) (U : ∀ j, Universe (n j))
    (r : ∀ j, Fin (n j) → ℕ) (k : J → ℕ)
    (hk : Poly n k 1) (hr : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => (Uniform.thresholdF upper).time (n j) (k j,(U j,r j))) 5 := by
  have hp := thresholdP (fun p : Poly.ListPool (fun j => (Finset.univ : Finset (Fin (n j))).sort (· ≤ ·)) => n p.1)
    upper (fun p => (p.2.1,(k p.1,r p.1))) (hk.precomp Sigma.fst) (hr.precomp Sigma.fst)
  poly_auto

theorem thresholdSets (upper : Bool) (U : ∀ j, Universe (n j))
    (r : ∀ j, Fin (n j) → ℕ) (hr : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => (Uniform.thresholdSets upper).time (n j) (U j,r j)) 6 := by
  have hk : Poly (fun p : Poly.ListPool (fun j => List.range (n j+2)) => n p.1)
      (fun p => p.2.1) 1 := by
    apply Poly.of_le (fun p => (Nat.le_of_lt (List.mem_range.mp p.2.2)))
    exact (Poly.base n).precomp Sigma.fst
  have hF := thresholdF (fun p : Poly.ListPool (fun j => List.range (n j+2)) => n p.1)
    upper (fun p => U p.1) (fun p => r p.1) (fun p => p.2.1) hk (hr.precomp Sigma.fst)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
def triplesE := (universeList.pair (universeList.pair universeList |>.comp product)).comp product
def triplesA := (triplesE.pair id).comp (swap.comp tripleSet).map
def triplesP : Uniform (fun n (x : Finset (Fin n) × Unit) => decide (x.1.card = 3)) :=
  (((fst.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ))
theorem time_triples (n : ℕ) (x : Universe n) :
    triples.time n x = ((triplesA.pair unit).comp triplesP.filter).time n x := rfl

def conesF (frame : Bool) (k : Fin 5) :=
  ((((snd.comp fst).pair ((snd.comp snd).pair fst))).comp (cone frame k))
def conesOne (frame : Bool) (k : Fin 5) :=
  (((fst.comp triples).pair id).comp (conesF frame k).map)
theorem time_cones_cons (frame : Bool) (k : Fin 5) (ks : List (Fin 5))
    (n : ℕ) (x : Universe n × Matrix n) :
    (cones frame (k::ks)).time n x = ((conesOne frame k).pair (cones frame ks) |>.comp append).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem matrixGetFrame (frame : Bool) :
    Poly (fun x : Σ n, Matrix n × (Fin n × Fin n) => x.1)
      (fun x => (Uniform.matrixGetFrame frame).time x.1 x.2) 3 := by
  cases frame <;> poly_auto

theorem conePred (frame : Bool) :
    Poly (fun x : Σ n, Universe n × (Matrix n × Finset (Fin n)) => x.1)
      (fun x => (Uniform.conePred frame).time x.1 x.2) 20 := by
  cases frame <;> poly_auto

theorem cone (frame : Bool) (kind : Fin 5) :
    Poly (fun x : Σ n, Universe n × (Matrix n × Finset (Fin n)) => x.1)
      (fun x => (Uniform.cone frame kind).time x.1 x.2) 20 := by
  have hf := conePred frame
  have hr := conePred (!frame)
  fin_cases kind <;> poly_auto

theorem triplesE : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triplesE.time x.1 x.2) 20 := by poly_auto
theorem triplesA : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triplesA.time x.1 x.2) 20 := by poly_auto
theorem triplesP : Poly (fun x : Σ n, Finset (Fin n) × Unit => x.1)
    (fun x => Uniform.triplesP.time x.1 x.2) 3 := by poly_auto
theorem triples : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triples.time x.1 x.2) 20 := by poly_auto

theorem conesF (frame : Bool) (k : Fin 5) :
    Poly (fun x : Σ n, Finset (Fin n) × (Universe n × Matrix n) => x.1)
      (fun x => (Uniform.conesF frame k).time x.1 x.2) 20 := by poly_auto
theorem conesOne (frame : Bool) (k : Fin 5) :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => (Uniform.conesOne frame k).time x.1 x.2) 100 := by
  have ht := Poly.lengthTriples (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
  poly_auto

theorem cones (frame : Bool) (ks : List (Fin 5)) :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => (Uniform.cones frame ks).time x.1 x.2) 100 := by
  induction ks with
  | nil => poly_auto
  | cons k ks ih =>
    have hCone := cone frame k
    have htr := Poly.lengthTriples (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
    have hlen : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
        (fun x => (ks.flatMap (fun k =>
          ((Structure.tripleList (List.finRange x.1)).map Subtype.val).map (coneSet x.2.2 frame k))).length) 3 := by
      have he (x : Σ n, Universe n × Matrix n) :
          (ks.flatMap (fun k => ((Structure.tripleList (List.finRange x.1)).map Subtype.val).map (coneSet x.2.2 frame k))).length =
          ks.length*(Structure.tripleList (List.finRange x.1)).length := by simp [List.length_flatMap]
      apply Poly.of_le (fun x => (he x).le)
      poly_bound
    poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
