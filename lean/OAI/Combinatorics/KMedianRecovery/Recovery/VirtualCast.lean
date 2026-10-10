import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchWeights

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} {a b : ℕ}
def Virtual.cast (h : a=b) : Virtual V a→Virtual V b := h ▸ id
@[simp] lemma Virtual.cast_real (h : a=b) (v : V) : Virtual.cast h (.real v)=.real v := by subst b;rfl
@[simp] lemma Virtual.cast_ball (h : a=b) (i : Fin a) : Virtual.cast (V:=V) h (.ball i)=.ball (Fin.cast h i) := by subst b;rfl
@[simp] lemma Virtual.cast_permanent (h : a=b) : Virtual.cast h (.permanent : Virtual V a)=.permanent := by subst b;rfl
lemma Virtual.cast_injective (h : a=b) : Function.Injective (Virtual.cast (V:=V) h) := by subst b;exact Function.injective_id
@[simp] lemma Virtual.cast_real_iff (h : a=b) (t : Virtual V a) (v : V) : Virtual.cast h t=.real v ↔ t=.real v := by subst b;rfl
variable [DecidableEq V]
lemma virtual_cast_mem (h : a=b) (S : Finset V) (t : Virtual V a) : Virtual.cast h t∈withGhosts S ↔ t∈withGhosts S := by subst b;rfl
variable [PseudoMetricSpace V]
omit [DecidableEq V] in
lemma virtualDistance_cast (h : a=b) (w : Fin a→V) (r : Fin a→ℝ) (w' : Fin b→V) (r' : Fin b→ℝ)
    (hw : ∀ i,w' (Fin.cast h i)=w i) (hr : ∀ i,r' (Fin.cast h i)=r i) (M : ℝ) (p : V) (t : Virtual V a) :
    virtualDistance w' r' M p (Virtual.cast h t)=virtualDistance w r M p t := by
  subst b
  have hw' : w'=w := funext hw
  have hr' : r'=r := funext hr
  subst w';subst r';rfl
lemma virtualNearest_cast (h : a=b) (w : Fin a→V) (r : Fin a→ℝ) (w' : Fin b→V) (r' : Fin b→ℝ)
    (hw : ∀ i,w' (Fin.cast h i)=w i) (hr : ∀ i,r' (Fin.cast h i)=r i) (S : Finset V) (M : ℝ) (p : V) :
    virtualNearest S w' r' M p=virtualNearest S w r M p := by
  subst b
  have hw' : w'=w := funext hw
  have hr' : r'=r := funext hr
  subst w';subst r';rfl
omit [PseudoMetricSpace V] in
lemma assignmentWeight_cast (h : a=b) (D : Finset V) (ass : V→Virtual V a) (v : V) :
    assignmentWeight D (Virtual.cast h ∘ ass) v=assignmentWeight D ass v := by subst b;rfl
end MetricKMedianRecovery.Completion
namespace MetricKMedianRecovery.RationalSampling
open Completion
variable {n : ℕ}
lemma State.real_length (s : State n) : s.real.leaves.length=s.leaves.length := List.length_map _
def State.center (s : State n) (i : Fin s.leaves.length) : Fin n := s.leaves[i.val].1
def State.radius (s : State n) (i : Fin s.leaves.length) : ℝ := (s.leaves[i.val].2:ℝ)
lemma State.center_cast (s : State n) (i : Fin s.real.leaves.length) :
    s.center (Fin.cast s.real_length i)=Sampling.leafCenter s.real i := by
  simp only [State.center,Sampling.leafCenter,State.real,List.getElem_map]
  rfl
lemma State.radius_cast (s : State n) (i : Fin s.real.leaves.length) :
    s.radius (Fin.cast s.real_length i)=Sampling.leafRadius s.real i := by
  simp only [State.radius,Sampling.leafRadius,State.real,List.getElem_map]
  rfl
variable [PseudoMetricSpace (Fin n)]
noncomputable def State.assignment (S : Finset (Fin n)) (Δ : ℚ) (s : State n) : Fin n→Virtual (Fin n) s.leaves.length :=
  Virtual.cast s.real_length ∘ Sampling.completionAssignment S (Δ:ℝ) s.real
lemma State.assignment_mem (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    s.assignment S Δ p ∈ withGhosts (S\s.deleted) := by
  rw [State.assignment,Function.comp_apply,virtual_cast_mem]
  exact Sampling.completionAssignment_mem S (Δ:ℝ) s.real p
lemma State.assignment_distance (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    virtualDistance s.center s.radius (Δ:ℝ) p (s.assignment S Δ p)=virtualNearest (S\s.deleted) s.center s.radius (Δ:ℝ) p := by
  rw [State.assignment,Function.comp_apply,virtualDistance_cast s.real_length _ _ _ _ s.center_cast s.radius_cast,
    virtualNearest_cast s.real_length _ _ _ _ s.center_cast s.radius_cast]
  exact Sampling.completionAssignment_distance S (Δ:ℝ) s.real p
lemma reference_array_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    (reference δ S Δ s p:ℝ)=virtualNearest (S\s.deleted) s.center s.radius (Δ:ℝ) p := by
  rw [reference_cast δ hδ,Sampling.reference_eq_virtualNearest,
    virtualNearest_cast s.real_length _ _ _ _ s.center_cast s.radius_cast]
  rfl
lemma assignment_array_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    (assignmentWeight δ D S Δ s p:ℝ)=Completion.assignmentWeight D (s.assignment S Δ) p := by
  rw [State.assignment,Completion.assignmentWeight_cast,assignmentWeight_cast δ hδ]
end MetricKMedianRecovery.RationalSampling

end OAI
