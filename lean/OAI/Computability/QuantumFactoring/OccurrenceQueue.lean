import Mathlib
import OAI.Computability.QuantumFactoring.TraceBounds

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- The full occurrence preorder; equal labels under different parents are
retained as different list elements. This is only a correctness invariant,
never used as the modulus-input physical circuit's initializer. -/
def preorder (m : ℕ) : List ℕ :=
  m::((children m).attach.flatMap (fun d=>preorder d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

lemma preorder_eq (m : ℕ) : preorder m=m::(children m).flatMap preorder := by
  rw [preorder]
  congr 1
  rw [List.flatMap_subtype (g:=preorder) (fun _ _=>rfl),List.unattach_attach]

lemma visits_eq_preorder {m depth : ℕ} (hd : level m depth=[]) :
    visits depth m=preorder m := by
  induction depth generalizing m with
  | zero=>simp only [level,List.cons_ne_self] at hd
  | succ d ih=>
    rw [visits,preorder_eq]
    congr 1
    apply List.flatMap_congr
    intro a ha
    exact ih (DataProducer.child_level_empty hd ha)

lemma preorder_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (preorder m).length ≤ 2*n^2 := by
  rw [←visits_eq_preorder (level_empty hm hb)]
  simpa only [pow_two,Nat.mul_assoc] using visits_length_le hm hb (2*n)

lemma preorder_nonempty (m : ℕ) : preorder m≠[] := by
  rw [preorder_eq]
  exact List.cons_ne_nil _ _

def forest (xs : List ℕ) : List ℕ := xs.flatMap preorder

def advance : List ℕ→List ℕ
  | []=>[]
  | m::ms=>children m++ms

lemma forest_advance (m : ℕ) (ms : List ℕ) :
    forest (m::ms)=m::forest (advance (m::ms)) := by
  simp only [forest,List.flatMap_cons,preorder_eq,List.cons_append,advance,List.flatMap_append]

lemma queue_length_le (xs : List ℕ) : xs.length ≤ (forest xs).length := by
  induction xs with
  | nil=>simp [forest]
  | cons m ms ih=>
    rw [forest_advance,List.length_cons,List.length_cons]
    have he : (forest (advance (m::ms))).length=
        ((children m).flatMap preorder).length+(forest ms).length := by
      simp only [forest,advance,List.flatMap_append,List.length_append]
    rw [he]
    omega

def run : ℕ→List ℕ→List ℕ
  | 0,xs=>xs
  | t+1,xs=>run t (advance xs)

lemma forest_run (t : ℕ) (xs : List ℕ) : forest (run t xs)=(forest xs).drop t := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>
    rw [run,ih]
    cases xs with
    | nil=>simp [advance,forest]
    | cons m ms=>rw [forest_advance,List.drop_succ_cons]

lemma forest_eq_nil_iff {xs : List ℕ} : forest xs=[] ↔ xs=[] := by
  constructor
  · intro h
    have hh := queue_length_le xs
    rw [h,List.length_nil] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    rfl

/-- Exactly the polynomial clock used by the physical queue suffices for EVERY
occurrence, not just every distinct label. -/
theorem run_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : run (2*n^2) [m]=[] := by
  apply forest_eq_nil_iff.mp
  rw [forest_run]
  have he : forest [m]=preorder m := by simp [forest]
  rw [he]
  exact List.drop_eq_nil_of_le (preorder_length_le hm hb)

lemma run_queue_length {m n t : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (run t [m]).length ≤ 2*n^2 := by
  have h := queue_length_le (run t [m])
  rw [forest_run] at h
  have he : forest [m]=preorder m := by simp [forest]
  rw [he,List.length_drop] at h
  exact h.trans ((Nat.sub_le _ _).trans (preorder_length_le hm hb))

lemma advance_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) :
    ∀ a∈advance xs,2 ≤ a ∧ a < B := by
  cases xs with
  | nil=>simp [advance]
  | cons m ms=>
    intro a ha
    have hm := hx m (by simp)
    rcases List.mem_append.mp ha with hd | ht
    · have hb := child_bounds hd
      exact ⟨hb.1,hb.2.trans hm.2⟩
    · exact hx a (by simp [ht])

lemma run_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) (t : ℕ) :
    ∀ a∈run t xs,2 ≤ a ∧ a < B := by
  induction t generalizing xs with
  | zero=>exact hx
  | succ t ih=>exact ih (advance_bounds hx)

lemma run_succ_right (t : ℕ) (xs : List ℕ) : run (t+1) xs=advance (run t xs) := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>rw [run,ih];rfl

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
