import OAI.Combinatorics.Ryser.Selection.Definitions
import OAI.Combinatorics.Ryser.Probability.Product

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

noncomputable def poolLaw : FiniteLaw (Pool F n K) :=
  FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))

theorem poolLaw_eq_uniform : poolLaw F n K = FiniteLaw.uniform (Pool F n K) := let _ := instDecidableEqF;
  FiniteLaw.pi_uniform

variable {F n K}

abbrev ExposedAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∈ T} → Point F

abbrev FreshAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∉ T} → Point F

def joinAssignments (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T) :
    Pool F n K :=
  (Equiv.piEquivPiSubtypeProd (fun e : Position n K => e ∈ T)
    (fun _ => Point F)).symm (x, y)

@[simp] theorem joinAssignments_exposed (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∈ T}) : joinAssignments T x y e.val = x e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

@[simp] theorem joinAssignments_fresh (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∉ T}) : joinAssignments T x y e.val = y e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

def frozenPool (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T) :
    Pool F n K := joinAssignments T x (fun _ => 0)

theorem feasible_join_iff (data : Data F n) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T)
    (i : Fin n) (b : Point F) :
    Feasible data T (joinAssignments T x y) i b ↔
      Feasible data T (frozenPool T x) i b := by
  apply feasible_congr
  intro e he
  change joinAssignments T x y (⟨e, he⟩ : {e // e ∈ T}).val =
    joinAssignments T x (fun _ => 0) (⟨e, he⟩ : {e // e ∈ T}).val
  rw [joinAssignments_exposed, joinAssignments_exposed]

theorem poolLaw_prob_split (T : Finset (Position n K)) (P : Pool F n K → Prop) :
    (poolLaw F n K).prob P =
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).expectation (fun x =>
        (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun y => P (joinAssignments T x y))) :=
  by
    rw [poolLaw_eq_uniform]
    exact FiniteLaw.prob_uniform_prod_equiv
      (X := Pool F n K) (Y := ExposedAssignment (F := F) T)
      (Z := FreshAssignment (F := F) T)
      (Equiv.piEquivPiSubtypeProd (fun e : Position n K => e ∈ T)
        (fun _ => Point F)) P

theorem poolLaw_prob_split_le (T : Finset (Position n K))
    (P : Pool F n K → Prop) (b : ℝ)
    (h : ∀ x : ExposedAssignment (F := let _ := instDecidableEqF; F) T,
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => P (joinAssignments T x y)) ≤ b) :
    (poolLaw F n K).prob P ≤ b :=
  FiniteLaw.prob_pi_uniform_split_le (fun e : Position n K => e ∈ T) P b h

theorem poolLaw_prob_split_le_bad (T : Finset (Position n K))
    (P : Pool F n K → Prop) (Bad : ExposedAssignment (F := F) T → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x : ExposedAssignment (F := F) T, ¬Bad x →
      (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => P (joinAssignments T x y)) ≤ b) :
    (poolLaw F n K).prob P ≤
      (FiniteLaw.uniform (ExposedAssignment (F := F) T)).prob Bad + b :=
  by
    rw [poolLaw_prob_split T P]
    simpa only [FiniteLaw.prob_prod_average] using
      FiniteLaw.prob_prod_le_bad_add
        (FiniteLaw.uniform (ExposedAssignment (F := F) T))
        (FiniteLaw.uniform (FreshAssignment (F := F) T))
        (fun z => P (joinAssignments T z.1 z.2)) Bad b hb h

end RyserCoveringCounterexample.Selection

end OAI
