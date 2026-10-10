import OAI.Analysis.MarkovType.LatticeCubes
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

abbrev LiftCube (C : FiniteMarkedChain S E) (R : ℕ) :=
  LatticeCube (OrbitRep C) R

def liftAccept (C : FiniteMarkedChain S E) (R : ℕ) (e : E)
    (a : LiftCube C R) : Prop :=
  ∀ j, -(R : ℤ) ≤ latticeCubeVal a j + orbitDisplacement C e j ∧
    latticeCubeVal a j + orbitDisplacement C e j ≤ R

def liftMove (C : FiniteMarkedChain S E) (R : ℕ) (e : E)
    (a : LiftCube C R) (h : liftAccept C R e a) : LiftCube C R :=
  fun j => ⟨latticeCubeVal a j + orbitDisplacement C e j, h j⟩

@[simp] theorem latticeCubeVal_liftMove (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a) :
    latticeCubeVal (liftMove C R e a h) =
      latticeCubeVal a + orbitDisplacement C e := rfl

theorem liftAccept_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a) :
    liftAccept C R (C.rev e) (liftMove C R e a h) := by
  intro j
  simpa only [liftAccept, latticeCubeVal_liftMove, Pi.add_apply,
    orbitDisplacement_rev, Pi.neg_apply, add_neg_cancel_right] using
    latticeCube_coordinate_bounds a j

@[simp] theorem liftMove_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a)
    (h' : liftAccept C R (C.rev e) (liftMove C R e a h)) :
    liftMove C R (C.rev e) (liftMove C R e a h) h' = a := by
  apply latticeCubeVal_injective
  simp [orbitDisplacement_rev]

def liftSource (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : S × LiftCube C R := (C.src x.1, x.2)

def liftTarget (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : S × LiftCube C R := by
  classical
  exact if h : liftAccept C R x.1 x.2 then
    (C.tgt x.1, liftMove C R x.1 x.2 h) else (C.src x.1, x.2)

def liftReverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : E × LiftCube C R := by
  classical
  exact if h : liftAccept C R x.1 x.2 then
    (C.rev x.1, liftMove C R x.1 x.2 h) else x

theorem liftReverse_involutive (C : FiniteMarkedChain S E) (R : ℕ) :
    Function.Involutive (liftReverse C R) := by
  classical
  rintro ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · have h' := liftAccept_reverse C R e a h
    have hfirst : liftReverse C R (e, a) = (C.rev e, liftMove C R e a h) := by
      simp only [liftReverse, dite_eq_left h]
    rw [hfirst]
    simp only [liftReverse, dite_eq_left h']
    exact Prod.ext (C.rev_rev e) (liftMove_reverse C R e a h h')
  · simp [liftReverse, h]

theorem liftSource_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftSource C R (liftReverse C R x) = liftTarget C R x := by
  classical
  rcases x with ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · simp [liftSource, liftTarget, liftReverse, h, C.src_rev]
  · simp [liftSource, liftTarget, liftReverse, h]

theorem liftTarget_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftTarget C R (liftReverse C R x) = liftSource C R x := by
  rw [← liftSource_reverse, liftReverse_involutive]

def liftMass (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) : ℝ :=
  C.π x.1 / (Fintype.card (LiftCube C R) : ℝ)

theorem liftMass_nonneg (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) : 0 ≤ liftMass C R x :=
  div_nonneg (C.π_nonneg x.1) (Nat.cast_nonneg _)

theorem sum_liftMass (C : FiniteMarkedChain S E) (R : ℕ) :
    ∑ x, liftMass C R x = 1 := by
  classical
  have hc : (Fintype.card (LiftCube C R) : ℝ) ≠ 0 :=
    ne_of_gt (latticeCube_card_real_pos R)
  have hsum (s : S) :
      (∑ _a : LiftCube C R, C.π s / (Fintype.card (LiftCube C R) : ℝ)) =
        C.π s := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hc]
  simpa only [liftMass, Fintype.sum_prod_type, hsum] using C.sum_π

theorem sum_liftOutgoing (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) :
    (∑ e : E × LiftCube C R, if liftSource C R e = x then C.q e.1 else 0) = 1 := by
  classical
  rcases x with ⟨s, a⟩
  rw [← C.sum_q s]
  simp only [liftSource, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : C.src e = s <;> simp [Prod.mk.injEq, h]

theorem lift_edge_balance (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftMass C R (liftSource C R x) * C.q x.1 =
      liftMass C R (liftTarget C R x) * C.q (liftReverse C R x).1 := by
  classical
  rcases x with ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · simp only [liftSource, liftTarget, liftReverse, h, dite_true, liftMass
      ]
    calc
      C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e =
          (C.π (C.src e) * C.q e) / (Fintype.card (LiftCube C R) : ℝ) := by ring
      _ = (C.π (C.tgt e) * C.q (C.rev e)) /
          (Fintype.card (LiftCube C R) : ℝ) := by rw [C.balance]
      _ = C.π (C.tgt e) / (Fintype.card (LiftCube C R) : ℝ) *
          C.q (C.rev e) := by ring
  · simp [liftSource, liftTarget, liftReverse, h]

def latticeLift (C : FiniteMarkedChain S E) (R : ℕ) :
    FiniteMarkedChain (S × LiftCube C R) (E × LiftCube C R) where
  π := liftMass C R
  π_nonneg := liftMass_nonneg C R
  sum_π := sum_liftMass C R
  src := liftSource C R
  tgt := liftTarget C R
  rev := liftReverse C R
  rev_rev := liftReverse_involutive C R
  src_rev := liftSource_reverse C R
  tgt_rev := liftTarget_reverse C R
  q := fun e => C.q e.1
  q_nonneg := fun e => C.q_nonneg e.1
  sum_q := fun s => by
    rw [← sum_liftOutgoing C R s]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : liftSource C R e = s <;> simp only [he, ite_true, ite_false]
  balance := lift_edge_balance C R

def latticeTransition (C : FiniteMarkedChain S E) (R : ℕ)
    (x y : S × LiftCube C R) : ℝ := by
  classical
  exact ∑ e : E × LiftCube C R,
    if liftSource C R e = x ∧ liftTarget C R e = y then C.q e.1 else 0

theorem latticeTransition_formula (C : FiniteMarkedChain S E) (R : ℕ)
    (s : S) (a : LiftCube C R) (y : S × LiftCube C R) :
    latticeTransition C R (s, a) y =
      ∑ e : E, if C.src e = s ∧ liftTarget C R (e, a) = y then C.q e else 0 := by
  classical
  unfold latticeTransition
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have heq : (fun b : LiftCube C R =>
      if liftSource C R (e, b) = (s, a) ∧ liftTarget C R (e, b) = y
      then C.q e else 0) =
      (fun b => if b = a then
        (if C.src e = s ∧ liftTarget C R (e, a) = y then C.q e else 0)
        else 0) := by
    funext b
    by_cases hb : b = a
    · subst b
      simp [liftSource]
    · simp [liftSource, Prod.mk.injEq, hb]
  rw [heq]
  simp

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def liftPotential (C : FiniteMarkedChain S E) (g : E → V) (R : ℕ)
    (x : S × LiftCube C R) : V := labelLinear C g (latticeCubeVal x.2)

theorem liftPotential_increment_accepted (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (R : ℕ) (e : E) (a : LiftCube C R)
    (h : liftAccept C R e a) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) = g e := by
  classical
  simp only [liftTarget, h, dite_true, liftSource, liftPotential,
    latticeCubeVal_liftMove]
  rw [labelLinear_add, labelLinear_displacement C hg]
  abel

theorem liftPotential_increment_rejected (C : FiniteMarkedChain S E)
    (g : E → V) (R : ℕ) (e : E) (a : LiftCube C R)
    (h : ¬liftAccept C R e a) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) = 0 := by
  classical
  simp [liftTarget, liftSource, h]

theorem liftPotential_increment (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (R : ℕ) (e : E) (a : LiftCube C R) :
    liftPotential C g R (liftTarget C R (e, a)) -
      liftPotential C g R (liftSource C R (e, a)) =
      if liftAccept C R e a then g e else 0 := by
  classical
  split_ifs with h
  · exact liftPotential_increment_accepted C hg R e a h
  · exact liftPotential_increment_rejected C g R e a h

end MarkovSuperreflexivity

end

end OAI
