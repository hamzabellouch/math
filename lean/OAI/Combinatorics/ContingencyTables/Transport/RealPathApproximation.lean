import OAI.Combinatorics.ContingencyTables.Transport.RealKernelApproximation

namespace OAI

/-! # Keeping an entire finite history during real-kernel comparison -/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def mapKernel (f : X → Y) : FiniteKernel X Y where
  P x y := if f x=y then 1 else 0
  nonnegative x y := by split_ifs <;> norm_num
  substochastic x := by simp

lemma rational_map_push [DecidableEq Y] (p : RationalLaw X) (f : X → Y) :
    (fun y => ((mapLaw p f).mass y:ℝ))=(mapKernel f).push (fun x => (p.mass x:ℝ)) := by
  funext y
  simp only [mapLaw,FiniteKernel.push,mapKernel,Rat.cast_sum,apply_ite,Rat.cast_zero,
    mul_one,mul_zero]

/-- `a` can contain the entire past. Only `read a` is used for the next
random transition; `put a` retains every coordinate needed afterward. -/
def liftKernel (K : FiniteKernel X Y) (read : A → X) (put : A → Y → B) : FiniteKernel A B where
  P a b := (mapKernel (put a)).push (K.P (read a)) b
  nonnegative a b := (mapKernel (put a)).push_nonneg _ (K.nonnegative (read a)) b
  substochastic a := ((mapKernel (put a)).push_mass_le _ (K.nonnegative (read a))).trans
    (K.substochastic (read a))

def liftRational [DecidableEq B] (Q : X → RationalLaw Y)
    (read : A → X) (put : A → Y → B) (a : A) : RationalLaw B := mapLaw (Q (read a)) (put a)

omit [Fintype X] [Fintype A] in
/-- Recording extra coordinates never increases one transition's error. -/
theorem lifted_row_distance [DecidableEq B] (Q : X → RationalLaw Y)
    (K : FiniteKernel X Y) (read : A → X) (put : A → Y → B) (a : A) :
    distance ((rationalKernel (liftRational Q read put)).P a)
      ((liftKernel K read put).P a) ≤ distance ((rationalKernel Q).P (read a)) (K.P (read a)) := by
  change distance (fun b => ((mapLaw (Q (read a)) (put a)).mass b:ℝ))
    ((mapKernel (put a)).push (K.P (read a))) ≤ _
  rw [rational_map_push]
  exact distance_push (mapKernel (put a)) _ _

/-- The joint-history version of the accumulated transition bound. The
recorded state may be a fixed-length vector of every visited state. -/
theorem lifted_walk_distance [DecidableEq A] (Q : X → RationalLaw X)
    (K : FiniteKernel X X) (read : A → X) (put : A → X → A)
    (η : ℝ) (hη : ∀ x,distance ((rationalKernel Q).P x) (K.P x) ≤ η)
    (a : A) (n : ℕ) :
    distance (fun b => ((walkLaw (liftRational Q read put) a n).mass b:ℝ))
      (((liftKernel K read put).power n).P a) ≤ n*η := by
  apply walk_distance
  intro b
  exact (lifted_row_distance Q K read put b).trans (hη (read b))

/-- The first coordinate records which entries of the vector have been
written. Saturation keeps the state space finite even after the horizon. -/
abbrev PathState (X : Type*) (N : ℕ) := Fin (N+1) × (Fin (N+1) → X)

def nextPosition {N : ℕ} (i : Fin (N+1)) : Fin (N+1) :=
  ⟨min (i.val+1) N,Nat.lt_succ_of_le (min_le_right _ _)⟩

def pathRead {N : ℕ} (a : PathState X N) : X := a.2 a.1

def pathPut {N : ℕ} (a : PathState X N) (x : X) : PathState X N :=
  (nextPosition a.1,Function.update a.2 (nextPosition a.1) x)

def pathInitial (N : ℕ) (x : X) : PathState X N := (0,fun _ => x)

/-- Error for the entire recorded path, hence also for any event defined
from all the empirical observations, is at most one row error per step. -/
theorem path_distance (Q : X → RationalLaw X) (K : FiniteKernel X X)
    (η : ℝ) (hη : ∀ x,distance ((rationalKernel Q).P x) (K.P x) ≤ η)
    (N n : ℕ) (x : X) :
    distance (fun a => ((walkLaw (liftRational Q pathRead pathPut) (pathInitial N x) n).mass a:ℝ))
      (((liftKernel K pathRead pathPut).power n).P (pathInitial N x)) ≤ n*η :=
  lifted_walk_distance Q K pathRead pathPut η hη (pathInitial N x) n

end
end ContingencyTables.RealKernelApproximation

end OAI
