import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockNames
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PhaseBalls
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowDerivativeFormula

namespace OAI

/-! Certified rational balls for the quadratic and viscous phase fields.
All oracle calls go to derivatives of the original finite two-table program. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff BigOperators

theorem iteratedDeriv_spatialPhase_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (k : ℕ) (β : List (Fin 3)) (t : ℝ) (x : Space) :
    iteratedDeriv k (fun s => spatialPhase V β (s, x)) t =
      mixedDerivative V (List.replicate k 0 ++ β.map Fin.succ) (t, x) := by
  change iteratedDeriv k (fun s => spatialWord β (fun y => V (s, y)) x) t = _
  exact (mixedDerivative_time_spatial hV k β t x).symm

def initializedVelocityBalls (loader body : Input) (hl : ValidInput loader)
    (hb : ValidInput body) (b : ℕ → RationalSpaceTime) (α : List (Fin 4))
    (N : ℕ) (j : Fin 3) : QBall :=
  vectorNameBall (initializedVelocityName loader body hl hb α b) N j

def quadraticPhaseBalls (loader body : Input) (hl : ValidInput loader)
    (hb : ValidInput body) (b : ℕ → RationalSpaceTime) (β : List (Fin 3))
    (k N : ℕ) (j : Fin 3) : QBall :=
  letI := ShearFlows.neZeroFour
  let α := List.replicate k 0 ++ β.map Fin.succ
  (initializedVelocityBalls loader body hl hb b (α ++ [0]) N j).add
    ((QBall.exact (-1)).mul (initializedVelocityBalls loader body hl hb b α N j))

def viscousPhaseBalls (loader body : Input) (hl : ValidInput loader)
    (hb : ValidInput body) (b : ℕ → RationalSpaceTime) (β : List (Fin 3))
    (k N : ℕ) (j : Fin 3) : QBall :=
  letI := ShearFlows.neZeroFour
  letI := ShearFlows.neZeroThree
  let α := List.replicate k 0 ++ β.map Fin.succ
  let a := fun i : Fin 3 =>
    initializedVelocityBalls loader body hl hb b (α ++ [i.succ, i.succ]) N j
  ((a 0).add (a 1)).add (a 2)

theorem initializedVelocityBalls_contains {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (α : List (Fin 4)) (N : ℕ) (j : Fin 3) :
    (initializedVelocityBalls loader body hl hb b α N j).Contains
      (mixedDerivative (initializedProgram loader body) α y j) :=
  vectorNameBall_contains (initializedVelocityName_spec hl hb α hy) N j

theorem initializedVelocityBalls_converges {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (α : List (Fin 4)) (j : Fin 3) :
    QBall.Converges (fun N => initializedVelocityBalls loader body hl hb b α N j)
      (mixedDerivative (initializedProgram loader body) α y j) :=
  vectorNameBall_converges (initializedVelocityName_spec hl hb α hy) j

theorem quadraticPhaseBalls_contains {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (β : List (Fin 3)) (k N : ℕ) (j : Fin 3) :
    (quadraticPhaseBalls loader body hl hb b β k N j).Contains
      (iteratedDeriv k (fun s => spatialPhase
        (fun z => quadraticPhase (initializedProgram loader body) z.2 z.1) β (s, y.2)) y.1 j) := by
  have hs := initializedProgram_smooth hl hb
  rw [iteratedDeriv_spatialPhase_eq_mixed (quadraticPhase_smooth hs),
    mixedDerivative_quadraticPhase hs (initializedProgram_zero_advection hl hb)]
  let α : List (Fin 4) := List.replicate k 0 ++ β.map Fin.succ
  have h := QBall.contains_add
    (initializedVelocityBalls_contains hl hb hy (α ++ [0]) N j)
    (QBall.contains_mul (QBall.contains_exact (-1))
      (initializedVelocityBalls_contains hl hb hy α N j))
  simpa only [quadraticPhaseBalls, Pi.sub_apply, Rat.cast_neg, Rat.cast_one,
    neg_one_mul, sub_eq_add_neg] using h

theorem quadraticPhaseBalls_converges {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (β : List (Fin 3)) (k : ℕ) (j : Fin 3) :
    QBall.Converges (fun N => quadraticPhaseBalls loader body hl hb b β k N j)
      (iteratedDeriv k (fun s => spatialPhase
        (fun z => quadraticPhase (initializedProgram loader body) z.2 z.1) β (s, y.2)) y.1 j) := by
  have hs := initializedProgram_smooth hl hb
  rw [iteratedDeriv_spatialPhase_eq_mixed (quadraticPhase_smooth hs),
    mixedDerivative_quadraticPhase hs (initializedProgram_zero_advection hl hb)]
  let α : List (Fin 4) := List.replicate k 0 ++ β.map Fin.succ
  have h := (initializedVelocityBalls_converges hl hb hy (α ++ [0]) j).add
    ((QBall.converges_exact (-1)).mul (initializedVelocityBalls_converges hl hb hy α j))
  simpa only [quadraticPhaseBalls, Pi.sub_apply, Rat.cast_neg, Rat.cast_one,
    neg_one_mul, sub_eq_add_neg] using h

theorem viscousPhaseBalls_contains {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (β : List (Fin 3)) (k N : ℕ) (j : Fin 3) :
    (viscousPhaseBalls loader body hl hb b β k N j).Contains
      (iteratedDeriv k (fun s => spatialPhase
        (fun z => viscousPhase (initializedProgram loader body) z.2 z.1) β (s, y.2)) y.1 j) := by
  have hs := initializedProgram_smooth hl hb
  rw [iteratedDeriv_spatialPhase_eq_mixed (viscousPhase_smooth hs), mixedDerivative_viscousPhase hs]
  simp only [Finset.sum_apply, Fin.sum_univ_three]
  exact QBall.contains_add (QBall.contains_add
    (initializedVelocityBalls_contains hl hb hy _ N j)
    (initializedVelocityBalls_contains hl hb hy _ N j))
    (initializedVelocityBalls_contains hl hb hy _ N j)

theorem viscousPhaseBalls_converges {loader body : Input} (hl : ValidInput loader)
    (hb : ValidInput body) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hy : IsFastName b y) (β : List (Fin 3)) (k : ℕ) (j : Fin 3) :
    QBall.Converges (fun N => viscousPhaseBalls loader body hl hb b β k N j)
      (iteratedDeriv k (fun s => spatialPhase
        (fun z => viscousPhase (initializedProgram loader body) z.2 z.1) β (s, y.2)) y.1 j) := by
  have hs := initializedProgram_smooth hl hb
  rw [iteratedDeriv_spatialPhase_eq_mixed (viscousPhase_smooth hs), mixedDerivative_viscousPhase hs]
  simp only [Finset.sum_apply, Fin.sum_univ_three]
  exact ((initializedVelocityBalls_converges hl hb hy _ j).add
    (initializedVelocityBalls_converges hl hb hy _ j)).add
    (initializedVelocityBalls_converges hl hb hy _ j)

end ForcedComputation

end OAI
