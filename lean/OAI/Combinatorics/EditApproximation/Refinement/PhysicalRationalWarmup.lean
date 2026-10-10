import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmup
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



theorem rationalActualWideActions_toReal {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    (rationalActualWideActions (M := M) parent representatives P).map RationalBellmanAction.toReal =
      actualWideActions (M := M) parent representatives P := by
  simp only [rationalActualWideActions, actualWideActions, List.map_flatMap,
    List.map_map, Function.comp_def, RationalBellmanAction.toReal, Rat.cast_natCast]

def rationalPhysicalBellman {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℚ) (state : PhysicalEntry M J target.length) : ℚ :=
  let parent := physicalSourceInterval source.length state.1
  if hbelow : state.1.1.val < J then
    if parent.hi - parent.lo ≤ 1 then initial state else
      rationalBellman (fun q => initial (state.1, q))
        (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent (representatives state.1) P)
        (fun is => value (physicalChild state.1 hbelow is.1, is.2)) state.2
  else initial state

theorem rationalPhysicalBellman_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℚ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalBellman source target P L initial representatives value state : ℝ) =
      physicalBellman source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives
        (fun s => (value s : ℝ)) state := by
  classical
  unfold rationalPhysicalBellman physicalBellman
  dsimp only
  split_ifs
  · rfl
  · rw [rationalBellman_cast, rationalActualWideActions_toReal]
    simp only [actualWideBellman, Rat.cast_natCast]
  · rfl

def rationalPhysicalWarmup {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ℕ → PhysicalEntry M J target.length → ℚ :=
  rationalWarmup (rationalPhysicalBellman source target P L initial representatives) initial

theorem rationalPhysicalWarmup_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (t : ℕ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalWarmup source target P L initial representatives t state : ℝ) =
      physicalWarmup source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives t state :=
  rationalWarmup_cast _ _ _ (rationalPhysicalBellman_cast source target P L initial representatives) t state

def rationalPhysicalWarmupAverage {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (state : PhysicalEntry M J target.length) : ℚ :=
  (∑ t ∈ range T, rationalPhysicalWarmup source target P L initial representatives t state) / T

theorem rationalPhysicalWarmupAverage_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalWarmupAverage source target P L initial representatives T state : ℝ) =
      physicalWarmupAverage source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives T state := by
  simp only [rationalPhysicalWarmupAverage, physicalWarmupAverage, warmupAverage,
    Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, rationalPhysicalWarmup_cast, physicalWarmup]

end EditApproximation

end OAI
