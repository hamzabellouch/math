import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArray
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.StacksLookup
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CenterPathsSignedCenter

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses

theorem time_in_stage {ν K D t : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (ht : 1 ≤ t) :
    ∃ n, t ∈ Icc (startTime ν K D n) (startTime ν K D (n + 1)) := by
  have hex : ∃ n, t < startTime ν K D (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt t
    refine ⟨n, ?_⟩
    have hs := startTime_ge hν hK hD (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hs
    linarith
  let n := Nat.find hex
  refine ⟨n, ?_, (Nat.find_spec hex).le⟩
  cases hn : n with
  | zero => simpa only [hn, startTime] using ht
  | succ k =>
    have hk : ¬t < startTime ν K D (k + 1) := Nat.find_min hex (by omega : k < Nat.find hex)
    simpa only [hn] using not_lt.mp hk

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))

def point (n : ℕ) : Coord 2 :=
  let c := orbit hb table c₀ n
  ![spacing ν (K₀ N b m) (D b) n * address (capacity b m n) c.state c.leftStack c.rightStack,
    sign terminal c.state * spacing ν (K₀ N b m) (D b) n]

def runPath (n : ℕ) : ℝ → Coord 2 :=
  let c := orbit hb table c₀ n
  let d := orbit hb table c₀ (n + 1)
  CenterPaths.signedCenter (startTime ν (K₀ N b m) (D b) n)
    (duration ν (K₀ N b m) (D b) n)
    (spacing ν (K₀ N b m) (D b) n) (spacing ν (K₀ N b m) (D b) (n + 1))
    (sign terminal c.state) (sign terminal d.state)
    (address (capacity b m n) c.state c.leftStack c.rightStack)
    (address (capacity b m (n + 1)) d.state d.leftStack d.rightStack)

@[fun_prop] theorem contDiff_runPath (n : ℕ) : ContDiff ℝ ∞ (runPath hb table terminal ν m c₀ n) :=
  CenterPaths.contDiff_signedCenter _ _ _ _ _ _ _ _

theorem runPath_start (n : ℕ) :
    runPath hb table terminal ν m c₀ n (startTime ν (K₀ N b m) (D b) n) =
      point hb table terminal ν m c₀ n := CenterPaths.signed_start _ _ _ _ _ _ _ _

theorem runPath_end (hν : 0 < ν) (n : ℕ) :
    runPath hb table terminal ν m c₀ n (startTime ν (K₀ N b m) (D b) (n + 1)) =
      point hb table terminal ν m c₀ (n + 1) :=
  CenterPaths.signed_end
    (lt_of_lt_of_le zero_lt_one (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n)) _ _ _ _ _ _ _

theorem runPath_joins (hν : 0 < ν) (n : ℕ) :
    runPath hb table terminal ν m c₀ n (startTime ν (K₀ N b m) (D b) (n + 1)) =
      runPath hb table terminal ν m c₀ (n + 1) (startTime ν (K₀ N b m) (D b) (n + 1)) := by
  rw [runPath_end hb table terminal ν m c₀ hν, runPath_start]

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ) (c₀ : Configuration (Fin N))
variable (hm : 1 ≤ m)
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)

def runBox (n : ℕ) : Box N (capacity b m n) :=
  let c := orbit hb table c₀ n
  ⟨c.state, ⟨c.leftStack, (orbit_fits hb table hm c₀ hc₀ n).1⟩,
    ⟨c.rightStack, (orbit_fits hb table hm c₀ hc₀ n).2⟩⟩

@[simp] theorem runBox_config (n : ℕ) :
    config (runBox hb table m c₀ hm hc₀ n) = orbit hb table c₀ n := by
  cases h : orbit hb table c₀ n
  simp only [config, runBox, h]

def runActive (n : ℕ) (h : (lookup hb table (orbit hb table c₀ n)).isSome) :
    Active hb table (capacity b m n) := ⟨runBox hb table m c₀ hm hc₀ n, h⟩

theorem target_runActive (n : ℕ) (h : (lookup hb table (orbit hb table c₀ n)).isSome) :
    target hb table (runActive hb table m c₀ hm hc₀ n h) = orbit hb table c₀ (n + 1) := by
  rw [target, show (runActive hb table m c₀ hm hc₀ n h).val = runBox hb table m c₀ hm hc₀ n from rfl,
    runBox_config, orbit_succ]
  apply (next_eq_of_lookup hb table _).symm
  exact (Option.some_get h).symm

theorem runPath_eq_installed (hterm : NoOutgoing table terminal) (n : ℕ)
    (h : (lookup hb table (orbit hb table c₀ n)).isSome) :
    runPath hb table terminal ν m c₀ n =
      path hb table terminal ν m n (runActive hb table m c₀ hm hc₀ n h) := by
  have hs : sign terminal (orbit hb table c₀ n).state = -1 :=
    ite_eq_right (lookup_source_nonterminal hb table hterm h)
  dsimp only [runPath]
  rw [hs, CenterPaths.signed_source_negative]
  unfold path
  rw [target_runActive hb table m c₀ hm hc₀ n h]
  congr 1
  simp only [targetAddress, target_runActive hb table m c₀ hm hc₀ n h, capacity_succ]

include hm hc₀

theorem runPath_plateau (hν : 0 < ν) (hdir : IncomingDirection table) (hin : IncomingRule table)
    (hterm : NoOutgoing table terminal) (n : ℕ)
    (h : (lookup hb table (orbit hb table c₀ n)).isSome) {t : ℝ}
    (ht : t ∈ Icc (startTime ν (K₀ N b m) (D b) n) (startTime ν (K₀ N b m) (D b) (n + 1)))
    (X : Coord 2) (hX : ∀ i, |X i - runPath hb table terminal ν m c₀ n t i| ≤
      radius ν (K₀ N b m) (D b) n) :
    field hb table terminal ν m t X = deriv (runPath hb table terminal ν m c₀ n) t := by
  rw [runPath_eq_installed hb table terminal ν m c₀ hm hc₀ hterm n h] at hX ⊢
  exact field_plateau hb table terminal ν m hν hm hdir hin n
    (runActive hb table m c₀ hm hc₀ n h) ht X hX

theorem runPath_negative (hν : 0 < ν) (hterm : NoOutgoing table terminal) (n : ℕ)
    (h : (lookup hb table (orbit hb table c₀ n)).isSome)
    (hn : (orbit hb table c₀ (n + 1)).state ≠ terminal) (t : ℝ) :
    runPath hb table terminal ν m c₀ n t 1 ≤ -spacing ν (K₀ N b m) (D b) n := by
  rw [runPath_eq_installed hb table terminal ν m c₀ hm hc₀ hterm n h]
  apply path_negative hb table terminal ν m hν
  rwa [target_runActive]

end VelocityDetection.ExpandingArray
end

end OAI
