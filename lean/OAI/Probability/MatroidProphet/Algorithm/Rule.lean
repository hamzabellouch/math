import OAI.Probability.MatroidProphet.LayerOnline
import OAI.Probability.MatroidProphet.Density.Birth
import Mathlib.Data.Finset.Sort

namespace OAI

namespace MatroidProphet
open Set Finset

structure MainMasks (n : ℕ) where
  H : Finset (Fin n)
  D : Finset (Fin n)
  C : Finset (Fin n)
  T : Finset (Fin n)
  odd : Bool

def mainSeedBits (n : ℕ) : ℕ := 4*n+2

def seedMask {n : ℕ} (r : Seed (mainSeedBits n)) (j : Fin 4) : Finset (Fin n) :=
  univ.filter fun e => r ⟨4*e.val+j.val, by dsimp [mainSeedBits]; omega⟩ = true

def mainMasks {n : ℕ} (r : Seed (mainSeedBits n)) : MainMasks n where
  H := seedMask r 0
  D := seedMask r 1
  C := seedMask r 2
  T := seedMask r 3
  odd := r ⟨4*n+1, by dsimp [mainSeedBits]; omega⟩

def mainBranch {n : ℕ} (r : Seed (mainSeedBits n)) : Bool :=
  r ⟨4*n, by dsimp [mainSeedBits]; omega⟩

namespace MainAlgorithm
variable {n : ℕ}

def higher (f : Fin n) (a : Option ℤ) (e : Fin n) (b : Option ℤ) : Prop :=
  match a, b with
  | some i, some j => j < i ∨ j = i ∧ f < e
  | some _, none => True
  | _, _ => False

def candidate (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (e : Fin n) (w : Option ℤ) : Prop :=
  w ≠ none ∧ e ∉ d.H ∧ e ∉ M.closure {f | f ∈ d.H ∧ higher f (seen f) e w}

noncomputable def listed (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : Finset ℤ := by
  classical
  exact d.D.biUnion fun e => if candidate M d seen e (seen e) then (seen e).toFinset else ∅

noncomputable def groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : List ℤ := (listed M d seen).sort (· ≤ ·)

def groupMask (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (mask : Finset (Fin n)) (h : ℕ) : Set (Fin n) :=
  {e | e ∈ mask ∧ candidate M d seen e (seen e) ∧ seen e = (groups M d seen)[h]?}

noncomputable def finalPath (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) : ℤ → Set (Fin n) :=
  guardedPath M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    (groups M d seen).length

noncomputable def birth (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : ℤ :=
  nominalBirth M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    ((groups M d seen).idxOf i) e

def eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : Prop :=
  e ∉ d.H ∪ d.D ∪ d.C ∧ candidate M d seen e (some i) ∧ i ∈ groups M d seen ∧
  e ∈ d.T ∧ activation ((groups M d seen).idxOf i) + 2 ≤ birth M hE d seen e i ∧
  (birth M hE d seen e i) % 2 = (if d.odd then 1 else 0) ∧
  e ∉ finalPath M hE d seen (birth M hE d seen e i - 2)

noncomputable def assign (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) : Option ℤ → Option ℤ := by
  classical
  exact fun w => match w with
    | none => none
    | some i => if eligible M hE d seen e i then some (birth M hE d seen e i) else none

noncomputable def core (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    OnlineRule n (mainSeedBits n) :=
  layerOnlineRule M (roundedLevel weightBase) (measurable_roundedLevel weightBase)
    (fun r seen b => finalPath M hE (mainMasks r) seen (b-2))
    (fun r seen => assign M hE (mainMasks r) seen)

noncomputable def hidden (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) where
  mask r := (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
  core := core M hE

end MainAlgorithm
end MatroidProphet

end OAI
