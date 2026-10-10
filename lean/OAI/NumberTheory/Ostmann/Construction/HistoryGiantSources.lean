import OAI.NumberTheory.Ostmann.Characters.TreeAncestorScheme

namespace OAI

/-! # The two current giants refer only to previously reconstructed pivots -/

namespace Ostmann

open scoped Classical

inductive HistoryGiantSource where
  | fixed : ℤ → HistoryGiantSource
  | ancestor : ℕ → HistoryGiantSource

def HistoryGiantSource.knownBefore : HistoryGiantSource → ℕ → Prop
  | .fixed _, _ => True
  | .ancestor i, d => i < d

def HistoryGiantSource.eval (p : ℕ → ℤ) : HistoryGiantSource → ℤ
  | .fixed c => c
  | .ancestor i => p i

def evolveGiantSources : ℕ → HistoryGiantSource × HistoryGiantSource → List Bool →
    HistoryGiantSource × HistoryGiantSource
  | _, g, [] => g
  | d, g, b :: path => evolveGiantSources (d + 1) (.ancestor d, if b then g.2 else g.1) path

theorem evolveGiantSources_known (d : ℕ) (g : HistoryGiantSource × HistoryGiantSource)
    (hg : g.1.knownBefore d ∧ g.2.knownBefore d) (path : List Bool) :
    (evolveGiantSources d g path).1.knownBefore (d + path.length) ∧
      (evolveGiantSources d g path).2.knownBefore (d + path.length) := by
  induction path generalizing d g with
  | nil => exact hg
  | cons b path ih =>
    have hs : (.ancestor d : HistoryGiantSource).knownBefore (d + 1) ∧
        (if b then g.2 else g.1).knownBefore (d + 1) := by
      constructor
      · exact Nat.lt_succ_self d
      · cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · cases h : g.1 with
          | fixed c => trivial
          | ancestor i =>
            have hi : i < d := by simpa only [h, HistoryGiantSource.knownBefore] using hg.1
            exact hi.trans (Nat.lt_succ_self d)
        · cases h : g.2 with
          | fixed c => trivial
          | ancestor i =>
            have hi : i < d := by simpa only [h, HistoryGiantSource.knownBefore] using hg.2
            exact hi.trans (Nat.lt_succ_self d)
    simpa only [evolveGiantSources, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
      ih (d + 1) (.ancestor d, if b then g.2 else g.1) hs

/-- This is the actual forward update: the reconstructed pivot becomes
one giant, and the giant on the selected branch is retained. -/
def evolveGiantValues (p : ℕ → ℤ) : ℕ → ℤ × ℤ → List Bool → ℤ × ℤ
  | _, g, [] => g
  | d, g, b :: path => evolveGiantValues p (d + 1) (p d, if b then g.2 else g.1) path

theorem evolveGiantSources_eval (p : ℕ → ℤ) (d : ℕ)
    (g : HistoryGiantSource × HistoryGiantSource) (path : List Bool) :
    ((evolveGiantSources d g path).1.eval p, (evolveGiantSources d g path).2.eval p) =
      evolveGiantValues p d (g.1.eval p, g.2.eval p) path := by
  induction path generalizing d g with
  | nil => rfl
  | cons b path ih =>
    rw [evolveGiantSources, ih, evolveGiantValues]
    cases b <;> rfl

def historyGiantSources (XL XR : ℤ) (path : List Bool) : HistoryGiantSource × HistoryGiantSource :=
  evolveGiantSources 0 (.fixed XL, .fixed XR) path

theorem historyGiantSources_known (XL XR : ℤ) (path : List Bool) :
    (historyGiantSources XL XR path).1.knownBefore path.length ∧
      (historyGiantSources XL XR path).2.knownBefore path.length := by
  simpa only [historyGiantSources, Nat.zero_add] using
    evolveGiantSources_known 0 (.fixed XL, .fixed XR) ⟨trivial, trivial⟩ path

def HistoryGiantSource.fixedFactor : HistoryGiantSource → ℤ
  | .fixed c => c
  | .ancestor _ => 1

def HistoryGiantSource.ancestorLevels (path : List Bool) (s : HistoryGiantSource)
    (hs : s.knownBefore path.length) : Finset (Fin path.length) :=
  match s with
  | .fixed _ => ∅
  | .ancestor i => {⟨i, hs⟩}

def HistoryGiantSource.nodeValue (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → ℤ) (s : HistoryGiantSource)
    (hs : s.knownBefore (preorderNodePath n j).length) : ℤ :=
  match s with
  | .fixed c => c
  | .ancestor i => p (ancestorNodeIndex n j ⟨i, hs⟩)

theorem HistoryGiantSource.coefficient (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → ℤ) (C : ℤ) (s : HistoryGiantSource)
    (hs : s.knownBefore (preorderNodePath n j).length) :
    ancestorCoefficient (C * s.fixedFactor)
      ((s.ancestorLevels (preorderNodePath n j) hs).image (ancestorNodeIndex n j)) p =
      C * s.nodeValue n j p hs := by
  cases s with
  | fixed c => simp [ancestorCoefficient, fixedFactor, ancestorLevels, nodeValue]
  | ancestor i => simp [ancestorCoefficient, fixedFactor, ancestorLevels, nodeValue]

noncomputable def forwardTreeAncestorScheme (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) : PivotDependencyScheme (2 ^ n - 1) :=
  treeAncestorScheme S n t
    (fun path => CR path * (historyGiantSources XL XR path).2.fixedFactor)
    (fun path => CL path * (historyGiantSources XL XR path).1.fixedFactor)
    (fun path => (historyGiantSources XL XR path).2.ancestorLevels path
      (historyGiantSources_known XL XR path).2)
    (fun path => (historyGiantSources XL XR path).1.ancestorLevels path
      (historyGiantSources_known XL XR path).1)

theorem forwardTreeAncestorScheme_left (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (p : Fin (2 ^ n - 1) → ℤ)
    (j : Fin (2 ^ n - 1)) :
    (forwardTreeAncestorScheme S n t XL XR CL CR).leftCoefficient p j =
      CR (preorderNodePath n j) *
        (historyGiantSources XL XR (preorderNodePath n j)).2.nodeValue n j p
          (historyGiantSources_known XL XR _).2 :=
  HistoryGiantSource.coefficient n j p _ _ _

theorem forwardTreeAncestorScheme_right (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (p : Fin (2 ^ n - 1) → ℤ)
    (j : Fin (2 ^ n - 1)) :
    (forwardTreeAncestorScheme S n t XL XR CL CR).rightCoefficient p j =
      CL (preorderNodePath n j) *
        (historyGiantSources XL XR (preorderNodePath n j)).1.nodeValue n j p
          (historyGiantSources_known XL XR _).1 :=
  HistoryGiantSource.coefficient n j p _ _ _

end Ostmann

end OAI
