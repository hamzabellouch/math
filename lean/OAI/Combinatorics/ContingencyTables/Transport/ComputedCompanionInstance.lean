import OAI.Combinatorics.ContingencyTables.Rooted.ComputedLargeForest
import OAI.Combinatorics.ContingencyTables.Machines.TightenedInputProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalMass

namespace OAI

/-! # A literal companion instance from binary bounded margins

All operational data are read from the executed endpoint, flow, and
maximum-forest programs. The existential endpoint witnesses are used
only in the terminal-mass proof, never to define an executed output.
-/

namespace ContingencyTables.ComputedCompanionInstance

open CompanionFactorialApplication ComputedTableTightening
open scoped BigOperators Classical

variable {m n : ℕ}

def baseline (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  ((TightenedInputProgram.baseline (NetworkVertexCode.data r c b)).getD i.val []).getD j.val 0

lemma baseline_properties (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    HasMargins (baseline r c b) (newRows r c b) (newColumns r c b) ∧
      ∀ i j,baseline r c b i j≤newBounds r c b i j := by
  obtain ⟨Y,hcode,hm,hb⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  have he : baseline r c b=Y := by
    funext i j
    simp only [baseline,hcode,ResidualGraphProgram.natCode,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,j.isLt,
      dite_true,Option.getD_some,Fin.eta]
  simpa only [he] using And.intro hm hb

/-- The package consumed by the proved factorial, terminal, and oracle
lemmas. Its forest and baseline are decoded executed values. -/
noncomputable def instanceData (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    Instance (Fin m) (Fin n) where
  small:=ComputedLargeForest.small (newBounds r c b) W
  b:=newBounds r c b
  T:=ComputedLargeForest.computed (newRows r c b) (newColumns r c b) (newBounds r c b) W
  hTG:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).1
  hT:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).2.1
  hmax:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).2.2
  r:=fun i=>(newRows r c b i:ℤ)
  c:=fun j=>(newColumns r c b j:ℤ)
  X:=fun i j=>(baseline r c b i j:ℤ)
  d:=1+m*n
  W:=W
  hd:=by omega
  hcard:=by simp only [Fintype.card_fin]; omega
  hW:=hW
  hlarge:=by
    intro i j hs
    have hb : W≤newBounds r c b i j := by
      simpa only [ComputedLargeForest.small,decide_eq_false_iff_not,not_lt] using hs
    exact ⟨hb,(show 1≤W by omega).trans hb⟩
  hsmall:=by
    intro i j hs
    simpa only [ComputedLargeForest.small,decide_eq_true_eq] using hs
  hX:=by
    intro i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (baseline_properties hEK r c b hne).2 i j⟩
  hXr:=by
    intro i
    exact_mod_cast (baseline_properties hEK r c b hne).1.1 i
  hXc:=by
    intro j
    exact_mod_cast (baseline_properties hEK r c b hne).1.2 j

/-- Tightening preserves the count consumed by the terminal estimator. -/
theorem original_count (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    CompanionTerminalMass.tableCount (instanceData hEK r c b hne W hW)=
      (Fintype.card (BoundedTable r c b):ℝ) := by
  unfold CompanionTerminalMass.tableCount
  have he := (ComputedTableTightening.count_eq hEK r c b hne).symm
  calc
    _ = (Fintype.card (BoundedTable (newRows r c b) (newColumns r c b)
        (newBounds r c b)):ℝ) := by
      apply congrArg (fun k : ℕ=>(k:ℝ))
      exact Fintype.card_congr (Equiv.refl _)
    _ = _ := congrArg (fun k : ℕ=>(k:ℝ)) he

/-- The endpoint assumption in the terminal proof follows from the
executed searches. The witnesses here are mathematical proof data. -/
noncomputable def endpoints (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    CompanionTerminalMass.Endpoints (instanceData hEK r c b hne W hW) := by
  have hends:=ComputedTableTightening.attained_endpoints hEK r c b hne
  let lo : ∀ i j,Fin m→Fin n→ℕ:=fun i j=>Classical.choose (hends.1 i j)
  let hi : ∀ i j,Fin m→Fin n→ℕ:=fun i j=>Classical.choose (hends.2 i j)
  have hlo (i : Fin m) (j : Fin n) := Classical.choose_spec (hends.1 i j)
  have hhi (i : Fin m) (j : Fin n) := Classical.choose_spec (hends.2 i j)
  refine { lowerTable:=fun t i j=>(lo t.val.1 t.val.2 i j:ℤ)
           upperTable:=fun t i j=>(hi t.val.1 t.val.2 i j:ℤ)
           lowerBounds:=?_,upperBounds:=?_,lowerRows:=?_,lowerColumns:=?_,
           upperRows:=?_,upperColumns:=?_,lowerAttains:=?_,upperAttains:=?_ }
  · intro t i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (hlo t.val.1 t.val.2).2.1 i j⟩
  · intro t i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (hhi t.val.1 t.val.2).2.1 i j⟩
  · intro t i
    change (∑ j,(lo t.val.1 t.val.2 i j:ℤ))=(newRows r c b i:ℤ)
    exact_mod_cast (hlo t.val.1 t.val.2).1.1 i
  · intro t j
    change (∑ i,(lo t.val.1 t.val.2 i j:ℤ))=(newColumns r c b j:ℤ)
    exact_mod_cast (hlo t.val.1 t.val.2).1.2 j
  · intro t i
    change (∑ j,(hi t.val.1 t.val.2 i j:ℤ))=(newRows r c b i:ℤ)
    exact_mod_cast (hhi t.val.1 t.val.2).1.1 i
  · intro t j
    change (∑ i,(hi t.val.1 t.val.2 i j:ℤ))=(newColumns r c b j:ℤ)
    exact_mod_cast (hhi t.val.1 t.val.2).1.2 j
  · intro t
    exact_mod_cast (hlo t.val.1 t.val.2).2.2
  · intro t
    exact_mod_cast (hhi t.val.1 t.val.2).2.2

end ContingencyTables.ComputedCompanionInstance

end OAI
