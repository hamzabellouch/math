import OAI.Combinatorics.ContingencyTables.Machines.CellMaximumProgram
import OAI.Combinatorics.ContingencyTables.Machines.BoundedComplementProgram

namespace OAI

/-! # Computing an attained minimum through the complementary table

Complementation changes the lower endpoint query to the
upper endpoint query and preserves every cell capacity.
-/

namespace ContingencyTables.CellMinimumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram

def complemented (z : Context) : Context := (BoundedComplementProgram.complement z.1,z.2)

def complementedRealizer : Realizer complemented :=
  pair (composition (f := fun z : Context=>z.1)
    (g := BoundedComplementProgram.complement) first BoundedComplementProgram.complementRealizer) second

lemma polynomial_complemented : PolynomialTime complementedRealizer :=
  polynomial_pair (polynomial_composition polynomial_first
    BoundedComplementProgram.polynomial_complement) polynomial_second

def minimum (z : Context) : ℕ :=
  CellMaximumProgram.bound z-CellMaximumProgram.maximum (complemented z)

def minimumRealizer : Realizer minimum :=
  composition (f := fun z : Context=>
      (CellMaximumProgram.bound z,CellMaximumProgram.maximum (complemented z)))
    (g := fun z : ℕ×ℕ=>z.1-z.2)
    (pair CellMaximumProgram.boundRealizer
      (composition (f := complemented) (g := CellMaximumProgram.maximum)
        complementedRealizer CellMaximumProgram.maximumRealizer)) subtract

lemma polynomial_minimum : PolynomialTime minimumRealizer :=
  polynomial_composition (polynomial_pair CellMaximumProgram.polynomial_bound
    (polynomial_composition polynomial_complemented CellMaximumProgram.polynomial_maximum))
    polynomial_subtract

lemma complemented_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    complemented (NetworkVertexCode.data r c b,(i.val,j.val))=
      (NetworkVertexCode.data (BoundedTableComplement.rows b r)
        (BoundedTableComplement.columns b c) b,(i.val,j.val)) := by
  unfold complemented
  rw [BoundedComplementProgram.complement_code]

/-- The returned lower endpoint is attained and is no larger than the
selected coordinate of any feasible bounded table. -/
theorem minimum_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n)
    (hne : ∃ X,HasMargins X r c ∧ ∀ u v,X u v≤b u v) :
    ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧
      X i j=minimum (NetworkVertexCode.data r c b,(i.val,j.val)) ∧
      ∀ Y,HasMargins Y r c → (∀ u v,Y u v≤b u v) → X i j≤Y i j := by
  obtain ⟨X₀,hx,hxb⟩ := hne
  have hn : ∃ Y,HasMargins Y (BoundedTableComplement.rows b r)
      (BoundedTableComplement.columns b c) ∧ ∀ u v,Y u v≤b u v :=
    ⟨BoundedTableComplement.complement b X₀,
      BoundedTableComplement.complement_margins b X₀ r c hx hxb,
      BoundedTableComplement.complement_bounds b X₀⟩
  obtain ⟨Y,hy,hyb,hvalue,hmax⟩ := CellMaximumProgram.maximum_correct hEK
    (BoundedTableComplement.rows b r) (BoundedTableComplement.columns b c) b i j hn
  refine ⟨BoundedTableComplement.complement b Y,
    BoundedTableComplement.complement_reverse_margins b X₀ Y r c hx hxb hy hyb,
    BoundedTableComplement.complement_bounds b Y,?_,?_⟩
  · unfold minimum
    rw [CellMaximumProgram.bound_code,complemented_code,←hvalue]
    rfl
  · intro Z hz hzb
    have hb := hmax (BoundedTableComplement.complement b Z)
      (BoundedTableComplement.complement_margins b Z r c hz hzb)
      (BoundedTableComplement.complement_bounds b Z)
    change b i j-Y i j≤Z i j
    change b i j-Z i j≤Y i j at hb
    omega

end ContingencyTables.CellMinimumProgram

end OAI
