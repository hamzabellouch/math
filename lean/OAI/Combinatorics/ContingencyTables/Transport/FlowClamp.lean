import OAI.Combinatorics.ContingencyTables.Transport.PublishedEdmondsKarp
import OAI.Combinatorics.ContingencyTables.Machines.SignedPairProgram

namespace OAI

/-! # Binary flow magnitudes and a harmless total-domain clamp

Skew symmetry bounds a feasible entry between its two directed
capacities. The executed list program clamps normalized entries to this
interval. This is the identity on every valid flow and bounds every
stored value even on unrelated raw program inputs.
-/

namespace ContingencyTables.FlowClamp

open MatchingFPRAS.TreeTyped SignedPairProgram PublishedEdmondsKarp

lemma feasible_lower {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (u v : Fin n) : -(c v u:ℤ)≤f u v := by
  have h := hf.2.1 v u
  have hs := hf.1 u v
  omega

lemma residual_bounds {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (u v : Fin n) :
    0≤(c u v:ℤ)-f u v ∧ (c u v:ℤ)-f u v≤c u v+c v u := by
  have hl := feasible_lower c s t f hf u v
  have hu := hf.2.1 u v
  constructor <;> omega

def clamp (z : (ℕ×ℕ)×Signed) : Signed :=
  (min z.1.1 (z.2.1-z.2.2),min z.1.2 (z.2.2-z.2.1))

def clampRealizer : Realizer clamp := by
  let A : Realizer (fun z : (ℕ×ℕ)×Signed=>z.1.1) := composition first first
  let B : Realizer (fun z : (ℕ×ℕ)×Signed=>z.1.2) := composition first second
  let N : Realizer (fun z : (ℕ×ℕ)×Signed=>SignedPairProgram.normalize z.2) :=
    composition second normalizeRealizer
  exact pair (composition (pair A (composition N first)) minimum)
    (composition (pair B (composition N second)) minimum)

theorem polynomial_clamp : PolynomialTime clampRealizer := by
  unfold clampRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition
        (polynomial_composition polynomial_second polynomial_normalize) polynomial_first))
      polynomial_minimum
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition
        (polynomial_composition polynomial_second polynomial_normalize) polynomial_second))
      polynomial_minimum

theorem clamp_bounds (limits : ℕ×ℕ) (z : Signed) :
    (clamp (limits,z)).1≤limits.1 ∧ (clamp (limits,z)).2≤limits.2 :=
  ⟨min_le_left _ _,min_le_left _ _⟩

theorem clamp_eq_normalize (limits : ℕ×ℕ) (z : Signed)
    (hl : -(limits.2:ℤ)≤SignedPairProgram.value z) (hu : SignedPairProgram.value z≤limits.1) :
    clamp (limits,z)=SignedPairProgram.normalize z := by
  apply Prod.ext
  · change min limits.1 (z.1-z.2)=z.1-z.2
    apply min_eq_right
    unfold SignedPairProgram.value at hu
    omega
  · change min limits.2 (z.2-z.1)=z.2-z.1
    apply min_eq_right
    unfold SignedPairProgram.value at hl
    omega

theorem clamp_feasible {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (u v : Fin n) (z : Signed) (hz : SignedPairProgram.value z=f u v) :
    clamp ((c u v,c v u),z)=ForestAffineProgram.signedParts (f u v) := by
  rw [clamp_eq_normalize _ z (by rw [hz];exact feasible_lower c s t f hf u v)
    (by rw [hz];exact hf.2.1 u v),SignedPairProgram.normalize_eq,hz]

end ContingencyTables.FlowClamp

end OAI
