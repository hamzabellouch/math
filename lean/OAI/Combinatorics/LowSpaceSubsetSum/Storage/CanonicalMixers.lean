import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationProgram
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSurvival

namespace OAI

/-! # Fixed input-index mixers

The three disjoint mixer domains are chosen uniformly for every input length;
their definition does not inspect the weights or a designated solution.
-/

namespace LowSpaceSubsetSum

def canonicalMixers (n : ℕ) (j : Fin 3) : Finset (Fin n) :=
  indexInterval n (j.val * mixerSize n) (mixerSize n)

theorem canonicalMixers_card (n : ℕ) (j : Fin 3) :
    (canonicalMixers n j).card = mixerSize n := by
  apply indexInterval_card
  have hj := j.isLt
  have hm : 3 * mixerSize n ≤ n := by unfold mixerSize; omega
  nlinarith

theorem canonicalMixers_disjoint (n : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (canonicalMixers n i) (canonicalMixers n j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxi := (Finset.mem_filter.mp hx).2
  have hxj := (Finset.mem_filter.mp hy).2
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_right (mixerSize n) (show i.val + 1 ≤ j.val by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega
  · have hm := Nat.mul_le_mul_right (mixerSize n) (show j.val + 1 ≤ i.val by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega

def canonicalRepresentationData {n : ℕ} (I : Instance n) : RepresentationData n where
  input := I
  mixers := canonicalMixers n
  disjoint := canonicalMixers_disjoint n
  card := canonicalMixers_card n

/-- The solution is supplied only to the analysis of the fixed runtime data. -/
def canonicalRepresentationSetup {n : ℕ} (I : Instance n) (S : Finset (Fin n))
    (hS : weight (fun i => (I.values i : ℤ)) S = I.target) : RepresentationSetup n where
  input := I
  solution := S
  solution_weight := hS
  mixers := canonicalMixers n
  disjoint := canonicalMixers_disjoint n
  card := canonicalMixers_card n

theorem canonicalRepresentationSetup_runtimeData {n : ℕ} (I : Instance n)
    (S : Finset (Fin n)) (hS : weight (fun i => (I.values i : ℤ)) S = I.target) :
    (canonicalRepresentationSetup I S hS).runtimeData = canonicalRepresentationData I := rfl

end LowSpaceSubsetSum

end OAI
