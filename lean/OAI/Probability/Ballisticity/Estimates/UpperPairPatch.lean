import Mathlib
import OAI.Probability.Ballisticity.Estimates.ProductTruncationError
import OAI.Probability.Ballisticity.Walk.OutwardKernelElementary

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def upperPairNeighborhood {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (N : ℕ) : Set (Lattice d) :=
  (LatticeBall x.1 N ∪ LatticeBall x.2 N) ∩ {y | a ≤ dot (realPosition y) (realPosition (step e))}

lemma upperPairNeighborhood_finite {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (N : ℕ) : (upperPairNeighborhood e a x N).Finite :=
  ((latticeBall_finite x.1 N).union (latticeBall_finite x.2 N)).subset Set.inter_subset_left

noncomputable def upperPairPatch {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (N : ℕ) (ω : Environment d) : Environment d :=
  fun y => if y ∈ upperPairNeighborhood e a x N then ω y else ω x.1

lemma upperPairPatch_measurable {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) (N : ℕ) :
    @Measurable _ _ (rowSigma (upperPairNeighborhood e a x N)) _ (upperPairPatch e a x N) := by
  have hx₁ : x.1 ∈ upperPairNeighborhood e a x N := by
    refine ⟨Or.inl ?_,?_⟩
    · simp [LatticeBall]
    · exact le_of_eq hx.1.symm
  refine @Measurable.of_eval _ _ _ (rowSigma (upperPairNeighborhood e a x N)) _ _ ?_
  intro y
  by_cases hy : y ∈ upperPairNeighborhood e a x N
  · simpa only [upperPairPatch,ite_eq_left hy] using measurable_row_on hy
  · simpa only [upperPairPatch,ite_eq_right hy] using measurable_row_on hx₁

lemma upperPairPatch_elliptic {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (N : ℕ) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y g, κ ≤ (ω y).1 g) :
    ∀ y g, κ ≤ ((upperPairPatch e a x N ω) y).1 g := by
  intro y g
  by_cases hy : y ∈ upperPairNeighborhood e a x N <;>
    simp only [upperPairPatch,hy,ite_true,ite_false] <;> apply hκ

lemma rawPairEndpointLaw_upper_patch_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ (ω : Environment d), (∀ y g, κ ≤ (ω y).1 g) →
      ∀ S : Set (Lattice d × Lattice d),
      rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
        rawPairEndpointLaw (realPosition (step e)) H (upperPairPatch e a x N ω) x S+ε ∧
      rawPairEndpointLaw (realPosition (step e)) H (upperPairPatch e a x N ω) x S ≤
        rawPairEndpointLaw (realPosition (step e)) H ω x S+ε := by
  obtain ⟨N,hN⟩ := rawPairEndpointLaw_uniform_locality hκ e hH hε
  refine ⟨N,?_⟩
  intro a x hx ω hω S
  let η : Environment d := fun y => if a ≤ dot (realPosition y) (realPosition (step e)) then ω y else ω x.1
  have hη : ∀ y g, κ ≤ (η y).1 g := by
    intro y g
    dsimp [η]
    split_ifs <;> apply hω
  have he : Set.EqOn η (upperPairPatch e a x N ω) (LatticeBall x.1 N ∪ LatticeBall x.2 N) := by
    intro y hy
    by_cases ha : a ≤ dot (realPosition y) (realPosition (step e))
    · simp [η,upperPairPatch,upperPairNeighborhood,hy,ha]
    · simp [η,upperPairPatch,upperPairNeighborhood,ha]
  have hsame : rawPairEndpointLaw (realPosition (step e)) H ω x = rawPairEndpointLaw (realPosition (step e)) H η x := by
    apply rawPairEndpointLaw_upper_congr e H a x hx
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e)) at hy
    simp only [η,ite_eq_left hy]
  rw [hsame]
  exact hN η (upperPairPatch e a x N ω) hη (upperPairPatch_elliptic e a x N ω hω) x he S
end DirectionalTransience

end

end

end OAI
