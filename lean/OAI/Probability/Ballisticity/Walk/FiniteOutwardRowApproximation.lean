import Mathlib
import OAI.Probability.Ballisticity.Entropy.FiniteLogStability

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma upperPairNeighborhood_mono {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) {N R : ℕ} (hNR : N ≤ R) :
    upperPairNeighborhood e a x N ⊆ upperPairNeighborhood e a x R := by
  intro y hy
  refine ⟨?_,hy.2⟩
  have hball (z : Lattice d) : LatticeBall z N ⊆ LatticeBall z R := by
    intro w hw i
    exact (hw i).trans (by exact_mod_cast hNR)
  exact hy.1.elim (fun h => Or.inl (hball _ h)) (fun h => Or.inr (hball _ h))

lemma finite_outward_upper_row_approximation {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e f : Direction d) (A : ℝ) (N : ℕ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ R : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
      @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
      (∀ ω, 0 ≤ F ω ∧ F ω ≤ B) ∧
      (∀ ω, (∀ y g, κ ≤ (ω y).1 g) →
        |min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B-F ω| ≤ ε) := by
  have hloc (n : ℕ) := outwardLog_fixed_height_locality hκ e f (Nat.succ_pos n) hε
  choose r hr using hloc
  obtain ⟨R,hR⟩ := ((Finset.range (N+1)).image r).exists_le
  refine ⟨R,?_⟩
  intro a x hx
  let q : ℕ → Environment d → ℝ := fun n ω => outwardKernelMass e f (n+1) x (upperPairPatch e a x (r n) ω)
  let F : Environment d → ℝ := fun ω => min (finiteLogExcess A q N ω) B
  refine ⟨F,?_,?_,?_⟩
  · have hm : @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ (finiteLogExcess A q N) := by
      unfold finiteLogExcess
      apply Measurable.ennreal_toReal
      apply Measurable.iSup
      intro n
      have hnr : r n ≤ R := hR (r n) (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr n.isLt,rfl⟩)
      have hp := (upperPairPatch_measurable e a x hx (r n)).mono
        (rowSigma_mono (upperPairNeighborhood_mono e a x hnr)) le_rfl
      have hq := (measurable_outwardKernelMass e f (n+1) x).comp hp
      exact (hq.log.neg.sub_const _).ennreal_ofReal
    exact hm.min measurable_const
  · intro ω
    exact ⟨le_min ENNReal.toReal_nonneg hB,min_le_right _ _⟩
  · intro ω hω
    have hd := finiteLogExcess_stability A (fun n => outwardKernelMass e f (n+1) x) q N ω hε.le
      (fun n hn => (hr n a x hx ω hω).le)
    have h₁ := (abs_le.mp hd).1
    have h₂ := (abs_le.mp hd).2
    apply abs_le.mpr
    constructor
    · have hh : min (finiteLogExcess A q N ω) B ≤ min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B+ε := by
        have ht := min_le_min (show finiteLogExcess A q N ω ≤ finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω+ε by linarith) (show B ≤ B+ε by linarith)
        simpa only [min_add_add_right] using ht
      exact by dsimp [F]; linarith
    · have hh : min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B ≤ min (finiteLogExcess A q N ω) B+ε := by
        have ht := min_le_min (show finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω ≤ finiteLogExcess A q N ω+ε by linarith) (show B ≤ B+ε by linarith)
        simpa only [min_add_add_right] using ht
      exact by dsimp [F]; linarith
end DirectionalTransience

end

end

end OAI
