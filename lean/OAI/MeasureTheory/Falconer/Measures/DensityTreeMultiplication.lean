import OAI.MeasureTheory.Falconer.Measures.FiniteMassMultiplication

namespace OAI

/-! # Multiplying local tube tests using the original pre-pruning fiber densities -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]

theorem density_tree_multiplication (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (T : ℕ → ι → Set X) (F : ℕ → ℝ≥0∞) (J : ℕ) {θ : ℝ≥0∞}
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j)
    (hdensity : ∀ j < J, ∀ i ∈ I (j+1), θ*μ (Q (j+1) i) ≤ μ (Q (j+1) i ∩ S))
    (hlocal : ∀ j < J, ∀ i ∈ I (j+1),
      Q (j+1) i ∩ S ⊆ Q j (parent j i) ∩ T j (parent j i))
    (htest : ∀ j < J, ∀ p ∈ I j, μ (Q j p ∩ T j p) ≤ F j*μ (Q j p)) :
    (∑ i ∈ I J, μ (Q J i)) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ I 0, μ (Q 0 i)) := by
  apply finite_mass_multiplication I parent (fun j i => μ (Q j i)) (fun j => θ⁻¹*F j) J hparent
  intro j hj p hp
  let C := (I (j+1)).filter (fun i => parent j i = p)
  have hC : ∀ i ∈ C, i ∈ I (j+1) := fun i hi => (Finset.mem_filter.mp hi).1
  have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
    intro i hi l hl hil
    exact hdisj (j+1) (by omega) (hC i hi) (hC l hl) hil
  exact density_hit_children_charge μ S (Q j p) (T j p) hS (Q (j+1)) C
    (fun i hi => hQ (j+1) (by omega) i (hC i hi)) hCdisj hθ hθtop
    (fun i hi => hdensity j hj i (hC i hi))
    (by
      intro i hi
      have hs := hlocal j hj i (hC i hi)
      rwa [(Finset.mem_filter.mp hi).2] at hs)
    (htest j hj p hp)

end Falconer

end OAI
