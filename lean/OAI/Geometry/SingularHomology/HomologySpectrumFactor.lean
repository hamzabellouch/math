import OAI.Dynamics.EntropyCounterexample.PolynomialSpectralBound
import OAI.Geometry.SingularHomology.HomologyTransfer
import OAI.Dynamics.EntropyCounterexample.FiniteSpectrumBound

namespace OAI

noncomputable section

namespace Problem340

open PolynomialSpectrum

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem homology_pairRadii_factor_subset (n : ℕ)
    (f : X → X) (i : Y → X) (p : X → Y)
    (hf : Continuous f) (hi : Continuous i) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (i ∘ p) (hi.comp hp))) :
    pairRadii (realHomologyMap n f hf) ⊆
      insert 0 (pairRadii (realHomologyMap n (p ∘ i) (hp.comp hi))) := by
  rw [realHomologyMap_eq_of_homotopy n hf (hi.comp hp) H,
    realHomologyMap_comp n p i hp hi, realHomologyMap_comp n i p hi hp]
  exact pairRadii_comp_subset _ _

theorem bddAbove_homology_pairRadii_of_homotopy_factor
    (f : X → X) (i : Y → X) (p : X → Y)
    (hf : Continuous f) (hi : Continuous i) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (i ∘ p) (hi.comp hp)))
    (hB : BddAbove (⋃ n, pairRadii (realHomologyMap n (p ∘ i) (hp.comp hi)))) :
    BddAbove (⋃ n, pairRadii (realHomologyMap n f hf)) := by
  apply (hB.insert 0).mono
  intro r hr
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hr
  rcases homology_pairRadii_factor_subset n f i p hf hi hp H hn with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, h⟩)

theorem bddAbove_homology_pairRadii_of_finite_homotopy_factor
    (f : X → X) (i : Y → X) (p : X → Y)
    (hf : Continuous f) (hi : Continuous i) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf)
      (continuousMapOf (i ∘ p) (hi.comp hp)))
    [∀ n, FiniteDimensional ℝ (RealSingularHomology n Y)]
    (N : ℕ) (hvanish : ∀ n, N < n → Subsingleton (RealSingularHomology n Y)) :
    BddAbove (⋃ n, pairRadii (realHomologyMap n f hf)) := by
  apply bddAbove_homology_pairRadii_of_homotopy_factor f i p hf hi hp H
  have h := bddAbove_total_pairedEigenvalue_moduli
    (fun n => realHomologyMap n (p ∘ i) (hp.comp hi)) N hvanish
  simpa only [pairRadii, Set.iUnion_ofPred] using h

theorem totalRealHomologySpectralRadius_eq_sSup_pairRadii
    (f : X → X) (hf : Continuous f) :
    totalRealHomologySpectralRadius f hf =
      sSup (⋃ n, pairRadii (realHomologyMap n f hf)) := by
  simp only [totalRealHomologySpectralRadius, pairRadii, Set.iUnion_ofPred]

end Problem340

end

end OAI
