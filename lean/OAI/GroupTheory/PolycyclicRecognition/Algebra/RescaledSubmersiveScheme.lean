import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedExponentialLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DifferenceAmplitudeWord
import Mathlib.Topology.Sequences

namespace OAI

/-! # A fixed submersive scheme for an actual sequence of rescalings

The subsequence and the word are selected from the actual coordinate laws,
before any good sheets or successful parameter sets are selected.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Filter Set
open scoped Topology

/-- A convergent subsequence and a fixed word with full-rank limiting
endpoint map. This packages only the explicit finite-dimensional data. -/
def HasSubmersiveWordSubsequence {I : Type*} {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ)))
    (p : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ)) : Prop :=
  ∃ q ∈ S, ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (p ∘ u) atTop (𝓝 q) ∧
    ∃ (m : ℕ) (letters : Fin m → I) (t : Fin (m + m) → ℝ),
      differenceAmplitudeWordEndpoint a letters q t = 0 ∧
      Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters q) t)

/-- Compact normalized laws retain their basis-word identities and hence a
submersive fixed word. This form keeps the compactness step independent of
the choice of a matrix realization. -/
theorem exists_submersive_scheme_of_normalized_sequence
    {I : Type*} [Fintype I] {n c : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin n → FreeMagma I) (C : ℝ)
    (p : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ))
    (hp : ∀ k, p k ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C) :
    ∃ q ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C,
      ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (p ∘ u) atTop (𝓝 q) ∧
        ∃ (m : ℕ) (letters : Fin m → I) (t : Fin (m + m) → ℝ),
          differenceAmplitudeWordEndpoint a letters q t = 0 ∧
          Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters q) t) := by
  obtain ⟨q, hq, u, hu, hlim⟩ :=
    (isCompact_normalizedExponentialParameters a w (fun i => Pi.single i 1) C).tendsto_subseq hp
  have hwords (i : Fin n) : evalBilinearWord q.1 q.2 (w i) = Pi.basisFun ℝ (Fin n) i := by
    simpa only [Pi.basisFun_apply] using hq.1.1.2.2.2 i
  obtain ⟨m, letters, t, ht, hsurj⟩ := exists_submersive_differenceAmplitudeWord a q.1
    hq.1.1.2.2.1 hq.1.2 hq.2 q.2 (Pi.basisFun ℝ (Fin n)) w hwords
  exact ⟨q, hq, u, hu, hlim, m, letters, t, ht, hsurj⟩

variable {I L G A : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A genuine family of rescaled exponential-coordinate groups has a
convergent subsequence and one fixed independent-difference word whose
limiting derivative is onto. In particular rank is not an extra hypothesis
on the subsequently retained good sets. -/
theorem exists_rescaled_submersive_scheme
    (X : I → L) {k : ℕ} (hk : LieModule.lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (s : I → ℝ) (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b)
      (fun w => bracketWordExponent s w) β.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) :
    ∃ (C : ℝ), 0 ≤ C ∧
      ∃ p ∈ normalizedExponentialParameters a (fun i => (β.val i : FreeMagma I))
          (fun i => Pi.single i 1) C,
      ∃ u : ℕ → ℕ, StrictMono u ∧
        Tendsto (fun n => rescaledLieData X (boundedBracketWords k) β s (scale (u n)))
          atTop (𝓝 p) ∧
        ∃ (m : ℕ) (letters : Fin m → I) (t : Fin (m + m) → ℝ),
          differenceAmplitudeWordEndpoint a letters p t = 0 ∧
          Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p) t) := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledExponentialData_bound X hk hletters b
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  obtain ⟨p, hp, u, hu, hlim⟩ :=
    (isCompact_normalizedExponentialParameters a (fun i => (β.val i : FreeMagma I))
      (fun i => Pi.single i 1) C).tendsto_subseq
      (fun n => hb s β hβ (scale n) (hscale n))
  have hwords (i : Fin (finrank ℝ L)) :
      evalBilinearWord p.1 p.2 (β.val i) = Pi.basisFun ℝ (Fin (finrank ℝ L)) i := by
    simpa only [Pi.basisFun_apply] using hp.1.1.2.2.2 i
  obtain ⟨m, letters, t, ht, hsurj⟩ := exists_submersive_differenceAmplitudeWord a p.1
    hp.1.1.2.2.1 hp.1.2 hp.2 p.2 (Pi.basisFun ℝ (Fin (finrank ℝ L)))
    (fun i => (β.val i : FreeMagma I)) hwords
  exact ⟨C, hC, p, hp, u, hu, hlim, m, letters, t, ht, hsurj⟩

end PolycyclicRecognition

end

end OAI
