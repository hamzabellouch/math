import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.SubsetEncoding

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open MeasureTheory ProbabilityTheory PoissonScore
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev BaseTape (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) → Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ

noncomputable def baseRowMeasure (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :=
  Measure.pi (fun _ : Fin (sizeScoreCutoff U n P τ) => scheduleMeasure
    (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)

noncomputable def baseTapeMeasure (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Measure (BaseTape U P τ R) :=
  Measure.pi (fun n : Fin (Fintype.card (ℙ K V)+1) => baseRowMeasure U n P τ R L₀)

instance (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    IsProbabilityMeasure (baseRowMeasure U n P τ R L₀) := by
  unfold baseRowMeasure
  infer_instance

instance (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    IsProbabilityMeasure (baseTapeMeasure U P τ R L₀) := by
  unfold baseTapeMeasure
  infer_instance

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma baseTape_marginal (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (n : Fin (Fintype.card (ℙ K V)+1))
    (E : Set (Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)) :
    (baseTapeMeasure U P τ R L₀).real {t | t n∈E}=
      (baseRowMeasure U n P τ R L₀).real E := by
  have hE : MeasurableSet E := Set.Countable.measurableSet (Set.to_countable E)
  have hh := (measurePreserving_eval
    (fun n : Fin (Fintype.card (ℙ K V)+1)=>baseRowMeasure U n P τ R L₀) n).measure_preimage hE.nullMeasurableSet
  exact congrArg ENNReal.toReal hh

noncomputable def baseMessageDecoded (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R)
    (m : (n : Fin (Fintype.card (ℙ K V)+1)) × baseAlphabet U n P τ) : Finset (ℙ K V) :=
  baseDecoded U m.1 P τ L₀ (t m.1) m.2

end SharpRamseyFive.ScoreGeometry

end OAI
