import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.IntegralForcedHits
import OAI.Combinatorics.RamseyFive.Geometry.ModifiedRadialSchedule
import OAI.Combinatorics.RamseyFive.Probability.FailureCount

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (RadialLine x)] in
lemma abs_modifiedPointScore (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} {b : ℝ} (hb : b∈Set.Icc 0 1)
    (ω : Fin R→S→ℕ) : |modifiedPointScore x S O F b ω|≤F.card := by
  simpa only [Finset.card_univ,Fintype.card_coe,modifiedPointScore] using
    abs_typicalScore_le_card Finset.univ _ hb
      (ownBitsMinus x S O F (fun r i => ω r i))
      (fun r d => ω r ((outsideEquiv x S O).symm d).val)

omit [Finite K] [FiniteDimensional K V] [Fintype (RadialLine x)] in
theorem unsampled_moment_tail (S O : Finset (ℙ K V)) (rate : S→ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} {b t B : ℝ}
    (hb : b∈Set.Icc 0 1) {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,(modifiedPointScore x S O F b ω)^p ∂scheduleMeasure rate R)≤B) :
    (scheduleMeasure rate R).real {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|}≤B/t^p := by
  have h := weighted_moment_tail (scheduleMeasure rate R) (modifiedPointScore x S O F b)
    (fun _ => (1:ℝ)) (abs_modifiedPointScore x S O F hb)
    (fun _ => ⟨by norm_num,le_refl _⟩) hp ht (by simpa only [one_mul] using hB)
  apply (measureReal_mono (μ:=scheduleMeasure rate R) ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  refine ⟨rfl,?_⟩
  rw [modifiedPointScore_eq x S O F b ω hω.1]
  exact hω.2

omit [Finite K] in
theorem unsampled_score_tail (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b t B : ℝ} (hb : b∈Set.Icc 0 1) {p J : ℕ} (hp : Even p) (ht : 0<t)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (scheduleMeasure (fun _ : S => L*δ) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|} ≤ B/t^p+
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2) := by
  have hbound := original_truncated_moment x S O L δ F hF hb p J B hB
  have hg : ∀ω : Fin R→S→ℕ,
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=0 ∨
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=1 := by
    intro ω
    have hi := HighMoment.allTrunc_indicator R J (modifiedRadialSchedule x S O ω)
    by_cases he : modifiedRadialSchedule x S O ω∈overloaded Finset.univ J
    · rw [Set.indicator_of_mem he] at hi
      exact Or.inl (by linarith only [hi])
    · rw [Set.indicator_of_notMem he] at hi
      exact Or.inr (by linarith only [hi])
  have h := truncated_moment_tail (scheduleMeasure (fun _ : S => L*δ) R)
    (modifiedPointScore x S O F b)
    (fun ω => HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω)))
    (abs_modifiedPointScore x S O F hb) hg hp ht hbound
  rw [original_truncation_failure] at h
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*δ) R) ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  change t < |modifiedPointScore x S O F b ω|
  rw [modifiedPointScore_eq x S O F b ω hω.1]
  exact hω.2

end SharpRamseyFive.ScoreGeometry

end OAI
