import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OwnQuery
import OAI.Combinatorics.RamseyFive.Entropy.OriginalUniformWeightedScoreMoment

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def modifiedRadialSchedule (S O : Finset (ℙ K V)) {R : ℕ}
    (ω : Fin R→S→ℕ) : Fin R→RadialLine x→ℕ :=
  fun r => aggregate (radialLabel x (outsideAt x S O))
    (fun d => ω r ((outsideEquiv x S O).symm d).val)

omit [Finite K] in
lemma original_weighted_radial_moment (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    (b : ℝ) (own : F→Fin R→Bool) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate (radialLabel x X) (ω r))*
      (typicalScore Finset.univ
        (fun H : F => Finset.univ.filter fun y : X => Incident y.val.val H.val) b own ω)^p
      ∂scheduleMeasure (fun _ : X => L*δ) R) =
    ∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
      ∂scheduleMeasure (fun l => L*radialWeight x X δ l) R := by
  have h := integral_original_weighted_score_pow (radialLabel x X) (fun _ => L*δ)
    Finset.univ (pencilLines x F) b own p g
  simp_rw [radialLabel_in_pencil x X F hF,aggregateRate_radialLabel] at h
  exact h

omit [Finite K] in
theorem actual_original_weighted (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ)
    (hg : ∀ω,|g ω|≤1) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
        ∂scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R)≤B) :
    (∫ ω,g (modifiedRadialSchedule x S O ω)*(modifiedPointScore x S O F b ω)^p
      ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply original_uniform_weighted_score_moment (ownQuery x S O) (outsideEquiv x S O)
    (L*δ) Finset.univ _ hb (ownBitsMinus x S O F)
    (fun v => g (fun r => aggregate (radialLabel x (outsideAt x S O)) (v r)))
    (fun v => hg _) p B
  intro u
  rw [original_weighted_radial_moment x (outsideAt x S O) L δ F hF]
  exact hB _

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem measurePreserving_modifiedRadial (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R : ℕ) :
    MeasurePreserving (modifiedRadialSchedule x S O (R:=R))
      (scheduleMeasure (fun _ : S => L*δ) R)
      (scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R) := by
  have hsplit := measurePreserving_split_schedule (fun _ : S => L*δ) (ownQuery x S O) R
  have hproj := (measurePreserving_snd (μ:=scheduleMeasure
    (fun _ : {y : S // ownQuery x S O y} => L*δ) R)
    (ν:=scheduleMeasure (fun _ : {y : S // ¬ownQuery x S O y} => L*δ) R)).comp hsplit
  have hr := (measurePreserving_schedule_reindex (outsideEquiv x S O)
    (fun _ : outsideAt x S O => L*δ) R).comp hproj
  have ha := (measurePreserving_schedule_aggregate (radialLabel x (outsideAt x S O))
    (fun _ : outsideAt x S O => L*δ) R).comp hr
  rw [aggregateRate_radialLabel] at ha
  exact ha

omit [Finite K] in
theorem original_truncation_failure (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R J : ℕ) :
    (∫ω,1-HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))
      ∂scheduleMeasure (fun _ : S => L*δ) R) =
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ p.2) := by
  exact ((measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).comp
      (measurePreserving_modifiedRadial x S O L δ R)).hasLaw.integral_comp
        (measurable_of_countable (fun ω => 1-HighMoment.allTrunc R J ω)).aestronglyMeasurable

omit [Finite K] in
theorem original_truncated_moment (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p J : ℕ) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (∫ω,HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))*
      (modifiedPointScore x S O F b ω)^p ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply actual_original_weighted x S O L δ F hF hb p
    (fun ω => HighMoment.allTrunc R J (Function.uncurry ω))
    (fun ω => by rw [abs_of_nonneg (HighMoment.allTrunc_range R J _).1]
                 exact (HighMoment.allTrunc_range R J _).2) B
  intro own
  have he := (measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).hasLaw.integral_comp
      (measurable_of_countable (fun ω : Fin R×RadialLine x→ℕ => HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p)).aestronglyMeasurable
  exact he.trans_le (hB own)

end SharpRamseyFive.ScoreGeometry

end OAI
