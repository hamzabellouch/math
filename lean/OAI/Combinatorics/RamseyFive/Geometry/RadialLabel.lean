import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.Outside
import OAI.Combinatorics.RamseyFive.Probability.TypicalScoreAggregate

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def radialLabel (X : Finset {y : ℙ K V // x ≠ y}) (y : X) : RadialLine x :=
  RadialLine.through x y.val.val y.val.property

omit [Fintype (RadialLine x)] in
lemma radialLabel_fiber_card (X : Finset {y : ℙ K V // x ≠ y}) (l : RadialLine x) :
    Fintype.card {y : X // radialLabel x X y=l}=(RadialLine.trainingOnLine X l).card := by
  rw [RadialLine.trainingOnLine_eq_fiber]
  change (Finset.univ : Finset {y : X // radialLabel x X y=l}).card=_
  apply Finset.card_bij (fun y _ => y.val.val)
  · intro y _
    exact Finset.mem_filter.mpr ⟨y.val.property,y.property⟩
  · intro y _ z _ he
    exact Subtype.ext (Subtype.ext he)
  · intro y hy
    obtain ⟨hyX,hyl⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨⟨y,hyX⟩,hyl⟩,Finset.mem_univ _,rfl⟩

omit [Fintype (RadialLine x)] in
lemma aggregateRate_radialLabel (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0) :
    aggregateRate (radialLabel x X) (fun _ => L*δ) =
      fun l => L*radialWeight x X δ l := by
  funext l
  simp only [aggregateRate,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    radialLabel_fiber_card,radialWeight]
  ring

omit [FiniteDimensional K V] in
lemma radialLabel_in_pencil (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) (y : X) :
    radialLabel x X y ∈ pencilLines x F H ↔ Incident y.val.val H.val := by
  simp only [radialLabel,pencilLines,RadialLine.inFlat,Finset.mem_filter,Finset.mem_univ,
    true_and,RadialLine.through_le_iff]
  change Incident x H.val ∧ Incident y.val.val H.val ↔ _
  simp only [hF H.val H.property,true_and]

theorem original_radial_moment (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) {R : ℕ}
    (b : ℝ) (own : F→Fin R→Bool) (p : ℕ) :
    (∫ ω,(typicalScore Finset.univ
      (fun H : F => Finset.univ.filter fun y : X => Incident y.val.val H.val) b own ω)^p
      ∂scheduleMeasure (fun _ : X => L*δ) R) =
    ∫ ω,(typicalScore Finset.univ (pencilLines x F) b own ω)^p
      ∂scheduleMeasure (fun l => L*radialWeight x X δ l) R := by
  have h := integral_original_score_pow (radialLabel x X) (fun _ => L*δ)
    Finset.univ (pencilLines x F) b own p
  simp_rw [radialLabel_in_pencil x X F hF,aggregateRate_radialLabel] at h
  exact h

end SharpRamseyFive.ScoreGeometry

end OAI
