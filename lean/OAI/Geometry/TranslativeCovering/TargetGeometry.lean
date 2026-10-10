import OAI.Geometry.TranslativeCovering.TargetSampling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace TargetGeometry
open Set MeasureTheory Metric CylinderProbability ConeStretch
open scoped ENNReal
noncomputable def bad {n : ℕ} {I : Type u_1} (p : I → Space n) (L ξ : ℝ) : Set (Space n × Space n) :=
  ⋃ i,⋃ j,pairEvent (p i) (p j) L ξ

lemma measurable_bad {n : ℕ} {I : Type u_2} [Fintype I] (p : I → Space n) (L ξ : ℝ) :
    MeasurableSet (bad p L ξ) := MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun j => pairEvent_measurable (p i) (p j) L ξ

lemma bad_probability {n : ℕ} [NeZero n] {I : Type u_3} [Fintype I]
    (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G) :
    (uniform G |>.prod (uniform G)) (bad p L ξ) ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1)) := by
  calc
    _ ≤ ∑ i,∑ j,(uniform G |>.prod (uniform G)) (pairEvent (p i) (p j) L ξ) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => measure_iUnion_le _) |>.trans_eq (by simp [tsum_fintype])
    _ ≤ ∑ _i : I,∑ _j : I,ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pair_probability hG hD hL hξ hGsub hGlarge (p i) (p j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];
                rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]; congr 1; ring

theorem select {n : ℕ} [NeZero n] {I : Type u_4} [Fintype I]
    (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
    {D L t ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (ht : 0 < t) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    {M : ℕ} (hM : 2 ≤ M) (hI : Nonempty I)
    (hsmall : ((TargetSampling.pairs M).card:ℝ)*
      (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*t/D)^(n-1)) < 1/2) :
    ∃ x : Fin M → Space n, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
      (∀ i j,i ≠ j → (x i,x j) ∉ bad p L t) ∧
      TargetSampling.score (bad p L ξ) x ≤
        10*((TargetSampling.pairs M).card:ℝ)*
          (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_antisymm hGlarge bot_le)
  have : IsProbabilityMeasure (uniform G) := uniform_probability hG0 hGf
  have : NullSingletonClass (uniform G) := ⟨fun x => by simp [uniform]⟩
  have : Nonempty I := hI
  have hf : 0 < 12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1) := by
    have hcard : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  apply TargetSampling.select (uniform G) hM measurableSet_diagonal hG
    (by simp [uniform,Measure.restrict_apply' hG,Set.compl_inter_self])
    (measurable_bad p L t) (measurable_bad p L ξ) hf hsmall
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (bad_probability p hG hD hL ht hGsub hGlarge)
  · exact ENNReal.toReal_le_of_le_ofReal hf.le (bad_probability p hG hD hL hξ hGsub hGlarge)

end TargetGeometry

end OAI
