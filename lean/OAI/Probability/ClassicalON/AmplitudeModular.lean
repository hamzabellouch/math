import OAI.Probability.ClassicalON.AmplitudePartition

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)
  (hT : ∀ e,Continuous (T e)) (hCov : EdgeCovarianceNonneg μ T)
  (h0 : ∀ e,0≤∫ x,T e x ∂μ) (hb : ∀ e,0≤b e)

include hT hCov h0 hb

theorem log_amplitudePartition_increment_mono {a c d : V → ℝ}
    (ha : ∀ v,0≤a v) (hac : ∀ v,a v≤c v) (hd : ∀ v,0≤d v) :
    Real.log (amplitudePartition μ T left right b (fun v => a v+d v))-
        Real.log (amplitudePartition μ T left right b a) ≤
      Real.log (amplitudePartition μ T left right b (fun v => c v+d v))-
        Real.log (amplitudePartition μ T left right b c) := by
  let F := fun t => Real.log (amplitudePartition μ T left right b (fun v => c v+t*d v))-
    Real.log (amplitudePartition μ T left right b (fun v => a v+t*d v))
  have hD (t : ℝ) := (log_amplitudePartition_direction_derivative μ T left right b hT c d t).sub
    (log_amplitudePartition_direction_derivative μ T left right b hT a d t)
  have hM : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hD t).continuousAt.continuousWithinAt)
      (fun t _ => (hD t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0≤t := (interior_subset ht).1
    apply sub_nonneg.mpr
    apply Finset.sum_le_sum
    intro e _
    have hJa : ∀ g,0≤amplitudeCoupling left right b (fun v => a v+t*d v) g := by
      intro g
      unfold amplitudeCoupling
      exact mul_nonneg (mul_nonneg (hb g) (add_nonneg (ha _) (mul_nonneg ht0 (hd _))))
        (add_nonneg (ha _) (mul_nonneg ht0 (hd _)))
    have hJ : ∀ g,amplitudeCoupling left right b (fun v => a v+t*d v) g≤
        amplitudeCoupling left right b (fun v => c v+t*d v) g := by
      apply amplitudeCoupling_mono left right b hb
      · intro v; exact add_nonneg (ha v) (mul_nonneg ht0 (hd v))
      · intro v; exact add_le_add (hac v) le_rfl
    have hm := edgeMean_mono_couplings μ T hT hCov hJa hJ e
    apply mul_le_mul (amplitudeSlope_mono left right b hb hd hac t e) hm
    · exact edgeMean_nonneg μ T hT hCov h0 _ hJa e
    · exact amplitudeSlope_nonneg left right b hb (fun v => (ha v).trans (hac v)) hd ht0 e
  have hi := hM (by simp : (0 : ℝ)∈Icc 0 1) (by simp : (1 : ℝ)∈Icc 0 1) (by norm_num)
  simp only [F,zero_mul,add_zero,one_mul] at hi
  linarith

theorem amplitudePartition_supermodular {u v : V → ℝ}
    (hu : ∀ i,0≤u i) (hv : ∀ i,0≤v i) :
    amplitudePartition μ T left right b u*amplitudePartition μ T left right b v ≤
      amplitudePartition μ T left right b (u⊓v)*amplitudePartition μ T left right b (u⊔v) := by
  let a := u⊓v
  let d := fun i => u i-a i
  have ha : ∀ i,0≤a i := by intro i; exact le_min (hu i) (hv i)
  have hd : ∀ i,0≤d i := by intro i; exact sub_nonneg.mpr (min_le_left _ _)
  have had : (fun i => a i+d i)=u := by funext i; dsimp [d]; ring
  have hvd : (fun i => v i+d i)=u⊔v := by
    funext i
    dsimp [d,a]
    rcases le_total (u i) (v i) with h | h
    · rw [min_eq_left h,max_eq_right h]; ring
    · rw [min_eq_right h,max_eq_left h]; ring
  have hi := log_amplitudePartition_increment_mono μ T left right b hT hCov h0 hb
    ha (fun i => min_le_right (u i) (v i)) hd
  rw [had,hvd] at hi
  have hp := amplitudePartition_pos μ T left right b hT
  apply (Real.log_le_log_iff (mul_pos (hp u) (hp v)) (mul_pos (hp _) (hp _))).mp
  rw [Real.log_mul (hp u).ne' (hp v).ne',Real.log_mul (hp _).ne' (hp _).ne']
  linarith

end
end ClassicalON

end

end OAI
