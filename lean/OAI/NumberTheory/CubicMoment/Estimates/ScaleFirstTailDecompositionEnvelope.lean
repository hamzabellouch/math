import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionRows
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedGeometry

namespace OAI

/-! The literal squarefree product cutoff can be removed exactly after
retaining the original smooth envelope and Gauss coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailKernel_zero_off_envelope (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : primary n) (hout : n ∉ centralProductEnvelope X) :
    scaleFirstTailKernel ℓ H U X n = 0 := by
  by_cases hs : Squarefree n
  · have hsize : Real.exp primeProductWeights.radius*X < norm n := lt_of_not_ge
      (fun hnorm => hout (Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hnorm⟩,hs⟩))
    apply scaleFirstTailKernel_envelope_zero
    exact primeProductWeights.upper_support () (norm n/X) ((lt_div_iff₀ hX).mpr hsize)
  · have hg : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hs])
    simp only [scaleFirstTailKernel,hg,mul_zero,zero_mul]

lemma scaleFirstTailKernel_indicator (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : primary n) :
    (if n ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X n else 0) =
      scaleFirstTailKernel ℓ H U X n := by
  split_ifs with hm
  · rfl
  · exact (scaleFirstTailKernel_zero_off_envelope ℓ H U hX hn hm).symm

theorem scaleFirstTailStoppedDyads_envelope (i : ℕ) (ρ ξ H T : ℝ) {X : ℝ} (hX : 0 < X)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k) =
      envelopeCutoffBilinearTail (stoppedNormDyad (distinguishedStoppedSide X) j)
        (stoppedNormDyad (distinguishedStoppedSide X) k)
        (distinguishedStoppedAlpha ρ ξ X q)
        (distinguishedStoppedBeta i ρ ξ X h early d q) primeProductEnvelope H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro s _
  unfold scaleFirstTailStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hpa := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  have hpb := (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1
  rw [scaleFirstTailKernel_indicator 0 H _ hX (primary_mul hpa hpb)]
  simp only [scaleFirstTailKernel,theta_zero,one_mul]
  ring

end CubicFirstMoment

end

end OAI
