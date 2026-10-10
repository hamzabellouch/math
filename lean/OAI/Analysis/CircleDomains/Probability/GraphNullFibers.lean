import OAI.Analysis.CircleDomains.Sobolev.LipschitzLengthFiberMajorant
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! A null two-dimensional graph has almost-everywhere null scalar fibers.
This is the precise geometric bridge needed for the Sobolev exceptional set. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graph_null_fibers (f : ℂ → ℝ) (A : Set ℂ)
    (hG : (μH[2] : Measure (ℂ × ℝ)) ((fun z => (z,f z)) '' A) = 0) :
    ∀ᵐ t, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {t}) = 0 := by
  let G := (fun z => (z,f z)) '' A
  have hL : LipschitzWith 1 (Prod.snd : ℂ × ℝ → ℝ) := LipschitzWith.prod_snd
  obtain ⟨H,hH,hbound,hint⟩ := exists_exact_lipschitz_length_fiber_majorant G
    (by rw [hG]; exact ENNReal.zero_lt_top)
    1 Prod.snd hL
  have hzero : (∫⁻ t, H t) = 0 := by
    have hi : (∫⁻ t, H t) ≤ 0 := by simpa only [G, hG, mul_zero] using hint
    exact le_antisymm hi (by positivity)
  filter_upwards [(lintegral_eq_zero_iff hH).mp hzero] with t ht
  have hset : Prod.fst '' (G ∩ Prod.snd ⁻¹' {t}) = A ∩ f ⁻¹' {t} := by
    ext z
    constructor
    · rintro ⟨⟨x,s⟩, ⟨⟨w,hw,hwe⟩,hs⟩,rfl⟩
      cases hwe
      exact ⟨hw,hs⟩
    · rintro ⟨hz,htz⟩
      exact ⟨(z,f z), ⟨⟨z,hz,rfl⟩,htz⟩,rfl⟩
  have hp : LipschitzWith 1 (Prod.fst : ℂ × ℝ → ℂ) := LipschitzWith.prod_fst
  apply le_antisymm _ bot_le
  rw [← hset]
  calc
    _ ≤ (1 : ℝ≥0∞)^(1:ℝ) * (μH[1] : Measure (ℂ × ℝ)) (G ∩ Prod.snd ⁻¹' {t}) :=
      hp.hausdorffMeasure_image_le (by norm_num) _
    _ ≤ H t := by simpa only [ENNReal.one_rpow, one_mul] using hbound t
    _ = 0 := ht

end CircleDomainRigidity

end

end OAI
