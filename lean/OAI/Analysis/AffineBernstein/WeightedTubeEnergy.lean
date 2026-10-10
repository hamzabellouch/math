import Mathlib
import OAI.Analysis.AffineBernstein.ActualGlobalCoercive

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

/- Absorption with the literal compact-product density, requiring positivity only
on the actual unit-normal tube. The identity is an input here and will be supplied
by the actual affine-maximal equation. -/
omit [NormedSpace ℝ S] [FiniteDimensional ℝ S] [Nontrivial E] in
theorem tube_compact_energy_of_identity {n k : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k)
    {D : Set S} {σ : S → ℝ} (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    {M PP DD EE PD Q Rp Rd : S × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hPP : ContinuousOn PP (tubeOpenSet D))
    (hDD : ContinuousOn DD (tubeOpenSet D)) (hEE : ContinuousOn EE (tubeOpenSet D))
    (hPD : ContinuousOn PD (tubeOpenSet D)) (hQ : ContinuousOn Q (tubeOpenSet D))
    (hRp : ContinuousOn Rp (tubeOpenSet D)) (hRd : ContinuousOn Rd (tubeOpenSet D))
    (hQzero : ∀ s ∉ tsupport σ, ∀ e : E, Q (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ PP (s,e) ∧ 0 ≤ DD (s,e) ∧
      0 ≤ EE (s,e) ∧ 0 ≤ Q (s,e) ∧ PD (s,e)^2 ≤ PP (s,e)*DD (s,e) ∧
      Rp (s,e)^2 ≤ PP (s,e)*Q (s,e) ∧ Rd (s,e)^2 ≤ DD (s,e)*Q (s,e))
    (hid : tubeIntegral μ M (fun s => σ s^2) (fun q => k-15/8+(n-7/8)*PP q+
        ((n+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*n))*Rp q-(15/(4*n))*Rd q)) :
    tubeIntegral μ M (fun s => σ s^2) (fun q => 1+PP q+DD q+EE q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q := by
  let en := fun q => 1+PP q+DD q+EE q
  let fl := fun q => k-15/8+(n-7/8)*PP q+((n+2)/2)*PD q+(15/16)*(DD q+EE q)
  let rr := fun q => (2-15/(2*n))*Rp q-(15/(4*n))*Rd q
  have hen : ContinuousOn en (tubeOpenSet D) := ((continuousOn_const.add hPP).add hDD).add hEE
  have hfl : ContinuousOn fl (tubeOpenSet D) := ((continuousOn_const.add
    (continuousOn_const.mul hPP)).add (continuousOn_const.mul hPD)).add
      (continuousOn_const.mul (hDD.add hEE))
  have hrr : ContinuousOn rr (tubeOpenSet D) := (continuousOn_const.mul hRp).sub (continuousOn_const.mul hRd)
  have hien := integrable_tube_compact_sq (μ := μ) hσ hc hsD hM hen
  have hifl := integrable_tube_compact_sq (μ := μ) hσ hc hsD hM hfl
  have hirr : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*rr (tubeLift q))
      (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hsD hM hrr using 1
    ext q; ring
  have hiQ : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*Q (tubeLift q))
      (μ.prod volume.toSphere) := by
    exact integrable_tube_supported hc hsD (hM.mul hQ) (fun s hs e => by simp [hQzero s hs e])
  have hlo := integral_mono_ae (hien.const_mul (1/512)) hifl (Filter.Eventually.of_forall fun q => by
    dsimp only
    by_cases hs : q.1 ∈ tsupport σ
    · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
      have hh' := tube_pointwise_coercivity hn hn9 hk hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1
      have hh'' := mul_le_mul_of_nonneg_left hh' (mul_nonneg hh.1 (sq_nonneg (σ q.1)))
      simpa only [en,fl,tubeLift] using (show (1/512)*(M (q.1,q.2)*σ q.1^2*(1+PP (q.1,q.2)+DD (q.1,q.2)+EE (q.1,q.2))) ≤
        M (q.1,q.2)*σ q.1^2*(k-15/8+(n-7/8)*PP (q.1,q.2)+((n+2)/2)*PD (q.1,q.2)+
        (15/16)*(DD (q.1,q.2)+EE (q.1,q.2))) by nlinarith [hh''])
    · simp [image_eq_zero_of_notMem_tsupport hs])
  have hup := integral_mono_ae hirr ((hien.const_mul (1/1024)).add (hiQ.const_mul 4096))
    (Filter.Eventually.of_forall fun q => by
      dsimp only [Pi.add_apply]
      by_cases hs : q.1 ∈ tsupport σ
      · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
        have hh' := tube_cutoff_absorption hn hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2 (v := σ q.1)
        have hh'' := mul_le_mul_of_nonneg_left hh' hh.1
        dsimp only [rr,en,tubeLift]
        nlinarith [hh'']
      · simp [image_eq_zero_of_notMem_tsupport hs,tubeLift,hQzero q.1 hs q.2])
  rw [integral_const_mul] at hlo
  change (1/512)*tubeIntegral μ M (fun s => σ s^2) en ≤ tubeIntegral μ M (fun s => σ s^2) fl at hlo
  change tubeIntegral μ M (fun s => σ s^2) fl = tubeIntegral μ M σ rr at hid
  rw [hid] at hlo
  simp only [Pi.add_apply] at hup
  rw [integral_add (hien.const_mul (1/1024)) (hiQ.const_mul 4096),integral_const_mul,integral_const_mul] at hup
  change tubeIntegral μ M σ rr ≤ (1/1024)*tubeIntegral μ M (fun s => σ s^2) en+
    4096*(∫ q : S × sphere (0:E) 1, M (tubeLift q)*Q (tubeLift q) ∂μ.prod volume.toSphere) at hup
  have hqI : (∫ q : S × sphere (0:E) 1, M (tubeLift q)*Q (tubeLift q) ∂μ.prod volume.toSphere) =
      tubeIntegral μ M (fun _ => 1) Q := by simp [tubeIntegral]
  rw [hqI] at hup
  change tubeIntegral μ M (fun s => σ s^2) en ≤ _
  linarith

end AffineBernstein
end

end OAI
