import Mathlib
import OAI.Analysis.AffineBernstein.LinearLogTrace

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

omit [NormedSpace ℝ S] [FiniteDimensional ℝ S] [Nontrivial E] in
theorem tube_compact_log_energy_of_identity {n : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {D : Set S} {σ : S → ℝ} (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    {M PP DD EE AA PA DA Q RA : S × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hPP : ContinuousOn PP (tubeOpenSet D))
    (hDD : ContinuousOn DD (tubeOpenSet D)) (hEE : ContinuousOn EE (tubeOpenSet D))
    (hAA : ContinuousOn AA (tubeOpenSet D)) (hPA : ContinuousOn PA (tubeOpenSet D))
    (hDA : ContinuousOn DA (tubeOpenSet D)) (hQ : ContinuousOn Q (tubeOpenSet D))
    (hRA : ContinuousOn RA (tubeOpenSet D))
    (hQzero : ∀ s ∉ tsupport σ, ∀ e : E, Q (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ PP (s,e) ∧ 0 ≤ DD (s,e) ∧
      0 ≤ EE (s,e) ∧ 0 ≤ AA (s,e) ∧ 0 ≤ Q (s,e) ∧ PA (s,e)^2 ≤ AA (s,e)*PP (s,e) ∧
      DA (s,e)^2 ≤ AA (s,e)*DD (s,e) ∧ RA (s,e)^2 ≤ AA (s,e)*Q (s,e))
    (hid : tubeIntegral μ M (fun s => σ s^2) (fun q => AA q+n*PA q+((n+2)/2)*DA q) =
      2*tubeIntegral μ M σ RA)
    (henergy : tubeIntegral μ M (fun s => σ s^2) (fun q => 1+PP q+DD q+EE q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q) :
    tubeIntegral μ M (fun s => σ s^2) AA ≤ 1358954512*tubeIntegral μ M (fun _ => 1) Q := by
  let en := fun q => 1+PP q+DD q+EE q
  let hl := fun q => AA q+n*PA q+((n+2)/2)*DA q
  let iA := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*AA (tubeLift q)
  let iH := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*hl (tubeLift q)
  let iR := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*RA (tubeLift q)
  let iE := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*en (tubeLift q)
  let iQ := fun q : S × sphere (0:E) 1 => M (tubeLift q)*Q (tubeLift q)
  have hen : ContinuousOn en (tubeOpenSet D) := ((continuousOn_const.add hPP).add hDD).add hEE
  have hhl : ContinuousOn hl (tubeOpenSet D) := (hAA.add (continuousOn_const.mul hPA)).add
    (continuousOn_const.mul hDA)
  have hiA : Integrable iA (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hAA
  have hiH : Integrable iH (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hhl
  have hiR : Integrable iR (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hsD hM hRA using 1
    ext q; dsimp [iR]; ring
  have hiE : Integrable iE (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hen
  have hiQ : Integrable iQ (μ.prod volume.toSphere) :=
    integrable_tube_supported hc hsD (hM.mul hQ) (fun s hs e => by simp [hQzero s hs e])
  have hup := integral_mono_ae hiA ((((hiH.const_mul 4).sub (hiR.const_mul 8)).add
    (hiE.const_mul 324)).add (hiQ.const_mul 16)) (Filter.Eventually.of_forall fun q => by
      dsimp only [Pi.add_apply,Pi.sub_apply]
      by_cases hs : q.1 ∈ tsupport σ
      · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
        have ha := tube_log_cutoff_absorption hn hn9 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.2 (v := σ q.1)
        have ham := mul_le_mul_of_nonneg_left ha hh.1
        dsimp only [iA,iH,iR,iE,iQ,hl,en,tubeLift]
        nlinarith [ham]
      · simp [iA,iH,iR,iE,iQ,tubeLift,image_eq_zero_of_notMem_tsupport hs,hQzero q.1 hs q.2])
  have hlin : (∫ q, (((fun q => 4*iH q)-(fun q => 8*iR q))+(fun q => 324*iE q)+
      (fun q => 16*iQ q)) q ∂μ.prod volume.toSphere) =
      4*(∫ q, iH q ∂μ.prod volume.toSphere)-8*(∫ q, iR q ∂μ.prod volume.toSphere)+
      324*(∫ q, iE q ∂μ.prod volume.toSphere)+16*(∫ q, iQ q ∂μ.prod volume.toSphere) := by
    have h₁ := integral_add (((hiH.const_mul 4).sub (hiR.const_mul 8)).add (hiE.const_mul 324)) (hiQ.const_mul 16)
    have h₂ := integral_add ((hiH.const_mul 4).sub (hiR.const_mul 8)) (hiE.const_mul 324)
    have h₃ := integral_sub (hiH.const_mul 4) (hiR.const_mul 8)
    simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂ h₃ ⊢
    rw [h₁,h₂,h₃,integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul]
  rw [hlin] at hup
  change tubeIntegral μ M (fun s => σ s^2) AA ≤
    4*tubeIntegral μ M (fun s => σ s^2) hl-8*tubeIntegral μ M σ RA+
    324*tubeIntegral μ M (fun s => σ s^2) en+16*(∫ q, iQ q ∂μ.prod volume.toSphere) at hup
  have hqI : (∫ q, iQ q ∂μ.prod volume.toSphere) = tubeIntegral μ M (fun _ => 1) Q := by
    simp [iQ,tubeIntegral]
  rw [hqI,hid] at hup
  change tubeIntegral μ M (fun s => σ s^2) en ≤ _ at henergy
  linarith

end AffineBernstein
end

end OAI
