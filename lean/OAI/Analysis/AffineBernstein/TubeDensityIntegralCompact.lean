import Mathlib
import OAI.Analysis.AffineBernstein.CompactDifferentiation
import OAI.Analysis.AffineBernstein.HessianVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [IsLocallyFiniteMeasure μ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The exact tube density can be differentiated under its compact integral;
positivity is required only on the zero-parameter slice and is then uniform
for the compactly supported variation by the tube lemma. -/
lemma hasDerivAt_integral_tubeDensity_variation
    {H G : S × E → ℝ} (q₀ : S × E) (J : F →L[ℝ] (S × E))
    {W K : Set F} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hH : ∀ x ∈ W, ContDiffAt ℝ ∞ H (q₀+J x))
    (hG : ∀ x ∈ W, ContDiffAt ℝ ∞ G (q₀+J x))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : ∀ x ∈ K, (tubeBaseMatrix H (q₀+J x) bS).PosDef)
    (hR : ∀ x ∈ K, (tubeRadiusMatrix H (q₀+J x) bE).PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, tubeAreaDensity
      (tubeBaseMatrix (fun r => H r+t*G r) (q₀+J x) bS)
      (tubeRadiusMatrix (fun r => H r+t*G r) (q₀+J x) bE) δ ∂μ)
      (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ ∂μ) 0 := by
  let DB := fun p : ℝ × F => (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det
  let DR := fun p : ℝ × F => (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det
  let U := {p : ℝ × F | p.2 ∈ W ∧ 0 < DB p ∧ 0 < DR p}
  have hc (p : ℝ × F) (hp : p.2 ∈ W) : ContinuousAt DB p ∧ ContinuousAt DR p := by
    obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J (hH _ hp) (hG _ hp) bS bE
    exact ⟨((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hb).continuousAt,
      ((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp p hr).continuousAt⟩
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hw : ∀ᶠ r : ℝ × F in 𝓝 p, r.2 ∈ W :=
      continuous_snd.continuousAt.preimage_mem_nhds (hW.mem_nhds hp.1)
    have hb := continuousAt_const.eventually_lt (hc p hp.1).1 hp.2.1
    have hr := continuousAt_const.eventually_lt (hc p hp.1).2 hp.2.2
    exact (hw.and (hb.and hr))
  have h0 (x : F) (hx : x ∈ K) : (0,x) ∈ U := by
    refine ⟨hKW hx,?_,?_⟩
    · simpa [DB] using (hB x hx).det_pos
    · simpa [DR] using (hR x hx).det_pos
  let Fd := fun p : ℝ × F => tubeAreaDensity
    (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS)
    (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE) δ
  have hFd (p : ℝ × F) (hp : p ∈ U) : ContDiffAt ℝ ∞ Fd p :=
    contDiffAt_tubeDensity_variation q₀ J (hH _ hp.1) (hG _ hp.1) bS bE
      (ne_of_gt hp.2.1) (ne_of_gt hp.2.2) δ
  have hd := hasDerivAt_setIntegral_compact (μ := μ) hK hU
    (by rintro ⟨t,x⟩ ⟨ht,hx⟩; rcases ht with rfl; exact h0 x hx)
    (F := Fd) (fun p hp => (hFd p hp).contDiffWithinAt)
  have he (x : F) (hx : x ∈ K) : fderiv ℝ Fd (0,x) (1,0) =
      tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ := by
    have h1 := (((hFd (0,x) (h0 x hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (f := fun t : ℝ => (t,x)) 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)))
    exact h1.unique (hasDerivAt_tubeDensity_variation (hH x (hKW hx)) (hG x (hKW hx))
      bS bE (hB x hx) (hR x hx) δ)
  convert hd using 1
  exact setIntegral_congr_fun hK.measurableSet (fun x hx => (he x hx).symm)

end AffineBernstein
end

end OAI
