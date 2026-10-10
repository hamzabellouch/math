import OAI.NumberTheory.JointDickman.Counting.ScaledSamplingComparison

namespace OAI

/-! # Uniform asymptotic sampling comparison -/

namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

/-- The manuscript's sampling transfer, uniformly over the finite site
spaces and all kernels satisfying its moment and fixed-test estimates.
No conditional second-moment bound at each row type is required. -/
theorem samplingComparison_eventually {C q c U e ε : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hc : 0 < c) (hU : 0 ≤ U)
    (he : 0 ≤ e) (hε : 0 < ε) :
    ∀ᶠ B : ℝ in atTop,
    ∀ (ι A : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A],
    FiniteMcDiarmidInput ι A →
    ∀ (p : ι → A → ℝ), (∀ i b, 0 ≤ p i b) → (∀ i, ∑ b, p i b = 1) →
    ∀ (E H : ι → ι → A → A → ℝ),
    (∀ i j b z, E i j b z = E j i z b) →
    (∀ i j b z, H i j b z = H j i z b) →
    (∀ i b, E i i b b = 0) → (∀ i b, H i i b b = 0) →
    (∀ i j b z, |E i j b z| ≤ H i j b z) →
    c*B^(0.32 : ℝ) ≤ Fintype.card ι →
    (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ) →
    (∀ i b, |siteRowMean p H i b| ≤ C) →
    (∀ i, siteRowSquareMass p H i ≤ q*B^(-0.21 : ℝ)) →
    (∀ i, siteRowSquareMass p E i ≤ q*B^(-0.21 : ℝ)) →
    (∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e) →
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤ e+ε := by
  let a := ε/4
  let L := e+ε+1
  have ha : 0 < a := by dsimp [a]; positivity
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hp := sampling_parameters_eventually C q U L (K := 1) (by norm_num) ha
  have hr := (samplingRateEnvelope_tendsto C q U hc (K := 1) (by norm_num) ha).eventually
    (eventually_lt_nhds (half_pos hε))
  filter_upwards [hp,hr,sampling_sites_le_scale U] with B hparams herr hsmall
  intro ι A _ _ _ _ _ hMC p hp hpone E H hEsym hHsym hEd hHd hdom hNlo hNhi hm hsH hsE ht
  have hb := scaledSamplingComparison hMC p hp hpone E H hEsym hHsym hEd hHd hdom
    hparams.1 hC hq hc hU (K := 1) (by norm_num)
    (u := e+a) (by linarith) hL ha hNlo hNhi (hsmall _ hNhi)
    hparams.2.1 hparams.2.2.1
    (by linarith [hparams.2.2.2])
    (by dsimp only [L,a]; linarith) hm hsH hsE ht
  dsimp only [a] at hb herr
  linarith

end JointDickman

end OAI
