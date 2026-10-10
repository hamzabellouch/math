import OAI.NumberTheory.JointDickman.Counting.SamplingRateEnvelope

namespace OAI

/-! # Sampling with the polynomial scales of the manuscript -/

namespace JointDickman
open Finset Classical PublishedInputs

theorem scaledSamplingComparison {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A]
    (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i b, 0 ≤ p i b) (hpone : ∀ i, ∑ b, p i b = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j b z, E i j b z = E j i z b)
    (hHsym : ∀ i j b z, H i j b z = H j i z b)
    (hEdiag : ∀ i b, E i i b b = 0) (hHdiag : ∀ i b, H i i b b = 0)
    (hdom : ∀ i j b z, |E i j b z| ≤ H i j b z)
    {B C q c U K e L u a : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hc : 0 < c) (hU : 0 ≤ U) (hK : 0 < K) (hu : 0 ≤ u) (hL : 0 ≤ L) (ha : 0 < a)
    (hNlo : c*B^(0.32 : ℝ) ≤ Fintype.card ι)
    (hNhi : (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ))
    (hNsmall : (2 : ℝ)*Fintype.card ι ≤ B)
    (hgap : 2*C ≤ K*B^(0.07 : ℝ))
    (hbad : samplingDegreeEnvelope U q K B < 1)
    (hbound : e+Real.sqrt (q*B^(-0.21 : ℝ))+L*samplingDegreeEnvelope U q K B ≤ u)
    (hcut : u+a < L)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q*B^(-0.21 : ℝ))
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q*B^(-0.21 : ℝ))
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e) :
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u+a+samplingRateEnvelope C q c U K a B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : 0 < K*B^(0.07 : ℝ) := by positivity
  have hg : C < K*B^(0.07 : ℝ) := by linarith
  have hb := sampling_degree_scale_bound hB0 hC hq hK hN.le hNhi hgap
  change _ ≤ samplingDegreeEnvelope U q K B at hb
  have hq0 : 0 ≤ q*B^(-0.21 : ℝ) := by positivity
  have hm := sampling_sample_size hB
  have hs := finiteSamplingComparison hMC p hp hpone E H hEsym hHsym hEdiag hHdiag hdom
    hC hq0 hd (by positivity : 0 < (Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) hg hu hL ha
    hmean hsquareH hsquareE htest (hb.trans_lt hbad)
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hL)).trans hbound) hcut
    ⌈B^(0.14 : ℝ)⌉₊ hm.1
  have hsamp := samplingError_scale_bound hB hc hU hK.le hNlo hNhi
    ⌈B^(0.14 : ℝ)⌉₊ hm.2.1 hm.2.2
  have hfamily := samplingFamily_scale_bound (a := a) hB hc hK Fintype.card_pos
    hNlo hNsmall hm.2.2
  have hsquare : (Fintype.card ι : ℝ)*(q*B^(-0.21 : ℝ))/
      ((Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) = samplingSquareEnvelope q B :=
    sampling_square_scale_eq hN.ne' hB0
  have htail := add_le_add (add_le_add hb hsquare.le) hfamily
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htail
    (add_nonneg (sq_nonneg C) hq0))
  unfold samplingRateEnvelope samplingEntropyEnvelope
  linarith

end JointDickman

end OAI
