import Mathlib
import OAI.Analysis.AffineBernstein.ActualGlobalP
import OAI.Analysis.AffineBernstein.ActualGlobalD

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ActualGlobalCoercive
open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_global_coercive_identity {n : ℕ} (hn : n ≠ 0) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)-15/8+
      ((n : ℝ)-7/8)*tubeBasePair H bS P P q+(((n : ℝ)+2)/2)*tubeBasePair H bS P F q+
      (15/16)*(tubeBasePair H bS F F q+tubeAngularPair H bE F F q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*(n : ℝ)))*tubeBasePair H bS (fun q => σ q.1) P q-
        (15/(4*(n : ℝ)))*tubeBasePair H bS (fun q => σ q.1) F q) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let PP := tubeBasePair H bS P P
  let DD := tubeBasePair H bS F F
  let PD := tubeBasePair H bS P F
  let EE := tubeAngularPair H bE F F
  let Rp := tubeBasePair H bS (fun q => σ q.1) P
  let Rd := tubeBasePair H bS (fun q => σ q.1) F
  let Jp := fun q => (Fintype.card ι : ℝ)+((n : ℝ)+1)*PP q+(((n : ℝ)+2)/2)*PD q
  let Jd := fun q => ((n : ℝ)/2)*(DD q+EE q)+((n : ℝ)+2)*(PP q+PD q)-((n : ℝ)-2*Fintype.card ι)
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hPP := hpair P P hP hP
  have hDD := hpair F F hF hF
  have hPD := hpair P F hP hF
  have hEE : ContinuousOn EE (tubeOpenSet D) := continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have hsp (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (fun q : S × E => σ q.1) q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hRp := hpair _ P hsp hP
  have hRd := hpair _ F hsp hF
  have hJp : ContinuousOn Jp (tubeOpenSet D) := (continuousOn_const.add (continuousOn_const.mul hPP)).add
    (continuousOn_const.mul hPD)
  have hJd : ContinuousOn Jd (tubeOpenSet D) := ((continuousOn_const.mul (hDD.add hEE)).add
    (continuousOn_const.mul (hPP.add hPD))).sub continuousOn_const
  have hpI := affineEpigraph_global_p_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero bS bE hσ hc hσD
  have hdI := affineMaximal_global_d_identity (μ := μ) hΩ hcv hu hp hm a L hD hK hzero bS bE hσ hc hσD
  change tubeIntegral μ M (fun s => σ s^2) Jp = 2*tubeIntegral μ M σ Rp at hpI
  change tubeIntegral μ M (fun s => σ s^2) Jd = -2*tubeIntegral μ M σ Rd at hdI
  change tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)-15/8+
      ((n : ℝ)-7/8)*PP q+(((n : ℝ)+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*(n : ℝ)))*Rp q-(15/(4*(n : ℝ)))*Rd q)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfunc : (fun q => (Fintype.card ι : ℝ)-15/8+((n : ℝ)-7/8)*PP q+
      (((n : ℝ)+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      fun q => (1-15/(4*(n : ℝ)))*Jp q+(15/(8*(n : ℝ)))*Jd q := by
    funext q
    dsimp [Jp,Jd]
    field_simp [hn0]
    ring
  rw [hfunc,tubeIntegral_linearCombination (σ := fun s => σ s^2) (by fun_prop)
    (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hJp hJd,hpI,hdI]
  rw [show (fun q => (2-15/(2*(n : ℝ)))*Rp q-(15/(4*(n : ℝ)))*Rd q) =
    (fun q => (2-15/(2*(n : ℝ)))*Rp q+(-15/(4*(n : ℝ)))*Rd q) by funext q; ring,
    tubeIntegral_linearCombination hσ.continuous hc hσD hM hRp hRd]
  field_simp [hn0]
  ring

end ActualGlobalCoercive

theorem tube_paired_determinant {n : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9) :
    7 / 128 ≤ (15 / 16) * (n - 7 / 8) - (n + 2) ^ 2 / 16 := by
  nlinarith [mul_nonneg (show 0 ≤ n - 2 by linarith) (show 0 ≤ 9 - n by linarith)]

/- A two-dimensional positive-semidefinite quadratic form, stated in
terms of the actual squared lengths and cross inner product. -/
theorem paired_cauchy_coercive {P D I a b c : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hI : I ^ 2 ≤ P * D)
    (ha : 0 ≤ a) (hb : 0 < b) (hdet : c ^ 2 ≤ 4 * a * b) :
    0 ≤ a * P + c * I + b * D := by
  by_cases hP0 : P = 0
  · have hI0 : I = 0 := by nlinarith [sq_nonneg I]
    simp only [hI0, mul_zero, add_zero]
    exact add_nonneg (mul_nonneg ha hP) (mul_nonneg hb.le hD)
  have hPp : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
  have h1 := mul_nonneg (show 0 ≤ 4 * a * b - c ^ 2 by linarith) (sq_nonneg P)
  have h2 := mul_nonneg (show 0 ≤ P * D - I ^ 2 by linarith) (show 0 ≤ 4 * b ^ 2 by positivity)
  have h3 := sq_nonneg (c * P + 2 * b * I)
  have htot : 0 ≤ 4 * b * P * (a * P + c * I + b * D) := by nlinarith
  exact nonneg_of_mul_nonneg_right htot (by positivity)

/- A fixed explicit lower coercivity constant for the exact source range.
In particular it is independent of the number of directions k >= 2. -/
theorem tube_pointwise_coercivity {n k P D I E : ℝ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hE : 0 ≤ E) (hI : I ^ 2 ≤ P * D) :
    (1 / 512) * (1 + P + D + E) ≤
      k - 15 / 8 + (n - 7 / 8) * P + ((n + 2) / 2) * I + (15 / 16) * (D + E) := by
  have hdet := tube_paired_determinant hn hn9
  have hc : ((n + 2) / 2) ^ 2 ≤
      4 * (n - 7 / 8 - 1 / 512) * (15 / 16 - 1 / 512) := by nlinarith
  have hq := paired_cauchy_coercive hP hD hI
    (show 0 ≤ n - 7 / 8 - 1 / 512 by linarith)
    (show (0 : ℝ) < 15 / 16 - 1 / 512 by norm_num) hc
  nlinarith

/- Cauchy--Schwarz followed by Young, with no choice of orthonormal frame. -/
theorem cauchy_young {P Q J a ε : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hJ : J ^ 2 ≤ P * Q) (hε : 0 < ε) :
    a * J ≤ ε * P + (a ^ 2 / (4 * ε)) * Q := by
  have hdet : (-a) ^ 2 ≤ 4 * (a ^ 2 / (4 * ε)) * ε := by
    field_simp
    nlinarith
  have h := paired_cauchy_coercive hQ hP (by nlinarith [hJ])
    (show 0 ≤ a ^ 2 / (4 * ε) by positivity) hε hdet
  nlinarith

/- The exact coefficients on the right of the source coercive identity. -/
theorem tube_cutoff_coefficients {n : ℝ} (hn : 3 ≤ n) :
    (2 - 15 / (2 * n)) ^ 2 + (-15 / (4 * n)) ^ 2 ≤ 8 := by
  have hn0 : 0 < n := by linarith
  have ha0 : 0 ≤ 15 / (2 * n) := by positivity
  have ha : 15 / (2 * n) ≤ 5 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb0 : 0 ≤ 15 / (4 * n) := by positivity
  have hb : 15 / (4 * n) ≤ 5 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  simp only [neg_div]
  nlinarith [mul_nonneg (show 0 ≤ 2 - (2 - 15 / (2 * n)) by linarith)
    (show 0 ≤ 2 + (2 - 15 / (2 * n)) by linarith),
    mul_nonneg (show 0 ≤ 5 / 4 - 15 / (4 * n) by linarith)
      (show 0 ≤ 5 / 4 + 15 / (4 * n) by linarith)]

/- Quantitative absorption in the exact coercive identity, with constants
uniform for every n in [3,9] and every tube direction count. -/
theorem tube_cutoff_absorption {n v P D E Q Jp Jd : ℝ}
    (hn : 3 ≤ n) (hP : 0 ≤ P) (hD : 0 ≤ D) (hE : 0 ≤ E) (hQ : 0 ≤ Q)
    (hJp : Jp ^ 2 ≤ P * Q) (hJd : Jd ^ 2 ≤ D * Q) :
    v * ((2 - 15 / (2 * n)) * Jp - (15 / (4 * n)) * Jd) ≤
      (1 / 1024) * v ^ 2 * (1 + P + D + E) + 4096 * Q := by
  have hCp := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hJp)
  have hCd := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hJd)
  have hp := cauchy_young (show 0 ≤ v ^ 2 * P by positivity) hQ
    (show (v * Jp) ^ 2 ≤ v ^ 2 * P * Q by nlinarith [hCp])
    (a := 2 - 15 / (2 * n)) (by norm_num : (0 : ℝ) < 1 / 2048)
  have hd := cauchy_young (show 0 ≤ v ^ 2 * D by positivity) hQ
    (show (v * Jd) ^ 2 ≤ v ^ 2 * D * Q by nlinarith [hCd])
    (a := -15 / (4 * n)) (by norm_num : (0 : ℝ) < 1 / 2048)
  simp only [neg_div] at hd ⊢
  norm_num at hp hd
  have hc := mul_nonneg (sub_nonneg.mpr (tube_cutoff_coefficients hn)) hQ
  simp only [neg_div] at hc
  have hrem : 0 ≤ v ^ 2 * (1 + P + D + 2 * E) := by positivity
  nlinarith

/- Exact cancellation of the two stationarity identities in tubes.tex.
The symbols are their actual integrals; this is just their linear combination. -/
theorem tube_coercive_identity_algebra {n k V P D E I Rp Rd : ℝ}
    (hn : n ≠ 0)
    (hp : k * V + (n + 1) * P + ((n + 2) / 2) * I = 2 * Rp)
    (hd : (n / 2) * (D + E) + (n + 2) * (P + I) - (n - 2 * k) * V = -2 * Rd) :
    (k - 15 / 8) * V + (n - 7 / 8) * P + ((n + 2) / 2) * I +
      (15 / 16) * (D + E) = (2 - 15 / (2 * n)) * Rp - (15 / (4 * n)) * Rd := by
  apply (mul_left_cancel₀ hn)
  field_simp
  linear_combination (1024 * n - 3840) * hp + 1920 * hd

end AffineBernstein

end

end OAI
