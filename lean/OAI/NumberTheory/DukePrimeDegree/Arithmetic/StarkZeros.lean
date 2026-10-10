import OAI.NumberTheory.PrimePackets.FunctionalEquation
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PacketBridge
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PublishedStark

namespace OAI

/-!
# Uniform residues from completed-zeta zero separation

The completed zeta function, its functional equation and its convergent
real Hadamard sum give the uniform residue estimate from a uniform zero
gap. Uniqueness of a near-one zero reduces this gap to real-zero exclusion.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.AnalyticGrowth
  PrimeDegreePackets.HeckeMellin

universe u

/-- Comparison of the actual multiplicity-weighted zero terms. -/
lemma realZeroPole_le_of_scaled_gap {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : f 0 ≠ 0)
    (hstrip : ∀ z, f z = 0 → z.re ≤ 1)
    {L c h : ℝ} (hL : 0 < L) (hc : 0 < c) (hh : 0 < h) (hh4 : h ≤ 4 / L)
    (hgap : ∀ z, f z = 0 →
      c ^ 2 ≤ (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2) (z : ℂ) :
    realZeroPole f (1 + h) z ≤
      (4 * (1 + 3 / c) ^ 2) * realZeroPole f (1 + 1 / L) z := by
  by_cases hm : zeroMultiplicity f z = 0
  · simp [realZeroPole, hm]
  have hz := (zeroMultiplicity_ne_zero_iff hf hzero z).mp hm
  have hX : 0 ≤ L * (1 - z.re) := mul_nonneg hL.le (sub_nonneg.mpr (hstrip z hz))
  have hU : L * h ≤ 4 := by
    have H := (le_div_iff₀ hL).mp hh4
    nlinarith only [H]
  have H := realPoleKernel_comparison hc hX (mul_pos hL hh) hU (hgap z hz)
  have H' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left H hL.le)
    (show (0 : ℝ) ≤ zeroMultiplicity f z from by exact_mod_cast zeroMultiplicity_nonneg hf z)
  simp only [realZeroPole, real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  unfold realPoleKernel at H'
  nlinarith only [H']

/-- The analytic estimate uses the proved completed-zeta Hadamard sum,
with no zero-sum or summability hypothesis. -/
theorem logRegularized_deriv_bound_of_completedXi_gap
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    {c B L : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL4 : 4 ≤ L)
    (harch : ∀ s ∈ Icc (1 : ℝ) 2, |archimedeanZetaTerm (d + 1) s| ≤ B)
    (hgap : ∀ z, completedThetaXi σ hn z = 0 →
      c ^ 2 ≤ (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2) :
    ∀ h ∈ Ioc (0 : ℝ) (4 / L),
      |deriv (logRegularizedDedekindZeta K) h| ≤
        (4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2) * L := by
  have hLp : 0 < L := by linarith
  have hbase := dedekindXi_hasSum_realZeroPole_totallyReal σ hn
    (show 1 < 1 + 1 / L by have := one_div_pos.mpr hLp; linarith)
  have hbaseEq := hbase.tsum_eq
  rw [hn, ← hL] at hbaseEq
  have he : 1 + 1 / L - 1 = 1 / L := by ring
  rw [he, one_div_one_div] at hbaseEq
  have hlog := div_nonpos_of_nonpos_of_nonneg
    (realDedekindZeta_deriv_nonpos K (show 1 < 1 + 1 / L by have := one_div_pos.mpr hLp; linarith))
    (realDedekindZeta_pos K (show 1 < 1 + 1 / L by have := one_div_pos.mpr hLp; linarith)).le
  have hinv : 1 / L ≤ 1 := (div_le_one hLp).mpr (by linarith)
  have hG := abs_le.mp (harch (1 + 1 / L) ⟨by have := one_div_pos.mpr hLp; linarith, by linarith⟩)
  have hrec : 1 / (1 + 1 / L) ≤ 1 :=
    (div_le_one (by have := one_div_pos.mpr hLp; linarith)).mpr
      (by have := one_div_pos.mpr hLp; linarith)
  have hBL : B ≤ B * L := by nlinarith
  have hbaseBound : (∑' z, realZeroPole (completedThetaXi σ hn) (1 + 1 / L) z) ≤
      (3 + B) * L := by nlinarith only [hbaseEq, hlog, hG.2, hrec, hBL, hL4]
  intro h hh
  have hsum := dedekindXi_hasSum_realZeroPole_totallyReal σ hn
    (show 1 < 1 + h by linarith [hh.1])
  let A := 4 * (1 + 3 / c) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint := realZeroPole_le_of_scaled_gap (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero_totallyReal σ hn)
    (fun z hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn hz).2)
    hLp hc hh.1 hh.2 hgap
  have hsumBound : (∑' z, realZeroPole (completedThetaXi σ hn) (1 + h) z) ≤
      A * (3 + B) * L := by
    have H := hsum.summable.tsum_le_tsum hpoint (hbase.summable.mul_left A)
    rw [tsum_mul_left] at H
    exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left hbaseBound hA])
  have hsumNonneg : 0 ≤ ∑' z, realZeroPole (completedThetaXi σ hn) (1 + h) z :=
    tsum_nonneg (dedekindXi_realZeroPole_nonneg_totallyReal σ hn (by linarith [hh.1]))
  have hsumEq := hsum.tsum_eq
  rw [hn, ← hL, show 1 + h - 1 = h by ring] at hsumEq
  have hh1 : h ≤ 1 := hh.2.trans ((div_le_one hLp).mpr hL4)
  have hGh := abs_le.mp (harch (1 + h) ⟨by linarith [hh.1], by linarith⟩)
  have hrecH : 0 ≤ 1 / (1 + h) ∧ 1 / (1 + h) ≤ 1 := by
    constructor
    · exact one_div_nonneg.mpr (by linarith [hh.1])
    · exact (div_le_one (by linarith [hh.1])).mpr (by linarith [hh.1])
  have hder := logRegularizedDedekindZeta_deriv K hh.1
  change |deriv (logRegularizedDedekindZeta K) h| ≤ (A * (3 + B) + B + 2) * L
  apply abs_le.mpr
  constructor <;> nlinarith only [hsumEq, hsumBound, hsumNonneg, hGh.1, hGh.2,
    hrecH.1, hrecH.2, hBL, hL4, hder]

/-- Uniform separation of completed-zeta zeros on the discriminant scale. -/
def CompletedXiGap (d : ℕ) : Prop :=
  ∃ c L₀ : ℝ, 0 < c ∧ 4 ≤ L₀ ∧
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (hn : Module.finrank ℚ K = d + 1) (σ : OrderedEmbeddings (d + 1) K),
      L₀ ≤ Real.log |(NumberField.discr K : ℝ)| →
      ∀ z, completedThetaXi σ hn z = 0 →
        c ^ 2 ≤ (Real.log |(NumberField.discr K : ℝ)| * (1 - z.re)) ^ 2 +
          (Real.log |(NumberField.discr K : ℝ)| * z.im) ^ 2

/-- The real exceptional-zero assertion in Stark's Lemma 8, after
excluding quadratic subfields. -/
def ExceptionalRealZeroExclusion (d : ℕ) : Prop :=
  ∃ a L₀ : ℝ, 0 < a ∧ 4 ≤ L₀ ∧
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (hn : Module.finrank ℚ K = d + 1) (σ : OrderedEmbeddings (d + 1) K),
      L₀ ≤ Real.log |(NumberField.discr K : ℝ)| →
      ∀ β : ℝ, 1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β → β < 1 →
        completedThetaXi σ hn β ≠ 0

/-- Uniqueness of a near-one zero reduces complex zero separation to
real-zero exclusion. -/
theorem completedXiGap_of_exceptionalRealZeroExclusion (d : ℕ)
    (H : ExceptionalRealZeroExclusion.{u} d) : CompletedXiGap.{u} d := by
  obtain ⟨a, L₀, ha, hL₀, Hex⟩ := H
  obtain ⟨C, _, Hunique⟩ := dedekind_near_one_zero_real_simple_unique_totallyReal d
  let c : ℝ := min a (1 / 4)
  have hc : 0 < c := lt_min ha (by norm_num)
  refine ⟨c, max L₀ C + 1, hc, by have := le_max_left L₀ C; linarith, ?_⟩
  intro K _ _ _ hn σ hL z hz
  let L := Real.log |(NumberField.discr K : ℝ)|
  have hLC : C < L := by have := le_max_right L₀ C; dsimp [L]; linarith
  have hLL₀ : L₀ ≤ L := by have := le_max_left L₀ C; dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hstrip := (dedekindXiZeros_re_mem_Icc_totallyReal σ hn hz).2
  have hX : 0 ≤ L * (1 - z.re) := mul_nonneg hLp.le (sub_nonneg.mpr hstrip)
  by_contra hgap
  have hsmall : (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2 < c ^ 2 := lt_of_not_ge hgap
  have hxc : L * (1 - z.re) < c := by nlinarith [sq_nonneg (L * z.im)]
  have hyc : |L * z.im| < c := by
    nlinarith [sq_nonneg (L * (1 - z.re)), sq_abs (L * z.im), abs_nonneg (L * z.im)]
  have hca : c ≤ a := min_le_left _ _
  have hcq : c ≤ 1 / 4 := min_le_right _ _
  have hbox : InNearOneBox L z := by
    constructor
    · have hx : 1 - z.re ≤ (1 / 4 : ℝ) / L :=
        (le_div_iff₀ hLp).mpr (by nlinarith only [hxc, hcq])
      have he : (1 / 4 : ℝ) / L = 1 / (4 * L) := by ring
      rw [he] at hx
      linarith
    · rw [abs_mul, abs_of_pos hLp] at hyc
      have hy : |z.im| ≤ (1 / 4 : ℝ) / L :=
        (le_div_iff₀ hLp).mpr (by nlinarith only [hyc, hcq])
      convert hy using 1
      ring
  obtain ⟨_, hreal, _⟩ := Hunique σ hn hLC z hz hbox
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hreal]
  have hβlt : z.re < 1 := by
    apply lt_of_le_of_ne hstrip
    intro h
    have hz1 : z = 1 := by rw [he, h]; rfl
    subst z
    exact dedekindXiZeros_ne_one_totallyReal σ hn hz
  have hβlo : 1 - a / L ≤ z.re := by
    have hx : 1 - z.re ≤ a / L :=
      (le_div_iff₀ hLp).mpr (by nlinarith only [hxc, hca])
    linarith
  exact Hex K hn σ hLL₀ z.re hβlo hβlt (by simpa only [← he] using hz)

/-- The completed-zeta zero gap gives the uniform zeta scale bound. -/
theorem uniformZetaScaleBound_of_completedXiGap (d : ℕ)
    (H : CompletedXiGap.{u} d) : UniformZetaScaleBound.{u} (d + 1) := by
  classical
  obtain ⟨c, L₀, hc, hL₀, Hgap⟩ := H
  obtain ⟨B, hB, harch⟩ := archimedeanZetaTerm_bounded (d + 1)
  let C := 4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A, E, hA, _, Hscale⟩ :=
    uniform_zeta_scale_of_large_discr_deriv (d + 1) (D₀ := Real.exp L₀) hC (by
      intro K _ _ _ hn hD
      let : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
      let : Algebra.IsSeparable ℚ K :=
        Algebra.IsAlgebraic.isSeparable_of_perfectField
      let σc : EmbeddingOrder K (d + 1) :=
        (Fintype.equivFinOfCardEq (by rw [AlgHom.card, hn])).symm
      let σ : OrderedEmbeddings (d + 1) K := σc.toRealOrder
      have hL : L₀ ≤ Real.log |(NumberField.discr K : ℝ)| := by
        apply (Real.le_log_iff_exp_le (abs_pos.mpr
          (show (NumberField.discr K : ℝ) ≠ 0 from by exact_mod_cast NumberField.discr_ne_zero K))).mpr
        exact hD
      exact logRegularized_deriv_bound_of_completedXi_gap σ hn hc hB rfl
        (hL₀.trans hL) harch (Hgap K hn σ hL))
  refine ⟨A, hA, ?_⟩
  filter_upwards [Hscale] with Q hQ
  intro K _ _ _ σ hn hD
  exact (hQ K σ hn hD).1

end DukePrimeDegree

end OAI
