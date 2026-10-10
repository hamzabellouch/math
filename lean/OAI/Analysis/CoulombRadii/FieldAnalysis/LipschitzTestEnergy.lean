import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFCountTest
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior
import OAI.Analysis.CoulombRadii.Packets.LipschitzMollifier

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

lemma smooth_test_energy_identity {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    (∫ x, testCharge χ x*χ x)=
      (4*Real.pi)⁻¹*∑ a : Fin 3, ∫ x, (dirPartial χ (axis a) x)^2 := by
  have hp (v : Space) : ContDiff ℝ ∞ (dirPartial χ v) :=
    NeutralAtom.contDiff_partial (by simpa using hχ) v
  have hpc (v : Space) := NeutralAtom.hasCompactSupport_partial hc v
  have hpp (v : Space) : ContDiff ℝ ∞ (dirPartial (dirPartial χ v) v) :=
    NeutralAtom.contDiff_partial (by simpa using hp v) v
  have hcross (v : Space) : Integrable (fun x : Space => (dirPartial χ v x)^2) (volume : Measure Space) := by
    have hh : HasCompactSupport (fun x => dirPartial χ v x*dirPartial χ v x) := (hpc v).mul_right
    have hc : Continuous (fun x : Space => (dirPartial χ v x)^2) := (hp v).continuous.pow 2
    exact hc.integrable_of_hasCompactSupport (μ := (volume : Measure Space)) (by simpa only [pow_two] using hh)
  have hsecond (v : Space) : Integrable (fun x => χ x*dirPartial (dirPartial χ v) v x) :=
    (hχ.continuous.mul (hpp v).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hprod (v : Space) : Integrable (fun x => χ x*dirPartial χ v x) :=
    (hχ.continuous.mul (hp v).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hibp (v : Space) : (∫ x, χ x*dirPartial (dirPartial χ v) v x)=
      -(∫ x, (dirPartial χ v x)^2) := by
    simpa only [dirPartial,pow_two] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by simpa only [pow_two,dirPartial] using hcross v) (hsecond v) (hprod v)
        (fun x _ => hχ.differentiable (by simp) x)
        (fun x _ => (hp v).differentiable (by simp) x))
  have he : (fun x => testCharge χ x*χ x)=
      (fun x => -(4*Real.pi)⁻¹*∑ a : Fin 3, χ x*dirPartial (dirPartial χ (axis a)) (axis a) x) := by
    funext x
    rw [testCharge,NeutralAtom.coordinateLaplacian_eq_partials
      ((hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt),←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum _ (fun a _ => hsecond (axis a))]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib]
  ring

lemma smooth_test_energy_le {χ : Space → ℝ} {A R : ℝ} (hA : 0≤A)
    (hχ : ContDiff ℝ ∞ χ) (y : Space)
    (hs : tsupport χ⊆Metric.closedBall y R)
    (hL : ∀ z v, |χ z-χ v|≤A*‖z-v‖) :
    (∫ x, testCharge χ x*χ x)≤
      (4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y R)).toReal*A^2) := by
  have hc : HasCompactSupport χ := (isCompact_closedBall y R).of_isClosed_subset (isClosed_tsupport χ) hs
  rw [smooth_test_energy_identity hχ hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsingle (a : Fin 3) : (∫ x, (dirPartial χ (axis a) x)^2)≤
      (volume (Metric.closedBall y R)).toReal*A^2 := by
    have hd (x : Space) : |dirPartial χ (axis a) x|≤A := by
      have hd := norm_fderiv_le_of_lip' ℝ (f := χ) (x₀ := x) hA (Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using hL z x))
      have ha : ‖axis a‖=1 := by simp [axis]
      have hh := (fderiv ℝ χ x).le_opNorm (axis a)
      rw [ha,mul_one] at hh
      exact (show |dirPartial χ (axis a) x|≤‖fderiv ℝ χ x‖ from hh).trans hd
    have hout (x : Space) (hx : x∉Metric.closedBall y R) : (dirPartial χ (axis a) x)^2=0 := by
      rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (NeutralAtom.tsupport_dirPartial_subset χ _ hh)))]
      norm_num
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (isCompact_closedBall y R).measure_lt_top (fun z _ => show ‖(dirPartial χ (axis a) z)^2‖≤A^2 by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).2 (hd z))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Measure.real,mul_comm] using hh)
  have HH := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hsingle a)
  simpa [mul_assoc] using HH

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb

theorem raw_coulomb_lipschitz_test {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {σ K : Space → ℝ} {A B R : ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hσs : ∀ x∉Ω, σ x=0)
    (hA : 0≤A) (hR : 0<R) (y : Space)
    (hB : ∀ x, |K x|≤B) (hK : ∀ x, R<‖x-y‖ → K x=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖)
    (hball : Metric.closedBall y (2*R)⊆Ω) :
    (∫ x, σ x*K x)^2≤coulombBilinear σ σ*
      ((4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y (2*R))).toReal*A^2)) := by
  let ε : ℕ → ℝ := fun n => R*(1/((n:ℝ)+1))
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have hεR (n : ℕ) : ε n≤R := by
    dsimp [ε]
    apply mul_le_of_le_one_right hR.le
    exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεt : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  choose χ hsm hsp hLip happ using
    (fun n => NeutralAtom.exists_smooth_lipschitz_approx K hA (hε n) y hK hL)
  have hiΩ : Integrable σ (volume.restrict Ω) := hσ.integrable (by norm_num [TFExponent])
  have hind : Ω.indicator σ=σ := by
    funext x
    by_cases hx : x∈Ω
    · exact indicator_of_mem hx σ
    · rw [indicator_of_notMem hx,hσs x hx]
  have hi : Integrable σ := by
    have hh := (integrable_indicator_iff hΩ).2 hiΩ
    rwa [hind] at hh
  have hpoint (x : Space) : Tendsto (fun n => χ n x) atTop (𝓝 (K x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hh : Tendsto (fun n => A*ε n) atTop (𝓝 0) := by simpa using hεt.const_mul A
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using happ n x) hh
  have hdom (n : ℕ) (x : Space) : |χ n x|≤B+A*R := by
    calc
      _≤|χ n x-K x|+|K x| := by simpa only [sub_add_cancel] using abs_add_le (χ n x-K x) (K x)
      _≤A*ε n+B := add_le_add (happ n x) (hB x)
      _≤_ := by have hh := mul_le_mul_of_nonneg_left (hεR n) hA; linarith
  have hconv : Tendsto (fun n => ∫ x, σ x*χ n x) atTop (𝓝 (∫ x, σ x*K x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖σ x‖*(B+A*R))
    · intro n
      exact hi.aestronglyMeasurable.mul (hsm n).continuous.aestronglyMeasurable
    · exact hi.norm.mul_const _
    · intro n
      filter_upwards [] with x
      rw [norm_mul,Real.norm_eq_abs (χ n x)]
      exact mul_le_mul_of_nonneg_left (hdom n x) (norm_nonneg _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (hpoint x)
  have hQ := raw_coulomb_nonneg hΩ hσ hσs
  apply le_of_tendsto (hconv.pow 2)
  filter_upwards [] with n
  have hsp' : tsupport (χ n)⊆Metric.closedBall y (2*R) :=
    (hsp n).trans (Metric.closedBall_subset_closedBall (by linarith [hεR n]))
  have hc : HasCompactSupport (χ n) := (isCompact_closedBall y (2*R)).of_isClosed_subset
    (isClosed_tsupport _) hsp'
  exact (raw_coulomb_smooth_test hΩ (hsm n) hc (hsp'.trans hball) hσ hσs).trans
    (mul_le_mul_of_nonneg_left (smooth_test_energy_le hA (hsm n) y hsp' (hLip n)) hQ)

end Coulomb

end

end OAI
