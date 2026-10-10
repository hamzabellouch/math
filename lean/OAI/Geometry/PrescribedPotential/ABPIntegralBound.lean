import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.LocalPotentialABP

namespace OAI

/-! A B P Integral Bound. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory Matrix
open scoped ContDiff InnerProductSpace
namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance abpIntegralRealIP (d : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))
local notation "e" => EuclideanSpace.equiv (Fin d) ℂ

theorem abp_integral_minimum_bound
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (G : E → Matrix (Fin d) (Fin d) ℂ)
    {c : E} {r δ K B : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hK : 0 < K)
    (hmin : ∀ x ∈ closedBall c r, f (e c) ≤ f (e x))
    (hG : ∀ x ∈ closedBall c r, (G x).IsHermitian)
    (hGδ : ∀ x ∈ closedBall c r, ∀ v : E,
      δ*‖v‖^2 ≤ inner ℝ ((G x).toEuclideanLin v) v)
    (hdet : ∀ x ∈ closedBall c r,
      |(G x + PotentialKaehler.potentialMatrix f (e x)).det.re| ≤ K)
    {U : Set E} (hU : MeasurableSet U) (hsub : closedBall c r ⊆ U)
    (hn : ∀ x ∈ U, f (e x) ≤ 0)
    (hi : IntegrableOn (fun x => -f (e x)) U μ)
    (hB : (∫ x in U, -f (e x) ∂μ) ≤ B) :
    -f (e c) ≤ δ*r^2/2 + B*((4:ℝ)^(2*d)*K^2) /
      μ.real (closedBall (0:E) (δ*r/2)) := by
  let S : Set E := {x | x ∈ closedBall c r ∧ f (e x) ≤ f (e c)+δ*r^2/2}
  let C : ℝ := (4:ℝ)^(2*d)*K^2
  let V : ℝ := μ.real (closedBall (0:E) (δ*r/2))
  have hC : 0 < C := by positivity
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos μ _ (by positivity)).ne'
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hSc : IsClosed S := isClosed_closedBall.inter
    (isClosed_le (hf.continuous.comp (EuclideanSpace.equiv (Fin d) ℂ).continuous) continuous_const)
  have hSsub : S ⊆ U := fun x hx => hsub hx.1
  have hSi : IntegrableOn (fun x => -f (e x)) S μ := hi.mono_set hSsub
  have hSfin : μ S ≠ ⊤ :=
    ((measure_mono (show S ⊆ closedBall c r from fun _ hx => hx.1)).trans_lt
      (isCompact_closedBall _ _).measure_lt_top).ne
  have hABP := local_potential_sublevel_volume μ hf G hr hδ hK.le hmin hG hGδ hdet
  have hABPr : V ≤ C * μ.real S := by
    have hne : ENNReal.ofReal C * μ S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
    have hh := ENNReal.toReal_mono hne hABP
    simpa only [V,C,S,measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le] using hh
  have hBn : 0 ≤ B := (setIntegral_nonneg hU (fun x hx => neg_nonneg.mpr (hn x hx))).trans hB
  have hIS : (-f (e c)-δ*r^2/2)*μ.real S ≤ B := by
    have hc : IntegrableOn (fun _ : E => -f (e c)-δ*r^2/2) S μ :=
      integrableOn_const hSfin
    have hm := setIntegral_mono_on hc hSi hSc.measurableSet (fun x (hx : x ∈ S) => by
      have hh := hx.2
      linarith)
    have hm' := setIntegral_mono_set hi
      (by
        filter_upwards [ae_restrict_mem hU] with x hx
        exact neg_nonneg.mpr (hn x hx))
      (Filter.Eventually.of_forall hSsub)
    have hh := hm.trans (hm'.trans hB)
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hh
  by_cases hm : 0 ≤ -f (e c)-δ*r^2/2
  · have hmul := mul_le_mul_of_nonneg_left hABPr hm
    have hmul' := mul_le_mul_of_nonneg_left hIS hC.le
    have hh : (-f (e c)-δ*r^2/2)*V ≤ B*C := by nlinarith
    have hd := (le_div_iff₀ hV).mpr hh
    change -f (e c) ≤ δ*r^2/2 + B*C/V
    linarith
  · have hdiv : 0 ≤ B*C/V := div_nonneg (mul_nonneg hBn hC.le) hV.le
    change -f (e c) ≤ δ*r^2/2 + B*C/V
    linarith
end PotentialABP

end
end

end OAI
