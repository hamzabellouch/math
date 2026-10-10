import OAI.MeasureTheory.Falconer.Angular.AngularStationaryRadialError
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

namespace PlanarFalconer
open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate

theorem measurable_angular_deriv {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, Differentiable ℝ (f x)) :
    Measurable (fun p : α × ℝ => deriv (f p.1) p.2) := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε : Tendsto ε atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => show 0 < 1/((n:ℝ)+1) by positivity)⟩
  apply measurable_of_tendsto_metrizable
    (f := fun n => fun p : α × ℝ => (ε n)⁻¹ • (f p.1 (p.2+ε n)-f p.1 p.2))
  · intro n
    exact (show Measurable (fun _ : α × ℝ => (ε n)⁻¹) from measurable_const).smul
      ((hm.comp (measurable_fst.prodMk (measurable_snd.add_const (ε n)))).sub hm)
  · apply tendsto_pi_nhds.mpr
    intro p
    exact (hd p.1 p.2).hasDerivAt.tendsto_slope_zero_right.comp hε

theorem measurable_angular_iteratedDeriv {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, ContDiff ℝ ∞ (f x)) (n : ℕ) :
    Measurable (fun p : α × ℝ => iteratedDeriv n (f p.1) p.2) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hm
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    exact measurable_angular_deriv (fun x => iteratedDeriv n (f x)) ih (fun x => (AngularDifferentialExpr.smooth_iteratedDeriv (f := f x) (hd x) n).differentiable (by simp))

theorem measurable_stationary_family {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, ContDiff ℝ ∞ (f x)) (n : ℕ) :
    Measurable (fun p : α × ℝ => fullCircleStationaryExpansion p.2 (f p.1) n) := by
  have hjet (g : α → ℝ → ℂ)
      (hg : Measurable (fun p : α × ℝ => g p.1 p.2))
      (hgd : ∀ x, ContDiff ℝ ∞ (g x)) (k : ℕ) :
      Measurable (fun x => iteratedDeriv k (stationaryAmplitude (g x)) 0) := by
    have hma : Measurable (fun p : α × ℝ => stationaryAmplitude (g p.1) p.2) := by
      unfold stationaryAmplitude
      exact ((stationaryWeight_contDiff.continuous.measurable.comp measurable_snd).complex_ofReal).mul
        (hg.comp (measurable_fst.prodMk (extendedStationaryInverse_contDiff.continuous.measurable.comp measurable_snd)))
    exact (measurable_angular_iteratedDeriv _ hma (fun x => stationaryAmplitude_contDiff (hgd x)) k).comp
      (measurable_id.prodMk measurable_const)
  have hopp : Measurable (fun p : α × ℝ => conj (f p.1 (p.2+Real.pi))) :=
    Complex.continuous_conj.measurable.comp (hm.comp (measurable_fst.prodMk (measurable_snd.add_const _)))
  have hdopp (x : α) : ContDiff ℝ ∞ (fun t => conj (f x (t+Real.pi))) :=
    Complex.conjCLE.contDiff.comp ((hd x).comp (contDiff_id.add contDiff_const))
  have h1 (k : ℕ) := (hjet f hm hd k).comp (measurable_fst : Measurable (Prod.fst : α × ℝ → α))
  have h2 (k : ℕ) := (hjet _ hopp hdopp k).comp (measurable_fst : Measurable (Prod.fst : α × ℝ → α))
  unfold fullCircleStationaryExpansion fresnelCoefficient stationaryDerivativeExpansion
  fun_prop

end PlanarFalconer

end OAI
