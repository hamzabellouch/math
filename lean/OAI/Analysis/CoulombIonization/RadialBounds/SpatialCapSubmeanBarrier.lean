import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCellGeometryBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis

def capBandStatistic (u C : ℝ) (f : Space → ℝ) : ℝ :=
  (1/((u/8)^3*(Real.pi*4/3)))*
    ∫ x in closedAnnularShell u (2*u), max ((u/100000)^4*f x-C) 0

lemma cap_interior_ball_subset {u : ℝ} (hu : 0 < u) {y : Space}
    (hyl : 5*u/4 ≤ ‖y‖) (hyh : ‖y‖ ≤ 7*u/4) :
    closedBall y (u/8) ⊆ closedAnnularShell u (2*u) := by
  intro x hx
  have hxy : ‖x-y‖ ≤ u/8 := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hl := norm_le_norm_sub_add y x
  rw [norm_sub_rev y x] at hl
  have hh := norm_le_norm_sub_add x y
  constructor <;> linarith

lemma scalar_cap_excess_mono {a b C f : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C) :
    max (a^4*f-C) 0 ≤ max (b^4*f-C) 0 := by
  by_cases hf : 0 ≤ f
  · apply max_le_max_right
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 4) hf) C
  · have haf : a^4*f-C ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha 4) (le_of_not_ge hf)]
    rw [max_eq_right haf]
    exact le_max_right _ _

lemma submean_le_capBandStatistic {u C : ℝ} (hu : 0 < u) {f : Space → ℝ}
    (hf : ContinuousOn f (closedAnnularShell u (2*u))) {y : Space}
    (hyl : 5*u/4 ≤ ‖y‖) (hyh : ‖y‖ ≤ 7*u/4)
    (hmean : f y ≤ (1/((u/8)^3*(Real.pi*4/3)))*(∫ x in closedBall y (u/8), f x)) :
    (u/100000)^4*f y ≤ C+capBandStatistic u C f := by
  let A := closedAnnularShell u (2*u)
  let B := closedBall y (u/8)
  let a := (u/100000)^4
  let V := (u/8)^3*(Real.pi*4/3)
  let e := fun x => max (a*f x-C) 0
  have hBA : B ⊆ A := cap_interior_ball_subset hu hyl hyh
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr (isCompact_closedBall y (u/8)).measure_ne_top
  have hfi : IntegrableOn f B := (hf.mono hBA).integrableOn_compact (isCompact_closedBall _ _)
  have hec : ContinuousOn e A := ((hf.const_mul a).sub continuousOn_const).sup continuousOn_const
  have hei : IntegrableOn e A := hec.integrableOn_compact (closedAnnularShell_compact _ _)
  have heB : IntegrableOn e B := hei.mono_set hBA
  have hv : volume.real B = V := space_closedBall_real y (by positivity : 0 ≤ u/8)
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : a*(∫ x in B, f x)-V*C ≤ ∫ x in B, e x := by
    have hh : (∫ x in B, a*f x-C) ≤ ∫ x in B, e x :=
      integral_mono_ae ((hfi.const_mul a).sub (integrable_const C)) heB
        (ae_of_all _ fun x => le_max_left (a*f x-C) 0)
    rw [integral_sub (hfi.const_mul a) (integrable_const C),integral_const_mul,
      integral_const] at hh
    simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hh
    change a*(∫ x in B, f x)-volume.real B*C ≤ ∫ x in B, e x at hh
    rw [hv] at hh
    exact hh
  have hEA : (∫ x in B, e x) ≤ ∫ x in A, e x :=
    setIntegral_mono_set hei (ae_of_all _ fun x => le_max_right _ _) (ae_of_all _ fun _ hx => hBA hx)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  calc
    a*f y ≤ a*((1/V)*(∫ x in B, f x)) := mul_le_mul_of_nonneg_left hmean ha
    _ = C+(1/V)*(a*(∫ x in B, f x)-V*C) := by field_simp; ring
    _ ≤ C+(1/V)*(∫ x in A, e x) := by
      have ht := mul_le_mul_of_nonneg_left (hE.trans hEA) (show 0 ≤ 1/V by positivity)
      linarith only [ht]
    _ = C+capBandStatistic u C f := rfl

theorem capBandStatistic_simultaneous_cap {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    {f : Space → ℝ} (hf : ContinuousOn f (closedAnnularShell u (2*u)))
    (hm : ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      f y ≤ (1/((u/8)^3*(Real.pi*4/3)))*(∫ x in closedBall y (u/8), f x))
    (hstat : capBandStatistic u C f ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 → (localCellRadius y)^4*f y ≤ 16*(C+1) := by
  intro y hyl hyh
  have hb := submean_le_capBandStatistic (C := C) hu hf hyl hyh (hm y hyl hyh)
  have ha : 0 ≤ u/100000 := by positivity
  have hay : localCellRadius y ≤ 2*(u/100000) := by dsimp [localCellRadius]; linarith
  have hpy := pow_le_pow_left₀ (show 0 ≤ localCellRadius y by dsimp [localCellRadius]; positivity) hay 4
  have hp : (localCellRadius y)^4 ≤ 16*(u/100000)^4 := by nlinarith only [hpy]
  by_cases hfy : 0 ≤ f y
  · have hh := mul_le_mul_of_nonneg_right hp hfy
    nlinarith only [hh,hb,hstat]
  · have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg
      (show 0 ≤ localCellRadius y by dsimp [localCellRadius]; positivity) 4) (le_of_not_ge hfy)
    nlinarith only [hh,hC]

open MeasureTheory Set Metric

open CoulombAnalysis

lemma capBandStatistic_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {u C : ℝ} {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u))))) :
    Integrable (fun z => capBandStatistic u C (f z)) μ :=
  hi.integral_prod_left.const_mul _

lemma capBandStatistic_nonneg (u C : ℝ) (hu : 0 < u) (f : Space → ℝ) :
    0 ≤ capBandStatistic u C f := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun _ => le_max_right _ _

lemma capBandStatistic_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u C b : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u)))))
    (hp : ∀ x ∈ closedAnnularShell u (2*u),
      (∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ b) :
    (∫ z, capBandStatistic u C (f z) ∂μ) ≤ 4096*b := by
  let A := closedAnnularShell u (2*u)
  let V := (u/8)^3*(Real.pi*4/3)
  have hV : 0 < V := by dsimp [V]; positivity
  have hAc : IsCompact A := closedAnnularShell_compact _ _
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAc.measure_ne_top
  have hvol : volume.real A ≤ (2*u)^3*(Real.pi*4/3) := by
    rw [←space_closedBall_real (0:Space) (by positivity : 0 ≤ 2*u)]
    refine measureReal_mono ?_ (isCompact_closedBall (0:Space) (2*u)).measure_ne_top
    intro x hx
    simpa only [mem_closedBall,dist_zero_right] using hx.2
  have hpt : (∫ x in A, ∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ volume.real A*b := by
    have hh := integral_mono_ae hi.integral_prod_right (integrable_const b)
      ((ae_restrict_mem hAc.measurableSet).mono fun x hx => hp x hx)
    rw [integral_const] at hh
    simpa only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ] using hh
  calc
    _ = (1/V)*(∫ x in A, ∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) := by
      unfold capBandStatistic
      rw [integral_const_mul,integral_integral_swap hi]
    _ ≤ (1/V)*(volume.real A*b) := mul_le_mul_of_nonneg_left hpt (by positivity)
    _ ≤ (1/V)*(((2*u)^3*(Real.pi*4/3))*b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvol hb) (by positivity)
    _ = 4096*b := by dsimp [V]; field_simp; ring

theorem capBandStatistic_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {u C b : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    {f : Ω → Space → ℝ}
    (hi : Integrable (fun p : Ω × Space => max ((u/100000)^4*f p.1 p.2-C) 0)
      (μ.prod (volume.restrict (closedAnnularShell u (2*u)))))
    (hp : ∀ x ∈ closedAnnularShell u (2*u),
      (∫ z, max ((u/100000)^4*f z x-C) 0 ∂μ) ≤ b) :
    μ.real {z | 1 < capBandStatistic u C (f z)} ≤ 4096*b := by
  have ht := capBandStatistic_integrable μ hi
  have hn : 0 ≤ᵐ[μ] (fun z => capBandStatistic u C (f z)) :=
    ae_of_all _ fun z => capBandStatistic_nonneg u C hu (f z)
  have hh := ht.measure_le_integral hn (s := {z | 1 < capBandStatistic u C (f z)})
    (fun _ hz => hz.le)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] at hr
  exact hr.trans (capBandStatistic_expectation μ hu hb hi hp)

end CoulombAtom

end

end OAI
