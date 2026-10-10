import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoreHistoryCountsBarrier
import OAI.Analysis.CoulombIonization.Localization.CoreObservationEnsembleBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BallAverageKernel_barrier_scope

open MeasureTheory Set Metric

open CoulombAnalysis

lemma space_closedBall_real (y : Space) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall y R) = R^3*(Real.pi*4/3) := by
  rw [Measure.real,EuclideanSpace.volume_closedBall_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,ENNReal.toReal_ofReal (by positivity)]

def ballAverageKernel (R : ℝ) : Space → ℝ :=
  (closedBall 0 R).indicator (fun _ => 1/(R^3*(Real.pi*4/3)))

lemma ballAverageKernel_measurable (R : ℝ) : Measurable (ballAverageKernel R) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

lemma ballAverageKernel_nonneg {R : ℝ} (hR : 0 < R) (z : Space) : 0 ≤ ballAverageKernel R z := by
  apply indicator_nonneg
  intro _ _
  positivity

lemma ballAverageKernel_support (R : ℝ) (z : Space) (hz : ballAverageKernel R z ≠ 0) : ‖z‖ ≤ R := by
  by_contra hh
  have hn : z ∉ closedBall (0:Space) R := by simpa only [mem_closedBall,dist_zero_right] using hh
  exact hz (by simp [ballAverageKernel,hn])

lemma ballAverageKernel_bound {R : ℝ} (hR : 0 < R) (z : Space) :
    |ballAverageKernel R z| ≤ 1/(R^3*(Real.pi*4/3)) := by
  by_cases hz : z ∈ closedBall (0:Space) R
  · simp only [ballAverageKernel,indicator_of_mem hz,abs_of_pos (by positivity : 0 < 1/(R^3*(Real.pi*4/3))),le_refl]
  · simp only [ballAverageKernel,indicator_of_notMem hz,abs_zero]
    positivity

lemma ballAverageKernel_radial (R : ℝ) : IsRadial (ballAverageKernel R) := by
  intro x y hxy
  simp only [ballAverageKernel,indicator,mem_closedBall,dist_zero_right,hxy]

lemma ballAverageKernel_mass {R : ℝ} (hR : 0 < R) : ∫ z, ballAverageKernel R z = 1 := by
  unfold ballAverageKernel
  rw [integral_indicator isClosed_closedBall.measurableSet,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,←Measure.real,space_closedBall_real 0 hR.le]
  field_simp

end Work_BallAverageKernel_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

lemma joinLists_empty {α : Type*} {N : ℕ} (x : Fin N → α) (y : Fin 0 → α) :
    joinLists x y = x := by
  funext i
  have hi : finSumFinEquiv (Sum.inl i : Fin N ⊕ Fin 0) = i := Fin.ext rfl
  simpa only [hi] using joinLists_left x y i

lemma coreSlice_empty {N : ℕ} (ψ : FormVector N) (s : Spins 0) (v : Configuration 0) :
    coreSlice (M := 0) ψ s v = ψ := by
  cases ψ
  simp only [coreSlice,joinLists_empty,finSumFinEquiv_apply_left,Fin.castAdd_zero]
  rfl

lemma coreLawAverage_empty {N : ℕ} (ψ : FormVector N) (F : FormVector N → ℝ) :
    coreLawAverage (M := 0) ψ F = F ψ := by
  unfold coreLawAverage
  simp [coreSlice_empty,Spins,Configuration,Measure.real,volume_pi]

namespace CoreObservationEnsemble

lemma initial_mass {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) :
    (initial ψ hψ).mass = formMass ψ := by
  change (∑ _i : Unit, formMass ψ) = formMass ψ
  simp
lemma initial_countMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) :
    (initial ψ hψ).countMoment y R = rawCountMoment ψ y R := by
  change (∑ _i : Unit, coreLawAverage (M := 0) ψ (fun f => rawCountMoment f y R)) = _
  simp [coreLawAverage_empty]
lemma initial_fieldMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) (Z lam : ℝ) (y : Space) :
    (initial ψ hψ).fieldMoment Z lam y = coreFieldSquare Z lam y ψ := by
  change (∑ _i : Unit, coreLawAverage (M := 0) ψ (coreFieldSquare Z lam y)) = _
  simp [coreLawAverage_empty]
lemma initial_excess {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) (Z lam : ℝ) :
    (initial ψ hψ).excess Z lam = corePriceExcess Z lam ψ := by
  change (∑ _i : Unit, coreLawAverage (M := 0) ψ (corePriceExcess Z lam)) = _
  simp [coreLawAverage_empty]

lemma countMoment_le_of_radius (E : CoreObservationEnsemble) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : E.countMoment y R ≤ E.countMoment z S :=
  Finset.sum_le_sum (fun i _ => (E.graph i).countMoment_le_of_radius y z h)

lemma outMoment_le_ball_field (E : CoreObservationEnsemble) (y : Space) {a Z lam Q : ℝ}
    (ha : 0 < a) (hsep : 5*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hQ : ∀ z ∈ closedBall y (4*a),
      (E.observe (coreFirstRadialCut y (by positivity : 0 ≤ 2*a) ha)
        (coreFirstRadialCut_partition y (by positivity : 0 ≤ 2*a) ha)).fieldMoment Z lam z ≤ Q) :
    E.outMoment y (by positivity : 0 ≤ 2*a) ha Z lam ≤ 64*Q := by
  have hh := E.outMoment_spatial y (by positivity : 0 ≤ 2*a) ha ha
    (by linarith : 2*a+a+2*a ≤ ‖y‖) (by linarith : 2*a+2*a ≤ ‖y‖) hZ hlam
    (ballAverageKernel_measurable a) (ballAverageKernel_nonneg ha)
    (ballAverageKernel_support a) (ballAverageKernel_bound ha)
    (ballAverageKernel_radial a) (ballAverageKernel_mass ha)
  have he : 2*a+a+a = 4*a := by ring
  rw [he] at hh
  let E' := E.observe (coreFirstRadialCut y (by positivity : 0 ≤ 2*a) ha)
    (coreFirstRadialCut_partition y (by positivity : 0 ≤ 2*a) ha)
  have hi := E'.fieldMoment_ball_integrable y ha (by linarith : 4*a+a ≤ ‖y‖) hZ hlam
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (4*a)) :=
    integrableOn_const (isCompact_closedBall y (4*a)).measure_lt_top.ne
  have hm := setIntegral_mono_on hi hc isClosed_closedBall.measurableSet hQ
  have hb : 0 ≤ 1/(a^3*(Real.pi*4/3)) := by positivity
  have hout := hh.trans (mul_le_mul_of_nonneg_left hm hb)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hout
  have hv : 1/(a^3*(Real.pi*4/3))*((4*a)^3*(Real.pi*4/3)*Q) = 64*Q := by
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  rwa [hv] at hout

end CoreObservationEnsemble

open MeasureTheory Set Metric
open scoped BigOperators

def localHistoryRadius (a : ℝ) (n : ℕ) : ℝ := a/(((n:ℝ)+1)*((n:ℝ)+2))
def localHistoryReach (a : ℝ) (n : ℕ) : ℝ := 4*a*(1-1/((n:ℝ)+1))

lemma localHistoryRadius_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < localHistoryRadius a n := by
  unfold localHistoryRadius
  positivity
lemma localHistoryRadius_le {a : ℝ} (ha : 0 < a) (n : ℕ) : localHistoryRadius a n ≤ a := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  unfold localHistoryRadius
  apply (div_le_iff₀ (by positivity)).2
  exact le_mul_of_one_le_right ha.le (by nlinarith)
lemma localHistoryReach_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 ≤ localHistoryReach a n := by
  unfold localHistoryReach
  apply mul_nonneg (by positivity)
  have : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith
lemma localHistoryReach_lt {a : ℝ} (ha : 0 < a) (n : ℕ) : localHistoryReach a n < 4*a := by
  unfold localHistoryReach
  have : 0 < 1/((n:ℝ)+1) := by positivity
  nlinarith
lemma localHistoryReach_step (a : ℝ) (n : ℕ) :
    localHistoryReach a (n+1) = localHistoryReach a n+4*localHistoryRadius a n := by
  unfold localHistoryReach localHistoryRadius
  push_cast
  field_simp
  ring

inductive CoreLocalHistory (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ) (ha : 0 < a) :
    ℕ → CoreObservationEnsemble → Prop
  | initial : CoreLocalHistory E₀ y₀ a ha 0 E₀
  | observe {n : ℕ} {E : CoreObservationEnsemble} (hE : CoreLocalHistory E₀ y₀ a ha n E)
      (y : Space) (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
      CoreLocalHistory E₀ y₀ a ha (n+1)
        (E.observe (coreFirstRadialCut y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
          (localHistoryRadius_pos ha n))
          (coreFirstRadialCut_partition y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
            (localHistoryRadius_pos ha n)))

namespace CoreLocalHistory
variable {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a : ℝ} {ha : 0 < a} {n : ℕ}

lemma mass (hE : CoreLocalHistory E₀ y₀ a ha n E) : E.mass = E₀.mass := by
  induction hE with
  | initial => rfl
  | observe hE y hy ih => rw [CoreObservationEnsemble.observe_mass,ih]

lemma countMoment (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space) (R : ℝ) :
    E.countMoment y R ≤ E₀.countMoment y R := by
  induction hE with
  | initial => rfl
  | observe hE z hz ih => exact (CoreObservationEnsemble.observe_countMoment ..).trans ih

lemma countMoment_local (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    E.countMoment y (4*localHistoryRadius a n) ≤ E₀.countMoment y₀ (8*a) := by
  apply (E.countMoment_le_of_radius y y₀ ?_).trans (hE.countMoment y₀ (8*a))
  have hh : ‖y-y₀‖ ≤ localHistoryReach a n := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have h1 := localHistoryReach_lt ha n
  have h2 := localHistoryRadius_le ha n
  linarith

include ha in
lemma center_nuclear_separation (hsep : 12*a ≤ ‖y₀‖) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) : 8*a ≤ ‖y‖ := by
  have hh : ‖y-y₀‖ ≤ localHistoryReach a n := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hh' : ‖y₀‖ ≤ ‖y‖+‖y-y₀‖ := by
    have := norm_add_le y (y₀-y)
    simpa only [add_sub_cancel, norm_sub_rev] using this
  have h1 := localHistoryReach_lt ha n
  linarith

lemma next_center (y z : Space) (hy : y ∈ closedBall y₀ (localHistoryReach a n))
    (hz : z ∈ closedBall y (4*localHistoryRadius a n)) :
    z ∈ closedBall y₀ (localHistoryReach a (n+1)) := by
  rw [mem_closedBall,localHistoryReach_step]
  exact (dist_triangle z y y₀).trans (add_le_add hz hy |>.trans_eq (add_comm _ _))

end CoreLocalHistory

end CoulombAtom

end

end OAI
