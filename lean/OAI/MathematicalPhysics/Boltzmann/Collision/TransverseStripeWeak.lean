import OAI.MathematicalPhysics.Boltzmann.Branching.AffineSlices
import OAI.MathematicalPhysics.Boltzmann.Branching.ShiftedStripe
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar

namespace OAI

section

/-! # Time spent by a nonaxial free flight near the transverse origin -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness

theorem transverse_flight_time_bound (x v : Transverse) (hv : v ≠ 0)
    (t ρ : ℝ) :
    volume {s : ℝ | ‖x-(t-s) • v‖ < ρ} ≤ ENNReal.ofReal (2*ρ/‖v‖) := by
  let e := direction v
  let A := inner ℝ e x-t*‖v‖
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he : inner ℝ e v = ‖v‖ := by
    dsimp [e,direction]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hp (s : ℝ) : inner ℝ e (x-(t-s) • v) = A-(-‖v‖)*s := by
    rw [inner_sub_right,inner_smul_right,he]
    dsimp [A]
    ring
  have hS : MeasurableSet {s : ℝ | ‖x-(t-s) • v‖ < ρ} := by
    apply measurableSet_lt <;> fun_prop
  have hb : (∫⁻ s : ℝ, if ‖x-(t-s) • v‖ < ρ then (1 : ℝ≥0∞) else 0) ≤
      ∫⁻ s : ℝ, if |A-(-‖v‖)*s-0| ≤ ρ then (1 : ℝ≥0∞) else 0 := by
    apply lintegral_mono
    intro s
    by_cases hs : ‖x-(t-s) • v‖ < ρ
    · have hi := abs_real_inner_le_norm e (x-(t-s) • v)
      rw [hp,show ‖e‖ = 1 from norm_direction hv,one_mul] at hi
      simp only [sub_zero,ite_eq_left hs,ite_eq_left (hi.trans hs.le),le_refl]
    · simp only [ite_eq_right hs]
      exact bot_le
  have hleft : (∫⁻ s : ℝ, if ‖x-(t-s) • v‖ < ρ then (1 : ℝ≥0∞) else 0) =
      volume {s : ℝ | ‖x-(t-s) • v‖ < ρ} := by
    simpa only [indicator_apply,mem_ofPred_eq,one_mul] using lintegral_indicator_const hS (1 : ℝ≥0∞)
  rw [hleft,AffineSlices.lintegral_affine_interval _ measurable_const A 0 ρ
    (neg_ne_zero.mpr hn)] at hb
  simpa only [abs_neg,abs_norm,lintegral_const,Measure.restrict_apply_univ,zero_sub,zero_add,
    Real.volume_Icc,sub_neg_eq_add,← two_mul,one_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg v)),div_eq_mul_inv,mul_comm] using hb

end BoltzmannNonuniqueness

end

end

section

/-! # Stripe averaging on the transverse plane and additional fibers -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def transverseCartesian : Transverse ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem transverseCartesian_measurePreserving : MeasurePreserving transverseCartesian :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

theorem centeredStripe_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (σ : Bool) :
    Compactness.WeakStarLInfConverges volume
      (fun n x => centeredStripe (p n) (d n) σ x) (fun _ => 0) :=
  PeriodicAveraging.weakStar_zero hp hplim
    (fun n => centeredStripe_periodic (p n) (d n) σ)
    (fun n => centeredStripe_measurable (p n) (d n) σ)
    (fun n => centeredStripe_bound (p n) (d n) σ)
    (fun n => centeredStripe_mean (hp n) (d n) σ)

theorem centeredStripe_transverse_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (σ : Bool) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n y => centeredStripe (p n) (d n) σ (y 0)) (fun _ => 0) := by
  have hprod : Compactness.WeakStarLInfConverges
      ((volume : Measure ℝ).prod volume)
      (fun n (z : ℝ × ℝ) => centeredStripe (p n) (d n) σ z.1) (fun _ => 0) :=
    Compactness.weakStar_zero_of_fibers
      (fun n => (centeredStripe_measurable (p n) (d n) σ).comp measurable_fst)
      (fun n z => centeredStripe_bound (p n) (d n) σ z.1)
      (fun _ => centeredStripe_weakStar hp hplim d σ)
  exact hprod.comp_measurableEquiv transverseCartesian transverseCartesian_measurePreserving

theorem centeredStripe_fiber_weakStar {W : Type*} [MeasurableSpace W]
    (ν : Measure W) [SFinite ν] {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) {d : ℕ → W → ℝ} (hd : ∀ n, Measurable (d n)) (σ : Bool) :
    Compactness.WeakStarLInfConverges ((volume : Measure Transverse).prod ν)
      (fun n z => centeredStripe (p n) (d n z.2) σ (z.1 0)) (fun _ => 0) := by
  apply Compactness.weakStar_zero_of_fibers
  · intro n
    have hm : Measurable (fun z : Transverse × W => z.1 0-d n z.2) :=
      (by fun_prop : Measurable (fun z : Transverse × W => z.1 0)).sub ((hd n).comp measurable_snd)
    exact ((measurable_const.indicator (stripeLine_measurable (p n) σ)).comp hm).sub_const (1/4)
  · intro n z
    exact centeredStripe_bound (p n) (d n z.2) σ (z.1 0)
  · intro w
    exact centeredStripe_transverse_weakStar hp hplim (fun n => d n w) σ

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
