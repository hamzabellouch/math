import OAI.MathematicalPhysics.Boltzmann.Branching.ChartPointLift
import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantPlaneIntegral
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Jets.ThermalPointBounds

namespace OAI

section

/-! # The redundant coordinates recover the actual graph-chart velocity -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.RedundantPlane

def normalVector (v p : Velocity) : V := WithLp.ofLp (v-p)

def crossVelocity (v p : Velocity) (L : V) : Velocity :=
  WithLp.toLp 2 (normalVector v p ⨯₃ L)

def tangentOffset (v p : Velocity) : ℝ :=
  inner ℝ (quarterTurn (direction (normal v p))) (transverse v)

theorem normal_norm_sq (v p : Velocity) :
    ‖normal v p‖^2 = normalVector v p 0^2+normalVector v p 1^2 := by
  simp [normal,normalVector,transverse,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]

theorem crossVelocity_on_plane (v p : Velocity) (L : V) :
    inner ℝ (v-p) (crossVelocity v p L) = 0 := by
  simp [crossVelocity,normalVector,PiLp.inner_apply,Fin.sum_univ_succ,cross_apply]
  ring

theorem crossVelocity_axial (v p : Velocity) (L : V) :
    axial (crossVelocity v p L) = coordinates (normalVector v p) ‖normal v p‖ L 0 := by
  simp [crossVelocity,axial,coordinates_apply,cross_apply]

theorem crossVelocity_tangent (v p : Velocity) (L : V) :
    inner ℝ (quarterTurn (direction (normal v p))) (transverse (crossVelocity v p L)) =
      coordinates (normalVector v p) ‖normal v p‖ L 1 := by
  simp [crossVelocity,normalVector,normal,transverse,quarterTurn,direction,
    PiLp.inner_apply,Fin.sum_univ_two,coordinates_apply,cross_apply]
  ring

theorem chart_crossVelocity (v p : Velocity) (hn : normal v p ≠ 0) (L : V) :
    chart v p (coordinates (normalVector v p) ‖normal v p‖ L 0)
      (coordinates (normalVector v p) ‖normal v p‖ L 1+tangentOffset v p) =
      v+crossVelocity v p L := by
  have hp := chart_recovers v p (v+crossVelocity v p L) hn (by
    simpa only [add_sub_cancel_left] using crossVelocity_on_plane v p L)
  have ha : axial (v+crossVelocity v p L)-axial v =
      coordinates (normalVector v p) ‖normal v p‖ L 0 := by
    change (v 2+crossVelocity v p L 2)-v 2 = _
    rw [add_sub_cancel_left]
    exact crossVelocity_axial v p L
  have ht : inner ℝ (quarterTurn (direction (normal v p)))
      (transverse (v+crossVelocity v p L)) =
      coordinates (normalVector v p) ‖normal v p‖ L 1+tangentOffset v p := by
    have he : transverse (v+crossVelocity v p L) =
        transverse v+transverse (crossVelocity v p L) := rfl
    rw [he,inner_add_right,crossVelocity_tangent,tangentOffset,add_comm]
  rwa [ha,ht] at hp

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # The actual Carleman chart integral in redundant plane parameters

The probability density in the redundant normal coordinate is arbitrary.
It can later be chosen bounded with compact support. No regularity of the
normal as a function of preceding collision parameters is required here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.RedundantPlane

attribute [local irreducible] PlaneChart.chart

theorem chart_integral_redundant (v p : Velocity) (hn : normal v p ≠ 0)
    {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ) (hζone : ∫⁻ u, ζ u = 1)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    ENNReal.ofReal (‖normal v p‖⁻¹) *
      (∫⁻ z : ℝ, ∫⁻ s : ℝ, f (chart v p z s)) =
    ∫⁻ L : V, ζ (coordinates (normalVector v p) ‖normal v p‖ L 2) *
      f (v+crossVelocity v p L) := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun zs =>
    f (chart v p zs.1 (zs.2+tangentOffset v p))
  let k : ℝ × ℝ → ChartKernel.Coordinates := fun zs => (p,zs)
  have hk : Measurable k := measurable_const.prodMk measurable_id
  have hchart : Measurable (fun zs : ℝ × ℝ => chart v p zs.1 zs.2) := by
    simpa only [Function.comp_def,k] using (ChartKernel.measurable_point v).comp hk
  have hF : Measurable F := hf.comp (hchart.comp
    (measurable_fst.prodMk (measurable_snd.add_const _)))
  have hi := redundant_coordinates_integral (norm_pos_iff.mpr hn) (normal_norm_sq v p)
    hζ hζone hF
  have hr : (∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s)) =
      ∫⁻ z : ℝ, ∫⁻ s : ℝ, f (chart v p z s) := by
    apply lintegral_congr
    intro z
    exact lintegral_add_right_eq_self (fun s => f (chart v p z s)) (tangentOffset v p)
  rw [hr] at hi
  simpa only [F,chart_crossVelocity v p hn] using hi.symm

theorem gain_redundant (c : Measure Velocity) (v : Velocity)
    (hc : ∀ᵐ p ∂c, normal v p ≠ 0)
    {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ) (hζone : ∫⁻ u, ζ u = 1)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    chartGain c f v = 2 * ∫⁻ p, ∫⁻ L : V,
      ζ (coordinates (normalVector v p) ‖normal v p‖ L 2) *
        f (v+crossVelocity v p L) ∂volume ∂c := by
  unfold chartGain
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hc] with p hp
  exact chart_integral_redundant v p hp hζ hζone hf

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Redundant parameters for the normalized positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.RedundantPlane

def normalCoefficient (v p : Velocity) (L : V) : ℝ :=
  (normalVector v p ⬝ᵥ L)/normSq (normalVector v p)

theorem measurable_redundant_point (v : Velocity) :
    Measurable (fun q : Velocity × V => v+crossVelocity v q.1 q.2) := by
  unfold crossVelocity normalVector
  apply measurable_const.add
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [cross_apply] <;> fun_prop

theorem measurable_normalCoefficient (v : Velocity) :
    Measurable (fun q : Velocity × V => normalCoefficient v q.1 q.2) := by
  unfold normalCoefficient normSq normalVector
  simp only [Matrix.vec3_dotProduct]
  fun_prop

theorem ae_normal_ne (v : Velocity) : ∀ᵐ p ∂volume, normal v p ≠ 0 := by
  have h := (MeasureTheory.QuasiMeasurePreserving.snd
    split_measurePreserving.quasiMeasurePreserving).ae (volume.ae_ne (transverse v))
  have ht : ∀ᵐ p ∂volume, transverse p ≠ transverse v := by
    simpa only [split_apply] using h
  filter_upwards [ht] with p hp
  rw [normal,transverse_sub,sub_ne_zero]
  exact Ne.symm hp

theorem gain_density_redundant (c : Velocity → ℝ≥0∞) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    chartGain (volume.withDensity c) f v =
      2 * ∫⁻ p, ∫⁻ L : V, normalDensity (normalCoefficient v p L) *
        f (v+crossVelocity v p L) ∂volume ∂volume.withDensity c := by
  have hc := (withDensity_absolutelyContinuous volume c).ae_le (ae_normal_ne v)
  simpa only [coordinates_last,normalCoefficient] using
    gain_redundant (volume.withDensity c) v hc measurable_normalDensity lintegral_normalDensity hf

theorem inputKernel_redundant {X : Type*} [MeasurableSpace X]
    (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity)
    (hc : ∀ᵐ p ∂c z.1, normal z.2 p ≠ 0)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂ChartKernel.inputKernel c q z) =
      2 * ∫⁻ p, ∫⁻ L : V, normalDensity (normalCoefficient z.2 p L) *
        (ENNReal.ofReal (H q (z.2+crossVelocity z.2 p L)/H q z.2)*
          f (z.2+crossVelocity z.2 p L)) ∂volume ∂c z.1 := by
  rw [ChartKernel.lintegral_inputKernel_eq_gain c q z hf]
  have hw : Measurable (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)*f ξ) :=
    (((ChartKernel.measurable_H q).div_const _).ennreal_ofReal).mul hf
  simpa only [coordinates_last,normalCoefficient] using
    gain_redundant (c z.1) z.2 hc measurable_normalDensity lintegral_normalDensity hw

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Compact support of redundant plane parameters on retained collision paths -/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.RedundantPlane

theorem normSq_eq_norm_sq (L : V) : normSq L = ‖WithLp.toLp 2 L‖^2 := by
  simp [normSq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring

theorem plane_parameter_sq_bound {δ Vmax P : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ Vmax) (hP : 0 ≤ P) (v p : Velocity) (L : V)
    (hv : ‖v‖ ≤ Vmax) (hp : ‖p‖ ≤ P) (hlow : δ ≤ ‖v-p‖)
    (hout : ‖v+crossVelocity v p L‖ ≤ Vmax)
    (hρ : normalDensity (normalCoefficient v p L) ≠ 0) :
    ‖WithLp.toLp 2 L‖^2 ≤ (2*Vmax)^2/δ^2+(Vmax+P)^2 := by
  have hn : ‖v-p‖ ≤ Vmax+P := (norm_sub_le v p).trans (add_le_add hv hp)
  have hk : ‖crossVelocity v p L‖ ≤ 2*Vmax := by
    calc
      _ = ‖(v+crossVelocity v p L)-v‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖v+crossVelocity v p L‖+‖v‖ := norm_sub_le _ _
      _ ≤ 2*Vmax := by linarith
  have hcoef := normalDensity_support hρ
  have hc : |coordinates (normalVector v p) 1 L 2| ≤ 1 := by
    rw [coordinates_last]
    change |normalCoefficient v p L| ≤ 1
    exact abs_le.mpr ⟨by linarith [hcoef.1],hcoef.2⟩
  have hnorm : normSq (normalVector v p) = ‖v-p‖^2 := normSq_eq_norm_sq _
  have hcross : normSq (normalVector v p ⨯₃ L) = ‖crossVelocity v p L‖^2 := normSq_eq_norm_sq _
  have hl : δ^2 ≤ normSq (normalVector v p) := by
    rw [hnorm]
    nlinarith [norm_nonneg (v-p)]
  have hh : normSq (normalVector v p) ≤ (Vmax+P)^2 := by
    rw [hnorm]
    nlinarith [norm_nonneg (v-p)]
  have hk' : normSq (normalVector v p ⨯₃ L) ≤ (2*Vmax)^2 := by
    rw [hcross]
    nlinarith [norm_nonneg (crossVelocity v p L)]
  rw [← normSq_eq_norm_sq]
  exact normSq_parameter_bound hδ hl hh hk' hc

theorem plane_parameter_bound {δ Vmax P : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ Vmax) (hP : 0 ≤ P) (v p : Velocity) (L : V)
    (hv : ‖v‖ ≤ Vmax) (hp : ‖p‖ ≤ P) (hlow : δ ≤ ‖v-p‖)
    (hout : ‖v+crossVelocity v p L‖ ≤ Vmax)
    (hρ : normalDensity (normalCoefficient v p L) ≠ 0) :
    ‖WithLp.toLp 2 L‖ ≤ (2*Vmax)^2/δ^2+(Vmax+P)^2+1 := by
  have h := plane_parameter_sq_bound hδ hV hP v p L hv hp hlow hout hρ
  have hn := norm_nonneg (WithLp.toLp 2 L)
  nlinarith [sq_nonneg (‖WithLp.toLp 2 L‖-1)]

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
