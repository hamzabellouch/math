import OAI.MathematicalPhysics.Boltzmann.Branching.AccessAngleStability
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability

namespace OAI

section

/-! # Bounded weighted averaging is Lipschitz in L1 -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem weighted_average_difference_le {f g w : X × Y → ℝ} {C : ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hwm : Measurable w)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hb : ∀ p, |w p| ≤ C) :
    eLpNorm (fun x => (∫ y, w (x,y)*f (x,y) ∂ν)-(∫ y, w (x,y)*g (x,y) ∂ν)) 1 μ ≤
      ENNReal.ofReal C*eLpNorm (f-g) 1 (μ.prod ν) := by
  have hw : ∀ᵐ p ∂μ.prod ν, ‖w p‖ ≤ C :=
    Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hb p)
  have hi₁ := hfi.bdd_mul hwm.aestronglyMeasurable hw
  have hi₂ := hgi.bdd_mul hwm.aestronglyMeasurable hw
  have he : (fun x => (∫ y, w (x,y)*f (x,y) ∂ν)-(∫ y, w (x,y)*g (x,y) ∂ν)) =ᵐ[μ]
      (fun x => ∫ y, w (x,y)*(f (x,y)-g (x,y)) ∂ν) := by
    filter_upwards [hi₁.prod_right_ae,hi₂.prod_right_ae] with x hx hy
    rw [← integral_sub hx hy]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => (mul_sub _ _ _).symm)
  rw [eLpNorm_congr_ae he]
  apply (eLpNorm_integral_le (hwm.mul (hfm.sub hgm))).trans
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hwm.mul (hfm.sub hgm)).aestronglyMeasurable
  filter_upwards [] with p
  change ‖w p*(f p-g p)‖ ≤ C*‖f p-g p‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb p) (norm_nonneg _)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Positive two-collision entry weight with measurable beam coefficients -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def accessWeight (v : V) (w₁ w₂ : Sphere × Sphere → V)
    (b₁ b₂ : Sphere × Sphere → ℝ) (κ ρ : ℝ) (a : Sphere × Sphere) : ℝ≥0∞ :=
  let u := child v (w₁ a) a.1.1
  let z := child u (w₂ a) a.2.1
  ENNReal.ofReal (4*Real.pi*b₁ a*‖v-w₁ a‖)*
    ENNReal.ofReal (4*Real.pi*b₂ a*‖u-w₂ a‖)*
      (ball (κ • firstAxis) ρ).indicator (fun _ => 1) z

theorem accessWeight_lower {κ ρ ε c : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : ε ≤ 1/12) (hερ : 6*ε ≤ ρ) (hc : 0 < c)
    {e v : V} (he : ‖e‖ = 1) (hv : ‖v-e‖ ≤ ε)
    {w₁ w₂ : Sphere × Sphere → V} {b₁ b₂ : Sphere × Sphere → ℝ}
    (hpartners : ∀ a ∈ accessAngles κ (ρ/2),
      ‖w₁ a-(-e)‖ ≤ ε ∧ ‖w₂ a-beamAxis‖ ≤ ε)
    (hdensity : ∀ a ∈ accessAngles κ (ρ/2), c ≤ b₁ a ∧ c ≤ b₂ a) :
    (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
      (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)) ≤
        ∫⁻ a, accessWeight v w₁ w₂ b₁ b₂ κ ρ a ∂sphereProbability.prod sphereProbability := by
  let A := accessAngles κ (ρ/2)
  let μ := sphereProbability.prod sphereProbability
  let k := ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c)
  have hbound (a : Sphere × Sphere) (ha : a ∈ A) : k ≤ accessWeight v w₁ w₂ b₁ b₂ κ ρ a := by
    obtain ⟨hw₁,hw₂⟩ := hpartners a ha
    obtain ⟨hb₁,hb₂⟩ := hdensity a ha
    have hg := access_pair_stability hκ0 hκ hρ hε hερ he hv hw₁ hw₂ ha
    dsimp only at hg
    have hb₁0 : 0 ≤ b₁ a := hc.le.trans hb₁
    have hb₂0 : 0 ≤ b₂ a := hc.le.trans hb₂
    have h₁ : 4*Real.pi*c ≤ 4*Real.pi*b₁ a*‖v-w₁ a‖ := by
      calc
        _ ≤ 4*Real.pi*b₁ a := mul_le_mul_of_nonneg_left hb₁ (by positivity)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hg.1
    have h₂ : 3*Real.pi*c ≤
        4*Real.pi*b₂ a*‖child v (w₁ a) a.1.1-w₂ a‖ := by
      calc
        _ = 4*Real.pi*c*(3/4) := by ring
        _ ≤ 4*Real.pi*b₂ a*(3/4) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hg.2.1 (by positivity)
    have hz : child (child v (w₁ a) a.1.1) (w₂ a) a.2.1 ∈ ball (κ • firstAxis) ρ := hg.2.2.2.2
    unfold accessWeight
    dsimp only
    rw [indicator_of_mem hz,mul_one]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h₁) (ENNReal.ofReal_le_ofReal h₂)
  calc
    _ = ∫⁻ _a in A, k ∂μ := by rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ a in A, accessWeight v w₁ w₂ b₁ b₂ κ ρ a ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (accessAngles_measurable κ (ρ/2))] with a ha
      exact hbound a ha
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Entropy gives uniform integrability of moment-weighted normalized pairs -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weightedNormalizedPair_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => weightedNormalizedPair (f n)) 1
      (μ.prod (volume.prod volume)) := by
  have hui := normalizedPair_uniformIntegrable hfm hf hi hb
  have hcut (j : ℕ) : UniformIntegrable (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) 1
      (μ.prod (volume.prod volume)) := by
    let R : ℝ := (j:ℝ)+1
    let a : X × (Velocity × Velocity) → ℝ := fun z =>
      if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then pairVelocityWeight z else 0
    have ham : Measurable a := pairVelocityWeight_measurable.ite
      ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
        (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have ha (z) : |a z| ≤ 1+2*R := by
      dsimp only [a]
      split_ifs with hz
      · rw [abs_of_nonneg (show 0 ≤ pairVelocityWeight z by dsimp [pairVelocityWeight]; positivity)]
        dsimp only [pairVelocityWeight]
        linarith [hz.1,hz.2]
      · simp only [abs_zero]
        positivity
    have h := uniformIntegrable_of_bounded_multiplier hui ham
      ⟨1+2*R,by positivity⟩ ha
    have he : (fun n z => a z*normalizedPair volume (f n) z) =
        (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) := by
      funext n z
      dsimp only [a,pairVelocityCut,weightedNormalizedPair,R]
      split_ifs <;> simp only [zero_mul]
    rwa [he] at h
  apply uniformIntegrable_of_approximation hcut
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (8*C) hε
  exact ⟨j,fun n => (pairVelocityCut_L1_error (by positivity : 0 < (j:ℝ)+1)
    (hfm n) (hf n) (hi n) (hb n)).trans hj⟩

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
