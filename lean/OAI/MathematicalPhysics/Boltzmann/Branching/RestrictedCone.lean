import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveRestrictedChain
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies

namespace OAI

section

/-! # Uniform bounds and kernel decompositions for restricted collision chains -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_restrict_le (a : ℝ) (K : Kernel KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) (f : KineticPhase → ℝ≥0∞)
    (z : KineticPhase) : step a (K.restrict hS) f z ≤ step a K f z := by
  apply lintegral_mono
  intro s
  exact setLIntegral_le_lintegral _ _

theorem kernel_restrict_add (K L : Kernel KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) :
    (K+L).restrict hS = K.restrict hS+L.restrict hS := by
  ext z E hE
  simp only [Kernel.restrict_apply,add_apply,Measure.restrict_apply hE,
    Measure.add_apply]

theorem restrictedChain_uniform_bound {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (i n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T →
      restrictedChain a K S hS f i n z ≤ B*(C*ENNReal.ofReal (T-a))^n := by
  induction n generalizing i with
  | zero => simpa only [restrictedChain,pow_zero,mul_one] using hf
  | succ n ih =>
    intro z hz
    have hKR : ∀ y, y.1.1 ∈ Icc a T → (K.restrict (hS (i+1))) y univ ≤ C := by
      intro y hy
      exact (Measure.restrict_apply_le _ _).trans (hK y hy)
    have h := step_uniform_bound (K.restrict (hS (i+1))) hKR (ih (i+1)) hz
    simpa only [restrictedChain,pow_succ,mul_assoc] using h

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # A bounded velocity chain stays in its backward spatial cone -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def inSpatialCone (X T V : ℝ) (z : KineticPhase) : Prop :=
  ‖z.1.2‖ ≤ X+(T-z.1.1)*V

theorem flight_inSpatialCone {X T V : ℝ} {z : KineticPhase}
    (hz : inSpatialCone X T V z) {s : ℝ} (hs : s ≤ z.1.1) (hv : ‖z.2‖ ≤ V) :
    inSpatialCone X T V (flight z s) := by
  change ‖z.1.2-(z.1.1-s) • z.2‖ ≤ X+(T-s)*V
  calc
    _ ≤ ‖z.1.2‖+‖(z.1.1-s) • z.2‖ := norm_sub_le _ _
    _ = ‖z.1.2‖+(z.1.1-s)*‖z.2‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs)]
    _ ≤ (X+(T-z.1.1)*V)+(z.1.1-s)*V :=
      add_le_add hz (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hs))
    _ = _ := by ring

theorem small_scaled_cone_in_cube {a X T V r : ℝ} (ha : 0 ≤ a) (hV : 0 ≤ V) (hr : 0 ≤ r)
    (hsmall : r*(X+T*V) < 1/2) {z : KineticPhase}
    (ht : z.1.1 ∈ Icc a T) (hz : inSpatialCone X T V z) : r • z.1.2 ∈ TorusChart.cube := by
  have hx : ‖r • z.1.2‖ < 1/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz hr)
    apply lt_of_le_of_lt _ hsmall
    apply mul_le_mul_of_nonneg_left _ hr
    nlinarith [ha.trans ht.1]
  intro i
  have hi := (PiLp.norm_apply_le (r • z.1.2) i).trans_lt hx
  rw [Real.norm_eq_abs,abs_lt] at hi
  exact ⟨hi.1,hi.2.le⟩

theorem restrictedChain_cone_mono {a T X V : ℝ}
    (K L : Kernel KineticPhase Velocity) (S : ℕ → Set Velocity)
    (hS : ∀ i, MeasurableSet (S i)) (hV : ∀ i v, v ∈ S i → ‖v‖ ≤ V)
    (hKL : ∀ i z, z.1.1 ∈ Icc a T → inSpatialCone X T V z → z.2 ∈ S i → K z ≤ L z)
    (f : KineticPhase → ℝ≥0∞) (i n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → inSpatialCone X T V z → z.2 ∈ S i →
      restrictedChain a K S hS f i n z ≤ restrictedChain a L S hS f i n z := by
  induction n generalizing i with
  | zero => intro _ _ _ _; exact le_rfl
  | succ n ih =>
    intro z hz hcone hzS
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ht : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
    have hc := flight_inSpatialCone hcone hs.2 (hV i z.2 hzS)
    change (∫⁻ v in S (i+1), restrictedChain a K S hS f (i+1) n ((flight z s).1,v)
      ∂K (flight z s)) ≤ ∫⁻ v in S (i+1),
        restrictedChain a L S hS f (i+1) n ((flight z s).1,v) ∂L (flight z s)
    apply (lintegral_mono' (Measure.restrict_mono_measure (hKL i (flight z s) ht hc hzS) (S (i+1))) le_rfl).trans
    apply setLIntegral_mono' (hS (i+1))
    intro v hv
    exact ih (i+1) _ ht hc hv

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
