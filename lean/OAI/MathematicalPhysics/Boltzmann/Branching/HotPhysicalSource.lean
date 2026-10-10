import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLipschitz
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.ZeroProfileParameters
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound

namespace OAI

section

/-! # A fixed negligible velocity set for the weighted local construction

The exceptional set depends only on H and its proved quadratic gain bound,
not on a solution or an iterate. Setting the gain to zero there preserves
its almost-everywhere collision meaning and gives pointwise bounded sources.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

def good (q : ℝ) : Set Velocity := {v |
  nonnegativeGain (fun w => ENNReal.ofReal (H q w)) (fun w => ENNReal.ofReal (H q w)) v ≤
    ENNReal.ofReal (HotApplication.realBound q * H q v)}

theorem measurable_nonnegativeGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (nonnegativeGain f g) := by
  let : SFinite (gainPairMeasure) := Measure.prod.instSFinite
  have hl : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterLeft p.1 p.2.1 p.2.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterRight p.1 p.2.1 p.2.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      ENNReal.ofReal (collisionKernel p.1 p.2.1 p.2.2) / 2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (((hf.comp hl).mul (hg.comp hr)).add
    ((hg.comp hl).mul (hf.comp hr)))).lintegral_prod_right'

theorem measurableSet_good (q : ℝ) : MeasurableSet (good q) :=
  measurableSet_le (measurable_nonnegativeGain (measurable_H q).ennreal_ofReal
    (measurable_H q).ennreal_ofReal)
    ((measurable_H q).const_mul (HotApplication.realBound q)).ennreal_ofReal

theorem ae_good (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) : ∀ᵐ v : Velocity, v ∈ good q :=
  HotApplication.quadratic_gain_le_constant hcarleman hq₁ hq₂

theorem integrable_H_gain {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) :=
  GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv

theorem H_gain_bound {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v ≤ HotApplication.realBound q * H q v :=
  GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
    (mul_nonneg (HotApplication.realBound_pos q).le (H_nonneg q v)) v 0 hv

variable {X : Type*} [MeasurableSpace X]

def density (q : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := H q p.2 * f p

def gain (q b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := by
  classical
  exact if p.2 ∈ good q then KineticCollisionNullSets.gain b (density q f) p / H q p.2 else 0

def frequency (q b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  KineticCollisionNullSets.frequency b (density q f) p

theorem measurable_density {f : X × Velocity → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (density q f) := ((measurable_H q).comp measurable_snd).mul hf

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (gain q b f) :=
  Measurable.ite ((measurableSet_good q).preimage measurable_snd)
    ((KineticCollisionNullSets.measurable_gain (measurable_density hf q) b).div
      ((measurable_H q).comp measurable_snd)) measurable_const

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (frequency q b f) :=
  KineticCollisionNullSets.measurable_frequency (measurable_density hf q) b

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Pointwise weighted gain bounds off the fixed exceptional set -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem actual_gain_bound {q A : ℝ} {v : Velocity} (hv : v ∈ good q)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v ≤ A^2 * HotApplication.realBound q * H q v := by
  have hi := GainOrder.integrable_const_mul A v (integrable_H_gain hv)
  calc
    _ ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) 0 v :=
      CollisionCutoff.gain_le b hfm hf v 0 (GainOrder.integrable_of_le hfm hf hfB v hi)
    _ ≤ BoltzmannNonuniqueness.gain (fun p => A * H q p.2) 0 v :=
      GainOrder.gain_mono hfm hf hfB v 0 hi
    _ = A^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v :=
      GainOrder.gain_const_mul A (H q) v 0
    _ ≤ A^2 * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (sq_nonneg A)
    _ = _ := by ring

theorem actual_gain_upper_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v - CollisionCutoff.gain b g v ≤
      (D * (A+B) * HotApplication.realBound q) * H q v := by
  have hbase := integrable_H_gain hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hbase)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hbase)
  have hfc := CollisionCutoff.integrable_gain b hfm hf v hfi
  have hgc := CollisionCutoff.integrable_gain b hgm hg v hgi
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p
        ∂((volume : Measure Velocity).prod sphereArea) := (integral_sub hfc hgc).symm
    _ ≤ ∫ p, (D*(A+B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono (hfc.sub hgc) (hbase.const_mul _)
        (GainUpperDifference.cutoff_integrand_bound hA hB hD hf hg hfB hgB hfg b v)
    _ = (D*(A+B)) * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v := integral_const_mul _ _
    _ ≤ (D*(A+B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

theorem actual_gain_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (b : ℝ) :
    |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| ≤
      (D*(A+B)*HotApplication.realBound q) * H q v := by
  have h₁ := actual_gain_upper_difference hv hA hB hD hfm hgm hf hg hfB hgB
    (fun w => (le_abs_self _).trans (hfg w)) b
  have h₂ := actual_gain_upper_difference hv hB hA hD hgm hfm hg hf hgB hfB
    (fun w => (le_abs_self _).trans (by simpa only [abs_sub_comm] using hfg w)) b
  rw [add_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gain_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (q b : ℝ) (p : X × Velocity) :
    0 ≤ gain q b f p := by
  unfold gain
  split_ifs
  · apply div_nonneg _ (H_nonneg _ _)
    apply integral_nonneg
    intro w
    exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
      (mul_nonneg (H_nonneg _ _) (hf _))) (mul_nonneg (H_nonneg _ _) (hf _))
  · exact le_rfl

theorem gain_bound {q A : ℝ} (_hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (b : ℝ) (p : X × Velocity) :
    gain q b f p ≤ A^2 * HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_bound hv
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
    intro w
    exact (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · exact mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le

theorem gain_difference {q A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (b : ℝ) (p : X × Velocity) :
    |gain q b f p - gain q b g p| ≤ D*(A+B)*HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · rw [← sub_div, abs_div, abs_of_pos (H_pos q p.2)]
    apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_difference hv hA hB hD
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
      (fun w => mul_nonneg (H_nonneg _ _) (hg _).1)
      (fun w => (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
      (fun w => (mul_le_mul_of_nonneg_left (hg _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
    intro w
    change |H q w * f (p.1,w) - H q w * g (p.1,w)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (hfg _) (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (HotApplication.realBound_pos q).le

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Loss estimates and the collision meaning of weighted representatives -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem density_bounds {q A : ℝ} {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (p : X × Velocity) :
    0 ≤ density q f p ∧ density q f p ≤ A * H q p.2 :=
  ⟨mul_nonneg (H_nonneg _ _) (hf p).1,
    (mul_le_mul_of_nonneg_left (hf p).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)⟩

omit [MeasurableSpace X] in
theorem density_difference {q D : ℝ} {f g : X × Velocity → ℝ}
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |density q f p - density q g p| ≤ D * H q p.2 := by
  unfold density
  rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_left (hfg p) (H_nonneg _ _)).trans_eq (mul_comm _ _)

omit [MeasurableSpace X] in
theorem frequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (q b : ℝ) (p : X × Velocity) : 0 ≤ frequency q b f p :=
  CutoffLipschitz.frequency_nonneg (fun _ => mul_nonneg (H_nonneg _ _) (hf _)) b p.2

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A)
    (p : X × Velocity) : frequency q b f p ≤ A * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_bound hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hf (p.1,w)).2) p.2

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |frequency q b f p - frequency q b g p| ≤ D * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_difference hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hg (p.1,w)).1)
    (fun w => (density_bounds hf (p.1,w)).2) (fun w => (density_bounds hg (p.1,w)).2)
    (fun w => density_difference hfg (p.1,w)) p.2

omit [MeasurableSpace X] in
theorem physical_gain_eq {q b : ℝ} (f : X × Velocity → ℝ) {p : X × Velocity}
    (hp : p.2 ∈ good q) : H q p.2 * gain q b f p =
      KineticCollisionNullSets.gain b (density q f) p := by
  rw [gain, ite_eq_left hp]
  field_simp [(H_pos q p.2).ne']

omit [MeasurableSpace X] in
theorem ae_physical_gain (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (b : ℝ) (f : X × Velocity → ℝ) :
    ∀ᵐ v : Velocity, ∀ x : X, H q v * gain q b f (x,v) =
      KineticCollisionNullSets.gain b (density q f) (x,v) := by
  have hg : ∀ᵐ v : Velocity, v ∈ good q := ae_good hcarleman hq₁ hq₂
  exact hg.mono (fun v hv x => physical_gain_eq f (p := (x,v)) hv)

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Bounded positive source for the H-weighted local equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

def source (q b L : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain q b f p + (L - frequency q b f p) * f p

theorem measurable_source {f : X × Velocity → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (source q b L f) :=
  (measurable_gain hf q b).add ((measurable_const.sub (measurable_frequency hf q b)).mul hf)

theorem source_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (p : X × Velocity) :
    0 ≤ source q b L f p ∧ source q b L f p ≤ HotApplication.realBound q * R^2 + L*R := by
  have hν := frequency_nonneg (fun p => (hf p).1) q b p
  have hνB := frequency_bound hq hb hfm hf p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hf p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hf p).1)
  · have hg := gain_bound (q := q) hR hfm hf b p
    have hl : (L - frequency q b f p) * f p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hf p).1).trans
        (mul_le_mul_of_nonneg_left (hf p).2 hLp)
    unfold source
    nlinarith only [hg,hl]

theorem source_difference {q b L R D : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ R)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |source q b L f p - source q b L g p| ≤
      (2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L)*D := by
  have hgain := gain_difference (q := q) hR hR hD hfm hgm hf hg hfg b p
  have hνdiff := frequency_difference hq hb hfm hgm hf hg hfg p
  have hνfb : |frequency q b f p| ≤ R * CutoffLipschitz.frequencyConstant q b := by
    rw [abs_of_nonneg (frequency_nonneg (fun p => (hf p).1) q b p)]
    exact frequency_bound hq hb hfm hf p
  have hgabs : |g p| ≤ R := by rw [abs_of_nonneg (hg p).1]; exact (hg p).2
  have hloss : |frequency q b f p * f p - frequency q b g p * g p| ≤
      2 * CutoffLipschitz.frequencyConstant q b * R * D := by
    calc
      _ = |frequency q b f p * (f p-g p) + (frequency q b f p-frequency q b g p)*g p| := by
        congr 1; ring
      _ ≤ |frequency q b f p| * |f p-g p| + |frequency q b f p-frequency q b g p| * |g p| := by
        simpa only [abs_mul] using abs_add_le (frequency q b f p * (f p-g p))
          ((frequency q b f p-frequency q b g p)*g p)
      _ ≤ (R*CutoffLipschitz.frequencyConstant q b)*D + (D*CutoffLipschitz.frequencyConstant q b)*R :=
        add_le_add (mul_le_mul hνfb (hfg p) (abs_nonneg _)
          (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)))
          (mul_le_mul hνdiff hgabs (abs_nonneg _)
            (mul_nonneg hD (CutoffLipschitz.frequencyConstant_nonneg hb q)))
      _ = _ := by ring
  calc
    _ = |(gain q b f p-gain q b g p)+L*(f p-g p)-
        (frequency q b f p*f p-frequency q b g p*g p)| := by unfold source; congr 1; ring
    _ ≤ |gain q b f p-gain q b g p|+L*|f p-g p|+
        |frequency q b f p*f p-frequency q b g p*g p| := by
      have ha : |(gain q b f p-gain q b g p)+L*(f p-g p)| ≤
          |gain q b f p-gain q b g p|+L*|f p-g p| := by
        simpa only [abs_mul, abs_of_nonneg hL] using
          abs_add_le (gain q b f p-gain q b g p) (L*(f p-g p))
      exact (abs_sub _ _).trans (add_le_add ha le_rfl)
    _ ≤ D*(R+R)*HotApplication.realBound q+L*D+
        2*CutoffLipschitz.frequencyConstant q b*R*D :=
      add_le_add (add_le_add hgain (mul_le_mul_of_nonneg_left (hfg p) hL)) hloss
    _ = _ := by ring

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The nonnegative hot remainder of the countable cold construction -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoltzmannNonuniqueness.GaussianLocal

variable {I : Type*} [Countable I]

def hotRemainder (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : I → JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  F z - ∑' i, coldLimit β b L T F (c₀ i) z

def hotForcing (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : I → JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  forcing β b L F z - ∑' i, coldForcing β b L F (coldLimit β b L T F (c₀ i)) z

private theorem value_sub {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {g h : ℝ × JetPrototype.Phase → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S)
    (f₀ k₀ : JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) :
    PositiveIntegral.value T L JetBarrier.flight f₀ g z -
      PositiveIntegral.value T L JetBarrier.flight k₀ h z =
      PositiveIntegral.value T L JetBarrier.flight (fun p => f₀ p - k₀ p) (fun q => g q - h q) z := by
  unfold PositiveIntegral.value
  have he (r : ℝ) : Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
      (g (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) -
        h (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2)) =
      Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
        g (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) -
      Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
        h (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) := mul_sub _ _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (PositiveIntegral.damped_integrable hT hL measurable_flight hgm hg z)
    (PositiveIntegral.damped_integrable hT hL measurable_flight hhm hh z)]
  ring

theorem hotRemainder_solution {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z) :
    Measurable (hotRemainder β b L T F c₀) ∧
      (∀ z, 0 ≤ hotRemainder β b L T F c₀ z ∧ hotRemainder β b L T F c₀ z ≤ F z) ∧
      (∀ z, 0 ≤ hotForcing β b L T F c₀ z ∧ hotForcing β b L T F c₀ z ≤ forcing β b L F z) ∧
      ∀ z, hotRemainder β b L T F c₀ z = PositiveIntegral.value T L JetBarrier.flight
        (fun p => F₀ p - ∑' i, c₀ i p) (hotForcing β b L T F c₀) z := by
  let c (i : I) := coldLimit β b L T F (c₀ i)
  let G (i : I) := coldForcing β b L F (c i)
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  have hc (i) := coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq
  have hcf (z) := cold_family_summable hβ hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq z
  have hcm : ∀ i, Measurable (c i) := fun i => (hc i).1
  have hcb (i) (z) : 0 ≤ c i z ∧ c i z ≤ R :=
    ⟨((hc i).2.1 z).1, ((hc i).2.1 z).2.trans (hF z).2⟩
  have hgm : ∀ i, Measurable (G i) := fun i => measurable_coldForcing hFm (hcm i) β b L
  have hgb (i) (z) : 0 ≤ G i z ∧ G i z ≤ S :=
    GaussianCutoff.coldSource_bounds (F := state F) (c := state (c i)) hβ hb hR hloss
      (fun p => hF (p.1.1, (p.1.2, p.2))) (fun p => hcb i (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hfs (z) : 0 ≤ forcing β b L F z ∧ forcing β b L F z ≤ S :=
    GaussianCutoff.source_bounds (f := state F) hβ hb hR hloss
      (fun p => hF (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hGfinite (s : Finset I) (z) : ∑ i ∈ s, G i z ≤ forcing β b L F z :=
    GaussianCutoff.finite_sum_coldSource_le hβ hb hR hloss s
      (fun i _ => measurable_state (hcm i)) (measurable_state hFm)
      (fun i _ p => hcb i (p.1.1, (p.1.2, p.2)))
      (fun p => hF (p.1.1, (p.1.2, p.2)))
      (fun p => finite_sum_coldLimit_le hβ hb hL hT hR hloss s hFm (fun i _ => hc₀m i)
        hF (fun i _ => hc₀ i) hF₀ (hSum₀ s) hFeq (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hGs (z) : Summable (fun i => G i z) := summable_of_sum_le (fun i => (hgb i z).1) (fun s => hGfinite s z)
  have hGle (z) : (∑' i, G i z) ≤ forcing β b L F z :=
    Real.tsum_le_of_sum_le (fun i => (hgb i z).1) (fun s => hGfinite s z)
  have hSm : Measurable (fun z => ∑' i, G i z) := Measurable.tsum hgm
  have hSabs (z) : |∑' i, G i z| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hgb i z).1))]
    exact (hGle z).trans (hfs z).2
  refine ⟨hFm.sub (Measurable.tsum hcm), ?_, ?_, ?_⟩
  · intro z
    exact ⟨sub_nonneg.mpr (hcf z).2, sub_le_self _ (tsum_nonneg (fun i => (hcb i z).1))⟩
  · intro z
    exact ⟨sub_nonneg.mpr (hGle z), sub_le_self _ (tsum_nonneg (fun i => (hgb i z).1))⟩
  · intro z
    have hs := PositiveIntegral.hasSum_value hT hL measurable_flight c₀
      (fun p => summable_of_sum_le (fun i => (hc₀ i p).1) (fun s => hSum₀ s p)) G hgm hgb hGs
      (fun q => (hGle q).trans (hfs q).2) z
    have he : (fun i => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) z) =
        (fun i => c i z) := funext (fun i => ((hc i).2.2.1 z).symm)
    rw [he] at hs
    change F z - ∑' i, c i z = _
    rw [hFeq z, hs.tsum_eq]
    exact value_sub hT hL (measurable_forcing hFm β b L) hSm
      (fun q => by rw [abs_of_nonneg (hfs q).1]; exact (hfs q).2) hSabs F₀
      (fun p => ∑' i, c₀ i p) z

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Polynomial control of a hot remainder satisfying the mild equation a.e. -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  have hv : Continuous (fun t => size (fun p =>
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :=
    continuous_size_of_mildAE hT hL hA hS hf₀m hgm hf₀ hg (fun _ => ae_of_all _ (fun _ => rfl))
  apply hv.continuousOn.congr
  intro t ht
  exact size_congr_ae (hfix t ht)

theorem zero_seed_bound_ae {T L S R M C B D δ : ℝ} {m : ℕ}
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hBD : B ≤ D) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hsmall : C*D*T ≤ 1) (hm : M+2 ≤ (m+1 : ℕ))
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hf : ∀ u, 0 ≤ f u ∧ f u ≤ R)
    (hzc : ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T))
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ 0)
    (hfix : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)))
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤
        ZeroProfile.source M C B δ m u.1 (size (fun p => f (u.1,p)))+
          L*size (fun p => f (u.1,p))) :
    ∀ t ∈ Icc 0 T, size (fun p => f (t,p)) ≤ ZeroProfile.profile D m t := by
  let z (t : ℝ) := size (fun p => f (t,p))
  have hden : ContinuousOn (fun t => M/(t+δ)) (Icc 0 T) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun t ht => ne_of_gt (by linarith [ht.1]))
  have hwc : ContinuousOn (fun t => ZeroProfile.source M C B δ m t (z t)+L*z t) (Icc 0 T) :=
    (((hden.mul hzc).add ((hzc.pow 2).const_mul C)).add
      ((continuousOn_id.pow m).const_mul B)).add (hzc.const_mul L)
  apply ZeroProfile.le_profile hM hC hBD hD hδ hT hT₁ hL hR hsmall hm hzc
  · intro t _
    exact ⟨size_nonneg _,size_le hR (hfm.comp (measurable_const.prodMk measurable_id))
      (fun p => by rw [abs_of_nonneg (hf (t,p)).1]; exact (hf (t,p)).2)⟩
  · intro t ht
    have hw : IntervalIntegrable (fun r => ZeroProfile.source M C B δ m r (z r)+L*z r)
        volume 0 T := hwc.intervalIntegrable_of_Icc hT
    have hwn (r : ℝ) (hr : r ∈ Icc 0 T) :
        0 ≤ ZeroProfile.source M C B δ m r (z r)+L*z r := by
      have hz : 0 ≤ z r := size_nonneg _
      have hr0 : 0 ≤ r := hr.1
      have hd : 0 < r+δ := by linarith [hr.1]
      unfold ZeroProfile.source
      positivity
    simpa only [mul_zero,zero_add] using
      mild_size_le_of_ae hT hL (by rfl : (0:ℝ) ≤ 0) ht hgm hfm hg hw hwn hinit hsource
        (fun u => (hf u).1) (hfix t ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Gain created outside one distinguished cold color -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotGainRemainder

/-- The loss-free gain of the remainder uses the mixed cold estimate, rather
than the much larger pointwise norm of the cold color. -/
theorem gain_difference_le {q R D M : ℝ} {v : Velocity}
    (hv : v ∈ HotRepresentative.good q) (hD : 0 ≤ D)
    {f c : Velocity → ℝ} (hfm : Measurable f) (hcm : Measurable c)
    (hc : ∀ w, 0 ≤ c w) (hcf : ∀ w, c w ≤ f w)
    (hf : ∀ w, f w ≤ R * H q w) (hrem : ∀ w, f w - c w ≤ D * H q w)
    (hci : Integrable (MixedRealGain.integrand c (H q) v) gainPairMeasure)
    (hcM : MixedRealGain.gain c (H q) v ≤ M * H q v) (b : ℝ) :
    CollisionCutoff.gain b f v - CollisionCutoff.gain b c v ≤
      (2 * D * M + D^2 * HotApplication.realBound q) * H q v := by
  have hfn (w) : 0 ≤ f w := (hc w).trans (hcf w)
  have hcn (w) : c w ≤ R * H q w := (hcf w).trans (hf w)
  have hbase := HotRepresentative.integrable_H_gain hv
  have hfi := GainOrder.integrable_of_le hfm hfn hf v (GainOrder.integrable_const_mul R v hbase)
  have hcii := GainOrder.integrable_of_le hcm hc hcn v (GainOrder.integrable_const_mul R v hbase)
  have hfc := CollisionCutoff.integrable_gain b hfm hfn v hfi
  have hcc := CollisionCutoff.integrable_gain b hcm hc v hcii
  have hpoint (p : Velocity × Sphere) :
      CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b c v p ≤
        (2*D) * MixedRealGain.integrand c (H q) v p +
          D^2 * GainOrder.integrand (H q) v p := by
    let l := scatterLeft v p.1 p.2
    let r := scatterRight v p.1 p.2
    have hl : 0 ≤ f l - c l := sub_nonneg.mpr (hcf l)
    have hr : 0 ≤ f r - c r := sub_nonneg.mpr (hcf r)
    have h₁ := mul_le_mul (hrem l) (hrem r) hr (mul_nonneg hD (H_nonneg q l))
    have h₂ := mul_le_mul_of_nonneg_left (hrem r) (hc l)
    have h₃ := mul_le_mul_of_nonneg_right (hrem l) (hc r)
    have hd : f l * f r - c l * c r ≤
        D * (c l * H q r + H q l * c r) + D^2 * (H q l * H q r) := by
      nlinarith
    have hdn : 0 ≤ f l * f r - c l * c r :=
      sub_nonneg.mpr (mul_le_mul (hcf l) (hcf r) (hc r) (hfn l))
    have hk := mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b v p.1 p.2) hdn
    have hh := mul_le_mul_of_nonneg_left hd (collisionKernel_nonneg v p.1 p.2)
    unfold CollisionCutoff.integrand MixedRealGain.integrand GainOrder.integrand
    dsimp [l,r] at *
    nlinarith
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b c v p
        ∂gainPairMeasure := (integral_sub hfc hcc).symm
    _ ≤ ∫ p, (2*D) * MixedRealGain.integrand c (H q) v p +
        D^2 * GainOrder.integrand (H q) v p ∂gainPairMeasure :=
      integral_mono (hfc.sub hcc) ((hci.const_mul _).add (hbase.const_mul _)) hpoint
    _ = (2*D) * MixedRealGain.gain c (H q) v +
        D^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v := by
      rw [integral_add (hci.const_mul _) (hbase.const_mul _), integral_const_mul, integral_const_mul]
      rfl
    _ ≤ (2*D) * (M * H q v) + D^2 * (HotApplication.realBound q * H q v) :=
      add_le_add (mul_le_mul_of_nonneg_left hcM (by positivity))
        (mul_le_mul_of_nonneg_left (HotRepresentative.H_gain_bound hv) (sq_nonneg D))
    _ = _ := by ring

end BoltzmannNonuniqueness.HotGainRemainder

end

end

section

/-! # Cancellation of artificial damping in the physical collision equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem physical_source_eq {q b L : ℝ} (f : X × Velocity → ℝ) {p : X × Velocity}
    (hp : p.2 ∈ good q) :
    H q p.2 * (source q b L f p-L*f p) =
      CollisionCompactness.collisionSource b (density q f) p := by
  have hg := physical_gain_eq (b := b) f hp
  unfold source CollisionCompactness.collisionSource frequency
  rw [← hg]
  unfold density
  ring

omit [MeasurableSpace X] in
theorem ae_physical_source (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (b L : ℝ) (f : X × Velocity → ℝ) :
    ∀ᵐ v : Velocity, ∀ x : X,
      H q v * (source q b L f (x,v)-L*f (x,v)) =
        CollisionCompactness.collisionSource b (density q f) (x,v) := by
  filter_upwards [ae_good hcarleman hq₁ hq₂] with v hv
  intro x
  exact physical_source_eq (q := q) (b := b) (L := L) (p := (x,v)) f hv

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
