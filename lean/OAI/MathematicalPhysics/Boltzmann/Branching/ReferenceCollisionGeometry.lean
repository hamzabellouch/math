import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereAntipodal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

section

/-!
# The hard-sphere offspring sphere and reference collision rate

The one-child sphere law gives geometric identities for conservation of
momentum and energy, and bounds for the two-beam collision frequency.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev V := EuclideanSpace ℝ (Fin 3)

/-- One child on the sphere having the two incident velocities as diameter endpoints. -/
def child (v w n : V) : V := (1 / 2 : ℝ) • (v + w) + (‖v - w‖ / 2) • n

theorem child_distance_center (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n - (1 / 2 : ℝ) • (v + w)‖ = ‖v - w‖ / 2 := by
  simp only [child, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hn, mul_one]
  exact abs_of_nonneg (by positivity)

theorem child_pair_sum (v w n : V) : child v w n + child v w (-n) = v + w := by
  simp only [child, smul_neg]
  module

theorem child_energy (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 = (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 +
      (‖v - w‖ / 2) * inner ℝ (v + w) n := by
  unfold child
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_one,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (norm_nonneg _), hn,
    real_inner_smul_left, real_inner_smul_right, mul_one, mul_pow, div_pow]
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

theorem child_pair_energy (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 + ‖child v w (-n)‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [child_energy v w n hn, child_energy v w (-n) (by simpa using hn), inner_neg_right]
  ring

theorem child_energy_le_total (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have h := child_pair_energy v w n hn
  nlinarith only [h, sq_nonneg ‖child v w (-n)‖]

/-- The radius of the squared-speed interval appearing in the uniform sphere law. -/
def energyRadius (v w : V) : ℝ := ‖v - w‖ * ‖v + w‖

theorem energyRadius_nonneg (v w : V) : 0 ≤ energyRadius v w := by
  unfold energyRadius
  positivity

theorem energyRadius_le (v w : V) : energyRadius v w ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have hpar : ‖v - w‖ ^ 2 + ‖v + w‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    ring
  have hsq := sq_nonneg (‖v - w‖ - ‖v + w‖)
  unfold energyRadius
  nlinarith only [hpar, hsq]

/-- The interval-radius formula for a unit cold partner; this is independent of its sign. -/
theorem energyRadius_sq (v e : V) (he : ‖e‖ = 1) :
    energyRadius v e ^ 2 = (‖v‖ ^ 2 + 1) ^ 2 - 4 * inner ℝ v e ^ 2 := by
  unfold energyRadius
  rw [mul_pow, norm_sub_sq_real, norm_add_sq_real, he]
  ring

theorem two_beam_distance_lower (v e : V) (he : ‖e‖ = 1) :
    2 ≤ ‖v - e‖ + ‖v + e‖ := by
  have h : ‖(v + e) - (v - e)‖ ≤ ‖v + e‖ + ‖v - e‖ := norm_sub_le _ _
  have hid : (v + e) - (v - e) = (2 : ℝ) • e := by module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), he] at h
  linarith

theorem two_beam_distance_upper (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    ‖v - e‖ + ‖v + e‖ ≤ 12 := by
  have hl := norm_sub_le v e
  have hr := norm_add_le v e
  rw [he] at hl hr
  linarith

/-- Collision frequency of a particle in the two unit-strength reference beams. -/
def frequency (v e : V) : ℝ := 2 * Real.pi * (‖v - e‖ + ‖v + e‖)

theorem frequency_lower (v e : V) (he : ‖e‖ = 1) :
    4 * Real.pi ≤ frequency v e := by
  have h := mul_le_mul_of_nonneg_left (two_beam_distance_lower v e he)
    (by positivity : 0 ≤ 2 * Real.pi)
  dsimp only [frequency]
  nlinarith only [h]

theorem frequency_upper (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    frequency v e ≤ 24 * Real.pi := by
  have h := mul_le_mul_of_nonneg_left (two_beam_distance_upper v e he hv)
    (by positivity : 0 ≤ 2 * Real.pi)
  dsimp only [frequency]
  nlinarith only [h]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Stability of the finite collision paths used in the branching block -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_neg (v w n : V) : child (-v) (-w) (-n) = -child v w n := by
  have he : -v - -w = -(v-w) := by abel
  simp only [child,he,norm_neg,← neg_add,smul_neg]

theorem child_lipschitz (v w v' w' n : V) (hn : ‖n‖ = 1) :
    ‖child v w n-child v' w' n‖ ≤ ‖v-v'‖+‖w-w'‖ := by
  have he : child v w n-child v' w' n =
      (1/2:ℝ) • ((v-v')+(w-w'))+((‖v-w‖-‖v'-w'‖)/2) • n := by
    unfold child
    module
  rw [he]
  have hsum := norm_add_le ((1/2:ℝ) • ((v-v')+(w-w')))
    (((‖v-w‖-‖v'-w'‖)/2) • n)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hn,mul_one,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2),abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hsum
  have hdiff : ‖(v-w)-(v'-w')‖ ≤ ‖v-v'‖+‖w-w'‖ := by
    calc
      _ = ‖(v-v')-(w-w')‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hrad := (abs_norm_sub_norm_le (v-w) (v'-w')).trans hdiff
  have hc := norm_add_le (v-v') (w-w')
  linarith

theorem finite_path_error {v u w z n : ℕ → V} {ε : ℝ}
    (hinit : v 0 = u 0) (hn : ∀ j, ‖n j‖ = 1)
    (hw : ∀ j, ‖w j-z j‖ ≤ ε)
    (hv : ∀ j, v (j+1) = child (v j) (w j) (n j))
    (hu : ∀ j, u (j+1) = child (u j) (z j) (n j)) :
    ∀ j, ‖v j-u j‖ ≤ (j:ℝ)*ε := by
  intro j
  induction j with
  | zero => simp [hinit]
  | succ j ih =>
    rw [hv,hu]
    calc
      _ ≤ ‖v j-u j‖+‖w j-z j‖ := child_lipschitz _ _ _ _ _ (hn j)
      _ ≤ (j:ℝ)*ε+ε := add_le_add ih (hw j)
      _ = _ := by push_cast; ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The normalized outgoing-sphere kernel for reference collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereProbability : Measure Sphere := (ENNReal.ofReal (4*Real.pi))⁻¹ • sphereArea

instance sphereProbability_isProbability : IsProbabilityMeasure sphereProbability := by
  constructor
  rw [sphereProbability,Measure.smul_apply,smul_eq_mul,sphereArea_univ]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem child_measurable : Measurable (fun z : (V × V) × Sphere =>
    child z.1.1 z.1.2 z.2.1) := by
  unfold child
  fun_prop

def outgoing : Kernel (V × V) V :=
  (Kernel.id ×ₖ Kernel.const (V × V) sphereProbability).map
    (fun z => child z.1.1 z.1.2 z.2.1)

instance outgoing_isMarkov : IsMarkovKernel outgoing :=
  Kernel.IsMarkovKernel.map _ child_measurable

theorem outgoing_apply (p : V × V) :
    outgoing p = sphereProbability.map (fun n : Sphere => child p.1 p.2 n.1) := by
  ext s hs
  rw [outgoing,Kernel.map_apply' _ child_measurable p hs,
    Kernel.id_prod_apply' _ p (child_measurable hs),Kernel.const_apply,
    Measure.map_apply (by unfold child; fun_prop) hs]
  rfl

theorem outgoing_integral {f : V → ℝ} (hf : Continuous f) (p : V × V) :
    (∫ v, f v ∂outgoing p) = ∫ n : Sphere, f (child p.1 p.2 n.1) ∂sphereProbability := by
  rw [outgoing_apply,integral_map (by unfold child; fun_prop) hf.aestronglyMeasurable]

theorem outgoing_energy_support (p : V × V) :
    outgoing p {v | ‖v‖^2 ≤ ‖p.1‖^2+‖p.2‖^2} = 1 := by
  have hm : Measurable (fun n : Sphere => child p.1 p.2 n.1) := by unfold child; fun_prop
  rw [outgoing_apply,Measure.map_apply hm (measurableSet_le (by fun_prop) measurable_const)]
  have he : (fun n : Sphere => child p.1 p.2 n.1) ⁻¹' {v | ‖v‖^2 ≤ ‖p.1‖^2+‖p.2‖^2} = univ := by
    ext n
    simp only [mem_preimage,mem_ofPred_eq,mem_univ,iff_true]
    apply child_energy_le_total
    simpa only [Metric.mem_sphere,dist_zero_right] using n.2
  rw [he,measure_univ]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two-beam reference jump law and its sign probabilities -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def plusProbability (e v : V) : ℝ := ‖v-e‖/(‖v-e‖+‖v+e‖)

theorem plusProbability_mem (e v : V) : plusProbability e v ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact div_le_one_of_le₀ (by linarith [norm_nonneg (v+e)]) (by positivity)

def plusKernel (e : V) : Kernel V V :=
  outgoing.comap (fun v => (v,e)) (measurable_id.prodMk measurable_const)

def minusKernel (e : V) : Kernel V V :=
  outgoing.comap (fun v => (v,-e)) (measurable_id.prodMk measurable_const)

instance plusKernel_isMarkov (e : V) : IsMarkovKernel (plusKernel e) := by
  unfold plusKernel
  infer_instance

instance minusKernel_isMarkov (e : V) : IsMarkovKernel (minusKernel e) := by
  unfold minusKernel
  infer_instance

def referenceJump (e : V) : Kernel V V :=
  Kernel.withDensity (plusKernel e) (fun v _ => ENNReal.ofReal (plusProbability e v))+
    Kernel.withDensity (minusKernel e) (fun v _ => ENNReal.ofReal (1-plusProbability e v))

theorem plusProbability_measurable (e : V) : Measurable (plusProbability e) := by
  unfold plusProbability
  fun_prop

instance referenceJump_isMarkov (e : V) : IsMarkovKernel (referenceJump e) := by
  constructor
  intro v
  constructor
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  change (referenceJump e v) univ = 1
  simp only [referenceJump,add_apply,Measure.add_apply,
    Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm]
  rw [withDensity_apply _ MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ,lintegral_const,measure_univ,mul_one]
  rw [← ENNReal.ofReal_add (plusProbability_mem e v).1 (sub_nonneg.mpr (plusProbability_mem e v).2)]
  simp

theorem minusProbability_eq (e v : V) (he : ‖e‖ = 1) :
    1-plusProbability e v = ‖v+e‖/(‖v-e‖+‖v+e‖) := by
  have hd : 0 < ‖v-e‖+‖v+e‖ := lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  unfold plusProbability
  field_simp
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Normalization of the reference histories retained in the velocity ball -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def referenceRegion : Set V := Metric.closedBall 0 5

theorem referenceRegion_measurable : MeasurableSet referenceRegion :=
  Metric.isClosed_closedBall.measurableSet

def retention (e v : V) : ℝ≥0∞ := referenceJump e v referenceRegion

theorem retention_measurable (e : V) : Measurable (retention e) :=
  (referenceJump e).measurable_coe referenceRegion_measurable

theorem retention_le_one (e v : V) : retention e v ≤ 1 := by
  exact prob_le_one

theorem retention_ne_top (e v : V) : retention e v ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (retention_le_one e v)

def retainedJump (e : V) : Kernel V V :=
  Kernel.withDensity ((referenceJump e).restrict referenceRegion_measurable)
    (fun v _ => (retention e v)⁻¹)

theorem retainedJump_apply (e v : V) :
    retainedJump e v = (retention e v)⁻¹ • (referenceJump e v).restrict referenceRegion := by
  rw [retainedJump,Kernel.withDensity_apply _
    (((retention_measurable e).comp measurable_fst).inv),withDensity_const,
    Kernel.restrict_apply]

theorem retainedJump_univ (e v : V) (hp : retention e v ≠ 0) :
    retainedJump e v univ = 1 := by
  rw [retainedJump_apply,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (retention_ne_top e v)

theorem retainedJump_region (e v : V) (hp : retention e v ≠ 0) :
    retainedJump e v referenceRegion = 1 := by
  rw [retainedJump_apply,Measure.smul_apply,
    Measure.restrict_apply referenceRegion_measurable]
  simp only [inter_self,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (retention_ne_top e v)

/-- Each collision rate times its conditional jump law recovers the retained branching rate. -/
theorem retainedJump_rate_identity (e v : V) (c : ℝ≥0∞) (hp : retention e v ≠ 0) :
    (c*retention e v) • retainedJump e v = c • (referenceJump e v).restrict referenceRegion := by
  rw [retainedJump_apply,smul_smul,mul_assoc,
    ENNReal.mul_inv_cancel hp (retention_ne_top e v),mul_one]

def retainedRate (e v : V) : ℝ := 2*(retention e v).toReal*frequency v e

def retainedPotential (e v : V) : ℝ := retainedRate e v-frequency v e

theorem retention_toReal_mem (e v : V) : (retention e v).toReal ∈ Icc (0:ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  exact (ENNReal.toReal_le_toReal (retention_ne_top e v) ENNReal.one_ne_top).mpr
    (retention_le_one e v)

theorem retainedRate_nonneg (e v : V) : 0 ≤ retainedRate e v := by
  unfold retainedRate frequency
  positivity

theorem retainedRate_le (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    retainedRate e v ≤ 48*Real.pi := by
  have hu := frequency_upper v e he hv
  have hp := (retention_toReal_mem e v).2
  have hν : 0 ≤ frequency v e := by unfold frequency; positivity
  have hm := mul_le_mul_of_nonneg_right hp hν
  dsimp only [retainedRate]
  nlinarith

theorem retainedPotential_ge (e v : V) (he : ‖e‖ = 1)
    (hp : (25:ℝ)/26 ≤ (retention e v).toReal) :
    48*Real.pi/13 ≤ retainedPotential e v := by
  have hν := frequency_lower v e he
  have hν0 : 0 ≤ frequency v e := by unfold frequency; positivity
  have hm := mul_le_mul_of_nonneg_right hp hν0
  dsimp only [retainedPotential,retainedRate]
  nlinarith

theorem retainedRate_measure_identity (e v : V)
    (hp : retention e v ≠ 0) :
    ENNReal.ofReal (retainedRate e v) • retainedJump e v =
      ENNReal.ofReal (2*frequency v e) • (referenceJump e v).restrict referenceRegion := by
  have hν : 0 ≤ frequency v e := by unfold frequency; positivity
  have hnonneg : 0 ≤ 2*frequency v e := by positivity
  have hr : retainedRate e v = (2*frequency v e)*(retention e v).toReal := by
    unfold retainedRate
    ring
  rw [hr,ENNReal.ofReal_mul hnonneg,ENNReal.ofReal_toReal (retention_ne_top e v)]
  exact retainedJump_rate_identity e v _ hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Every reference velocity has a robust outgoing direction of small speed -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem exists_small_child (v e : V) (he : ‖e‖ = 1) :
    ∃ n : Sphere, ‖child v e n.1‖ ≤ 1 := by
  by_cases hu : v+e = 0
  · refine ⟨⟨e,mem_sphere_zero_iff_norm.mpr he⟩,?_⟩
    have hve : v = -e := eq_neg_of_add_eq_zero_left hu
    rw [child,hu,smul_zero,zero_add,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity),he,mul_one,hve]
    have hd : -e-e = (-2 : ℝ) • e := by module
    rw [hd,norm_smul,he]
    norm_num
  · let n : Sphere := ⟨-normalize (v+e),mem_sphere_zero_iff_norm.mpr
      (by rw [norm_neg,norm_normalize hu])⟩
    refine ⟨n,?_⟩
    have hn : ‖normalize (v+e)‖ = 1 := norm_normalize hu
    have hc : child v e n.1 = ((‖v+e‖-‖v-e‖)/2) • normalize (v+e) := by
      change (1/2 : ℝ) • (v+e)+(‖v-e‖/2) • (-normalize (v+e)) = _
      nth_rw 1 [← norm_smul_normalize (v+e)]
      module
    have hd := abs_norm_sub_norm_le (v+e) (v-e)
    have heq : (v+e)-(v-e) = (2 : ℝ) • e := by module
    rw [heq,norm_smul,he] at hd
    norm_num at hd
    rw [hc,norm_smul,Real.norm_eq_abs,abs_div,hn]
    norm_num
    linarith

theorem child_angular_distance (v w n m : V) :
    dist (child v w n) (child v w m) = (‖v-w‖/2)*dist n m := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : child v w n-child v w m = (‖v-w‖/2) • (n-m) := by
    unfold child
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

theorem small_child_neighborhood (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5)
    (n : Sphere) (hn : ‖child v e n.1‖ ≤ 1) :
    ∀ m ∈ Metric.ball n (1/6 : ℝ), ‖child v e m.1‖ < 2 := by
  intro m hm
  have hdist : dist (m : V) (n : V) < 1/6 := hm
  have hrel : ‖v-e‖ ≤ 6 := (norm_sub_le v e).trans (by rw [he]; linarith)
  have hd : ‖child v e m.1‖ ≤ ‖child v e n.1‖+dist (child v e m.1) (child v e n.1) :=
    norm_le_norm_add_const_of_dist_le le_rfl
  rw [child_angular_distance] at hd
  have hm0 : 0 ≤ dist (m : V) (n : V) := dist_nonneg
  have hh := mul_le_mul_of_nonneg_right hrel hm0
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # First moments of the reference sphere law for retention bounds -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphere_inner_integrable (g : V) :
    Integrable (fun n : Sphere => inner ℝ g (n : V)) sphereProbability := by
  apply (integrable_const ‖g‖).mono'
    ((continuous_const.inner continuous_subtype_val).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun n => by
    simpa only [Real.norm_eq_abs,mem_sphere_zero_iff_norm.mp n.2,mul_one] using
      abs_real_inner_le_norm g (n : V))

theorem sphere_inner_integral (g : V) :
    (∫ n : Sphere, inner ℝ g (n : V) ∂sphereProbability) = 0 := by
  have h := sphereArea_antipodal.integral_comp (Homeomorph.neg Sphere).measurableEmbedding
    (fun n : Sphere => inner ℝ g (n : V))
  change (∫ n : Sphere, inner ℝ g ((-n : Sphere) : V) ∂sphereArea) =
    ∫ n : Sphere, inner ℝ g (n : V) ∂sphereArea at h
  simp only [coe_neg_sphere,inner_neg_right,integral_neg] at h
  have hz : (∫ n : Sphere, inner ℝ g (n : V) ∂sphereArea) = 0 := by linarith
  rw [sphereProbability,integral_smul_measure,hz,smul_zero]

theorem sphere_abs_inner_integral (g : V) :
    (∫ n : Sphere, |inner ℝ g (n : V)| ∂sphereProbability) = ‖g‖/2 := by
  rw [sphereProbability,integral_smul_measure,smul_eq_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity),integral_abs_inner_sphereArea]
  field_simp
  ring

theorem sphere_abs_inner_integrable (g : V) :
    Integrable (fun n : Sphere => |inner ℝ g (n : V)|) sphereProbability :=
  (sphere_inner_integrable g).abs

theorem sphere_positive_inner_integral (g : V) :
    (∫ n : Sphere, max (inner ℝ g (n : V)) 0 ∂sphereProbability) = ‖g‖/4 := by
  have he (x : ℝ) : max x 0 = (|x|+x)/2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx,abs_of_nonneg hx]; ring
    · rw [max_eq_right (le_of_not_ge hx),abs_of_nonpos (le_of_not_ge hx)]; ring
  simp_rw [he]
  rw [integral_div,integral_add (sphere_abs_inner_integrable g) (sphere_inner_integrable g),
    sphere_abs_inner_integral,sphere_inner_integral]
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A positive retention margin from first spherical moments

A first-moment bound retains at least `35/48` of the offspring in the
radius-five ball, giving a strictly positive branching potential.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_escape_coarse (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (outgoing (v,e)).real referenceRegionᶜ ≤ (13 : ℝ)/48 := by
  let g : V := (‖v-e‖/2) • (v+e)
  let U : Set Sphere := {n | child v e n.1 ∉ referenceRegion}
  have hU : MeasurableSet U := referenceRegion_measurable.compl.preimage
    (show Measurable (fun n : Sphere => child v e n.1) from by unfold child; fun_prop)
  have hg : ‖g‖ ≤ 13 := by
    have hrad := energyRadius_le v e
    have hv2 := (sq_le_sq₀ (norm_nonneg v) (by norm_num)).mpr hv
    rw [he] at hrad
    dsimp only [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    dsimp only [energyRadius] at hrad
    nlinarith
  have hpoint (n : Sphere) : U.indicator (fun _ => (1 : ℝ)) n ≤ max (inner ℝ g (n : V)) 0/12 := by
    by_cases hn : n ∈ U
    · rw [indicator_of_mem hn]
      have hnorm : ‖(n : V)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
      have hchild : 5 < ‖child v e n.1‖ := by
        simpa only [U,referenceRegion,mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,not_le] using hn
      have henergy := child_energy v e n.1 hnorm
      have hv2 := (sq_le_sq₀ (norm_nonneg v) (by norm_num)).mpr hv
      have hinner : inner ℝ g (n : V) = (‖v-e‖/2)*inner ℝ (v+e) (n : V) := by
        simp only [g,real_inner_smul_left]
      rw [he,← hinner] at henergy
      have hlinear : 12 < inner ℝ g (n : V) := by nlinarith
      have hmax := le_max_left (inner ℝ g (n : V)) 0
      linarith
    · rw [indicator_of_notMem hn]
      exact div_nonneg (le_max_right _ _) (by norm_num)
  have himax : Integrable (fun n : Sphere => max (inner ℝ g (n : V)) 0) sphereProbability :=
    (sphere_abs_inner_integrable g).mono'
      (((continuous_const.inner continuous_subtype_val).max continuous_const).aestronglyMeasurable)
      (ae_of_all _ (fun n => by
        rw [Real.norm_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)))
  have hineq := integral_mono ((integrable_const (1 : ℝ)).indicator hU)
    (himax.div_const 12) hpoint
  have hiU := integral_indicator_one (μ := sphereProbability) hU
  change (∫ n : Sphere, U.indicator (fun _ => (1 : ℝ)) n ∂sphereProbability) = _ at hiU
  rw [hiU,integral_div,sphere_positive_inner_integral] at hineq
  have hmeasure : (outgoing (v,e)).real referenceRegionᶜ = sphereProbability.real U := by
    rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop)
      referenceRegion_measurable.compl]
    rfl
  rw [hmeasure]
  linarith

theorem outgoing_retention_coarse (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (35 : ℝ)/48 ≤ (outgoing (v,e)).real referenceRegion := by
  have h := outgoing_escape_coarse v e he hv
  rw [measureReal_compl referenceRegion_measurable,probReal_univ] at h
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A positive branching potential from the coarse retention estimate -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_real (e v : V) (s : Set V) :
    (referenceJump e v).real s =
      plusProbability e v*(outgoing (v,e)).real s+
        (1-plusProbability e v)*(outgoing (v,-e)).real s := by
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  have heq : referenceJump e v =
      ENNReal.ofReal (plusProbability e v) • outgoing (v,e)+
        ENNReal.ofReal (1-plusProbability e v) • outgoing (v,-e) := by
    simp only [referenceJump,add_apply,Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm,
      withDensity_const]
    rfl
  rw [Measure.real,heq,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)).ne
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)).ne]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (plusProbability_mem e v).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (plusProbability_mem e v).2),Measure.real]

theorem retention_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (35 : ℝ)/48 ≤ (retention e v).toReal := by
  have hp := outgoing_retention_coarse v e he hv
  have hm := outgoing_retention_coarse v (-e) (by simpa using he) hv
  have hpl := mul_le_mul_of_nonneg_left hp (plusProbability_mem e v).1
  have hml := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr (plusProbability_mem e v).2)
  change (35 : ℝ)/48 ≤ (referenceJump e v).real referenceRegion
  rw [referenceJump_real]
  linarith

theorem retention_ne_zero_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    retention e v ≠ 0 := by
  intro hz
  have h := retention_coarse e v he hv
  rw [hz,ENNReal.toReal_zero] at h
  norm_num at h

theorem retainedPotential_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    11*Real.pi/6 ≤ retainedPotential e v := by
  have hp := retention_coarse e v he hv
  have hν := frequency_lower v e he
  have hν0 : 0 ≤ frequency v e := by unfold frequency; positivity
  have h₁ := mul_le_mul_of_nonneg_right hp hν0
  have h₂ := mul_le_mul_of_nonneg_left hν (by norm_num : (0:ℝ) ≤ 11/24)
  dsimp only [retainedPotential,retainedRate]
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform entry of the reference collision law into a small velocity ball -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def smallEntryMass : ℝ := (Measure.toSphereBallBound 3 (1/6) : ℝ)/3

theorem smallEntryMass_pos : 0 < smallEntryMass := by
  exact div_pos (by exact_mod_cast Measure.toSphereBallBound_pos 3 (1/6 : ℝ)) (by norm_num)

theorem sphere_small_ball_lower (n : Sphere) :
    smallEntryMass ≤ sphereProbability.real (Metric.ball n (1/6 : ℝ)) := by
  have hv : (volume : Measure V).real (Metric.ball 0 1) = 4/3*Real.pi := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal,Real.pi_pos.le]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have h := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    (volume : Measure V) (by norm_num : (0 : ℝ) < 1/6) n
  simp only [finrank_euclideanSpace,Fintype.card_fin,hv] at h
  change (Measure.toSphereBallBound 3 (1/6) : ℝ)*(4/3*Real.pi) ≤
    sphereArea.real (Metric.ball n (1/6 : ℝ)) at h
  rw [Measure.real,sphereProbability,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (by positivity)]
  change (Measure.toSphereBallBound 3 (1/6) : ℝ)/3 ≤
    (4*Real.pi)⁻¹*sphereArea.real (Metric.ball n (1/6 : ℝ))
  rw [inv_mul_eq_div,le_div_iff₀ (by positivity : 0 < 4*Real.pi)]
  nlinarith

theorem outgoing_small_entry (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    smallEntryMass ≤ (outgoing (v,e)).real (Metric.ball 0 2) := by
  obtain ⟨n,hn⟩ := exists_small_child v e he
  have hsub : Metric.ball n (1/6 : ℝ) ⊆
      (fun m : Sphere => child v e m.1) ⁻¹' Metric.ball 0 2 := by
    intro m hm
    simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using
      small_child_neighborhood v e he hv n hn m hm
  have h := (sphere_small_ball_lower n).trans (measureReal_mono hsub)
  rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop) measurableSet_ball]
  exact h

theorem reference_small_entry (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    smallEntryMass ≤ (referenceJump e v).real (Metric.ball 0 2) := by
  have hp := mul_le_mul_of_nonneg_left (outgoing_small_entry v e he hv)
    (plusProbability_mem e v).1
  have hm := mul_le_mul_of_nonneg_left (outgoing_small_entry v (-e) (by simpa using he) hv)
    (sub_nonneg.mpr (plusProbability_mem e v).2)
  rw [referenceJump_real]
  linarith

theorem retained_small_entry (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    smallEntryMass ≤ (retainedJump e v).real (Metric.ball 0 2) := by
  have hp0 : 0 < (retention e v).toReal :=
    ENNReal.toReal_pos (retention_ne_zero_coarse e v he hv) (retention_ne_top e v)
  have hp1 := (retention_toReal_mem e v).2
  have hsub : Metric.ball (0 : V) 2 ⊆ referenceRegion := by
    intro w hw
    rw [Metric.mem_ball,dist_zero_right] at hw
    change dist w 0 ≤ 5
    rw [dist_zero_right]
    linarith
  rw [Measure.real,retainedJump_apply,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hsub]
  change smallEntryMass ≤ (retention e v).toReal⁻¹*(referenceJump e v).real (Metric.ball 0 2)
  rw [inv_mul_eq_div]
  apply (reference_small_entry e v he hv).trans
  apply (le_div_iff₀ hp0).mpr
  exact mul_le_of_le_one_right measureReal_nonneg hp1

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # No retention loss for the small velocities used by the minorization paths -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_measure (e v : V) : referenceJump e v =
    ENNReal.ofReal (plusProbability e v) • outgoing (v,e)+
      ENNReal.ofReal (1-plusProbability e v) • outgoing (v,-e) := by
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  simp only [referenceJump,add_apply,Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm,
    withDensity_const]
  rfl

theorem outgoing_small_region (v e : V) (hv : ‖v‖ ≤ 4) (he : ‖e‖ = 1) :
    outgoing (v,e) referenceRegion = 1 := by
  have hsub : {w : V | ‖w‖^2 ≤ ‖v‖^2+‖e‖^2} ⊆ referenceRegion := by
    intro w hw
    change ‖w‖^2 ≤ ‖v‖^2+‖e‖^2 at hw
    change dist w 0 ≤ 5
    rw [dist_zero_right]
    rw [he] at hw
    nlinarith [norm_nonneg v,norm_nonneg w]
  apply le_antisymm prob_le_one
  rw [← outgoing_energy_support (v,e)]
  exact measure_mono hsub

theorem retention_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 4) : retention e v = 1 := by
  rw [retention,referenceJump_measure,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    outgoing_small_region v e hv he,outgoing_small_region v (-e) hv (by simpa using he)]
  simp only [smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (plusProbability_mem e v).1
    (sub_nonneg.mpr (plusProbability_mem e v).2)]
  simp

theorem retainedJump_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 4) :
    retainedJump e v = referenceJump e v := by
  have hr : referenceRegion ∈ ae (referenceJump e v) :=
    (mem_ae_iff_prob_eq_one referenceRegion_measurable).mpr (retention_small e v he hv)
  rw [retainedJump_apply,retention_small e v he hv,inv_one,one_smul]
  exact Measure.restrict_eq_self_of_ae_mem hr

theorem two_beam_distance_upper_small (v e : V) (hv : ‖v‖ ≤ 2) (he : ‖e‖ = 1) :
    ‖v-e‖+‖v+e‖ ≤ 6 := by
  have hm := norm_sub_le v e
  have hp := norm_add_le v e
  rw [he] at hm hp
  linarith

theorem plusProbability_lower_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v-e‖) : (1/6 : ℝ) ≤ plusProbability e v := by
  have hpos : 0 < ‖v-e‖+‖v+e‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  rw [plusProbability,le_div_iff₀ hpos]
  have hb := two_beam_distance_upper_small v e hv he
  linarith

theorem minusProbability_lower_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v+e‖) : (1/6 : ℝ) ≤ 1-plusProbability e v := by
  have hpos : 0 < ‖v-e‖+‖v+e‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  rw [minusProbability_eq e v he,le_div_iff₀ hpos]
  have hb := two_beam_distance_upper_small v e hv he
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Velocity reversal symmetry of the actual retained reference law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphereProbability_neg : sphereProbability.map (Neg.neg : Sphere → Sphere) = sphereProbability := by
  rw [sphereProbability,Measure.map_smul, sphereArea_antipodal.map_eq]
  exact measurable_neg.aemeasurable

theorem outgoing_neg (v e : V) :
    (outgoing (v,e)).map (Neg.neg : V → V) = outgoing (-v,-e) := by
  have hm (a b : V) : Measurable (fun n : Sphere => child a b n.1) := by unfold child; fun_prop
  rw [outgoing_apply,outgoing_apply,Measure.map_map measurable_neg (hm v e)]
  conv_rhs => rw [← sphereProbability_neg,Measure.map_map (hm (-v) (-e)) measurable_neg]
  congr 1
  funext n
  exact (child_neg v e n.1).symm

theorem plusProbability_neg (e v : V) (he : ‖e‖ = 1) :
    plusProbability e (-v) = 1-plusProbability e v := by
  rw [minusProbability_eq e v he,plusProbability]
  have hm : ‖-v-e‖ = ‖v+e‖ := by rw [show -v-e = -(v+e) by module,norm_neg]
  have hp : ‖-v+e‖ = ‖v-e‖ := by rw [show -v+e = -(v-e) by module,norm_neg]
  rw [hm,hp]
  congr 1
  exact add_comm _ _

theorem referenceJump_neg (e v : V) (he : ‖e‖ = 1) :
    (referenceJump e v).map (Neg.neg : V → V) = referenceJump e (-v) := by
  rw [referenceJump_measure,referenceJump_measure,Measure.map_add,Measure.map_smul,
    Measure.map_smul,outgoing_neg,outgoing_neg,neg_neg,plusProbability_neg e v he]
  · have hh : 1-(1-plusProbability e v) = plusProbability e v := by ring
    rw [hh,add_comm]
  all_goals first
    | exact (measurable_neg : Measurable (Neg.neg : V → V))
    | exact (measurable_neg : Measurable (Neg.neg : V → V)).aemeasurable

theorem referenceRegion_neg_preimage : (Neg.neg : V → V) ⁻¹' referenceRegion = referenceRegion := by
  ext v
  simp [referenceRegion,Metric.mem_closedBall,dist_zero_right]

theorem retention_neg (e v : V) (he : ‖e‖ = 1) : retention e (-v) = retention e v := by
  have h := congrArg (fun μ : Measure V => μ referenceRegion) (referenceJump_neg e v he)
  rw [Measure.map_apply measurable_neg referenceRegion_measurable,referenceRegion_neg_preimage] at h
  exact h.symm

theorem retainedJump_neg (e v : V) (he : ‖e‖ = 1) :
    (retainedJump e v).map (Neg.neg : V → V) = retainedJump e (-v) := by
  have hr : ((referenceJump e v).restrict referenceRegion).map (Neg.neg : V → V) =
      (referenceJump e (-v)).restrict referenceRegion := by
    rw [← referenceRegion_neg_preimage,← Measure.restrict_map measurable_neg referenceRegion_measurable,
      referenceJump_neg e v he,referenceRegion_neg_preimage]
  rw [retainedJump_apply,retainedJump_apply,Measure.map_smul,hr,retention_neg e v he]
  exact measurable_neg.aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Sphere probability is invariant under velocity isometries -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : Sphere ≃ᵐ Sphere where
  toFun n := ⟨e n,by simpa only [mem_sphere_zero_iff_norm,e.norm_map] using n.2⟩
  invFun n := ⟨e.symm n,by simpa only [mem_sphere_zero_iff_norm,e.symm.norm_map] using n.2⟩
  left_inv n := by apply Subtype.ext; exact e.symm_apply_apply n
  right_inv n := by apply Subtype.ext; exact e.apply_symm_apply n
  measurable_toFun := (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

theorem sphereRotation_cone (e : V ≃ₗᵢ[ℝ] V) (A : Set Sphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereRotation e) ⁻¹' A)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
  ext x
  constructor
  · rintro ⟨r,hr,n,⟨m,hm,rfl⟩,rfl⟩
    exact ⟨r,hr,e m,⟨sphereRotation e m,hm,rfl⟩,by simp⟩
  · rintro ⟨r,hr,n,⟨m,hm,rfl⟩,he⟩
    refine ⟨r,hr,e.symm m,⟨(sphereRotation e).symm m,?_,rfl⟩,?_⟩
    · change sphereRotation e ((sphereRotation e).symm m) ∈ A
      simpa using hm
    · calc
        r • e.symm (m : V) = e.symm (r • (m : V)) := by simp
        _ = x := (congrArg e.symm he).trans (e.symm_apply_apply x)

theorem sphereRotation_area (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) sphereArea sphereArea := by
  refine ⟨(sphereRotation e).measurable,Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply (sphereRotation e).measurable hA]
  rw [sphereArea,(volume : Measure V).toSphere_apply' ((sphereRotation e).measurable hA),
    (volume : Measure V).toSphere_apply' hA,sphereRotation_cone]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphereRotation_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) sphereProbability sphereProbability := by
  refine ⟨(sphereRotation e).measurable,?_⟩
  rw [sphereProbability,Measure.map_smul,(sphereRotation_area e).map_eq]
  exact (sphereRotation e).measurable.aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The incoming-velocity derivative of the reference offspring map -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_curve_derivative {u : ℝ → V} {u' : V} {t : ℝ}
    (hu : HasDerivAt u u' t) (e n : V) (hne : u t ≠ e) :
    HasDerivAt (fun s => child (u s) e n)
      ((1/2 : ℝ) • u'+(inner ℝ (u t-e) u'/(2*‖u t-e‖)) • n) t := by
  have hz : ‖u t-e‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs := ((hu.sub_const e).norm_sq).sqrt (pow_ne_zero 2 hz)
  have hn : HasDerivAt (fun s => ‖u s-e‖) (inner ℝ (u t-e) u'/‖u t-e‖) t := by
    convert hs using 1
    · funext s
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · rw [Real.sqrt_sq (norm_nonneg _)]
      field_simp
  have h := ((hu.add_const e).const_smul (1/2 : ℝ)).add ((hn.div_const 2).smul_const n)
  convert h using 1
  · rfl
  · congr 1
    congr 1
    field_simp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The transverse collision point used in the three-collision minorization -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def firstAxis : V := EuclideanSpace.single 0 1
def secondAxis : V := EuclideanSpace.single 1 1
def beamAxis : V := EuclideanSpace.single 2 1
def minorizationNormal : V := -(Real.sqrt 2)⁻¹ • (firstAxis+beamAxis)

theorem axis_norms : ‖firstAxis‖ = 1 ∧ ‖secondAxis‖ = 1 ∧ ‖beamAxis‖ = 1 := by
  simp [firstAxis,secondAxis,beamAxis,EuclideanSpace.single,PiLp.norm_single]

theorem first_beam_inner : inner ℝ firstAxis beamAxis = 0 := by
  simp [firstAxis,beamAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single]

theorem first_beam_norms : ‖firstAxis+beamAxis‖ = Real.sqrt 2 ∧
    ‖firstAxis-beamAxis‖ = Real.sqrt 2 := by
  have hp : ‖firstAxis+beamAxis‖^2 = 2 := by
    rw [norm_add_sq_real,axis_norms.1,axis_norms.2.2,first_beam_inner]
    norm_num
  have hm : ‖firstAxis-beamAxis‖^2 = 2 := by
    rw [norm_sub_sq_real,axis_norms.1,axis_norms.2.2,first_beam_inner]
    norm_num
  constructor
  · exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hp)
  · exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hm)

theorem minorizationNormal_norm : ‖minorizationNormal‖ = 1 := by
  rw [minorizationNormal,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num)),first_beam_norms.1]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

theorem minorization_child_zero : child firstAxis beamAxis minorizationNormal = 0 := by
  rw [child,first_beam_norms.2,minorizationNormal,smul_smul]
  have hs : (Real.sqrt 2/2)*(-(Real.sqrt 2)⁻¹) = -(1/2 : ℝ) := by
    field_simp
  rw [hs]
  module

theorem minorization_velocity_derivative :
    HasDerivAt (fun t : ℝ => child (firstAxis+t • beamAxis) beamAxis minorizationNormal)
      ((1/4 : ℝ) • (firstAxis+3 • beamAxis)) 0 := by
  have hu : HasDerivAt (fun t : ℝ => firstAxis+t • beamAxis) beamAxis 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const beamAxis).const_add firstAxis using 1
    simp
  have hne : firstAxis+(0 : ℝ) • beamAxis ≠ beamAxis := by
    intro h
    have hi := first_beam_inner
    simp only [zero_smul,add_zero] at h
    rw [h,real_inner_self_eq_norm_sq,axis_norms.2.2] at hi
    norm_num at hi
  have h := child_curve_derivative hu beamAxis minorizationNormal hne
  convert h using 1
  simp only [zero_smul,add_zero,inner_sub_left,first_beam_inner,
    real_inner_self_eq_norm_sq,axis_norms.2.2,one_pow,zero_sub,first_beam_norms.2]
  rw [minorizationNormal,smul_smul]
  have hs : (-1/(2*Real.sqrt 2))*(-(Real.sqrt 2)⁻¹) = (1/4 : ℝ) := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  rw [hs]
  module

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform angular caps about collision endpoints -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereCapMass (r : ℝ) : ℝ := (Measure.toSphereBallBound 3 r : ℝ)/3

theorem sphereCapMass_pos {r : ℝ} (_hr : 0 < r) : 0 < sphereCapMass r := by
  exact div_pos (by exact_mod_cast Measure.toSphereBallBound_pos 3 r) (by norm_num)

theorem sphere_cap_lower {r : ℝ} (hr : 0 < r) (n : Sphere) :
    sphereCapMass r ≤ sphereProbability.real (Metric.ball n r) := by
  have hv : (volume : Measure V).real (Metric.ball 0 1) = 4/3*Real.pi := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal,Real.pi_pos.le]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have h := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    (volume : Measure V) hr n
  simp only [finrank_euclideanSpace,Fintype.card_fin,hv] at h
  change (Measure.toSphereBallBound 3 r : ℝ)*(4/3*Real.pi) ≤ sphereArea.real (Metric.ball n r) at h
  rw [Measure.real,sphereProbability,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (by positivity)]
  change (Measure.toSphereBallBound 3 r : ℝ)/3 ≤
    (4*Real.pi)⁻¹*sphereArea.real (Metric.ball n r)
  rw [inv_mul_eq_div,le_div_iff₀ (by positivity : 0 < 4*Real.pi)]
  nlinarith

theorem child_normalized_endpoints (v e : V) :
    child v e (normalize (v-e)) = v ∧ child v e (-normalize (v-e)) = e := by
  have hh : (‖v-e‖/2) • normalize (v-e) = (1/2 : ℝ) • (v-e) := by
    calc
      _ = (1/2 : ℝ) • (‖v-e‖ • normalize (v-e)) := by rw [smul_smul]; congr 1; ring
      _ = _ := by rw [norm_smul_normalize]
  constructor
  · rw [child,hh]
    module
  · rw [child,smul_neg,hh]
    module

theorem outgoing_endpoint_cap {δ : ℝ} (hδ : 0 < δ) (v e b : V)
    (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) (n : Sphere)
    (hn : dist (child v e n.1) b ≤ δ/2) :
    sphereCapMass (δ/12) ≤ (outgoing (v,e)).real (Metric.ball b δ) := by
  have hsub : Metric.ball n (δ/12) ⊆
      (fun m : Sphere => child v e m.1) ⁻¹' Metric.ball b δ := by
    intro m hm
    have hd : dist (m : V) (n : V) < δ/12 := hm
    have hr : ‖v-e‖ ≤ 6 := (norm_sub_le v e).trans (by rw [he]; linarith)
    have ht := dist_triangle (child v e m.1) (child v e n.1) b
    rw [child_angular_distance] at ht
    have hp := mul_le_mul_of_nonneg_right hr (dist_nonneg : 0 ≤ dist (m : V) (n : V))
    change dist (child v e m.1) b < δ
    nlinarith
  have hh := (sphere_cap_lower (by positivity : 0 < δ/12) n).trans (measureReal_mono hsub)
  rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop) measurableSet_ball]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Unit-sphere curves preserve tangent derivatives under normalization -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalize_curve_derivative {f : ℝ → V} {f' : V} {t : ℝ}
    (hf : HasDerivAt f f' t) (hn : ‖f t‖ = 1) (ht : inner ℝ (f t) f' = 0) :
    HasDerivAt (fun s => NormedSpace.normalize (f s)) f' t := by
  have hnormsq := hf.norm_sq
  have hs := hnormsq.sqrt (by rw [hn]; norm_num)
  have hnorm : HasDerivAt (fun s => ‖f s‖) 0 t := by
    convert hs using 1
    · funext s
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · rw [hn,ht]
      norm_num
  have hi := hnorm.inv (by rw [hn]; norm_num)
  have h := hi.smul hf
  convert h using 1
  · rfl
  · simp [hn]

theorem normalize_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → V} {f' : E →L[ℝ] V} {x : E} (hf : HasFDerivAt f f' x)
    (hn : ‖f x‖ = 1) (ht : ∀ v, inner ℝ (f x) (f' v) = 0) :
    HasFDerivAt (fun y => NormedSpace.normalize (f y)) f' x := by
  have hs := hf.norm_sq.sqrt (by rw [hn]; norm_num)
  have hnorm : HasFDerivAt (fun y => ‖f y‖) (0 : E →L[ℝ] ℝ) x := by
    convert hs using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · ext v
      simp [ht]
  have hi := (hasDerivAt_inv (by rw [hn]; norm_num)).comp_hasFDerivAt x hnorm
  have h := hi.smul hf
  convert h using 1
  · rfl
  · ext v
    simp [hn]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Volume distortion needed for the reference collision chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lipschitz_volume_image_le {f : V → V} {s : Set V} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤ (K : ℝ≥0∞)^3 * volume s := by
  let μ : Measure V := Measure.hausdorffMeasure (Module.finrank ℝ V)
  let c := Measure.addHaarScalarFactor μ volume
  have hm : μ = c • volume := isAddLeftInvariant_eq_smul μ volume
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  have hh := hf.hausdorffMeasure_image_le
    (show 0 ≤ (Module.finrank ℝ V : ℝ) from Nat.cast_nonneg _)
  change μ (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ V : ℝ) * μ s at hh
  rw [hm] at hh
  have hd : Module.finrank ℝ V = 3 := by simp
  rw [hd,ENNReal.rpow_natCast] at hh
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul] at hh
  apply (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower volume distortion on a chart with a controlled inverse -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem antilipschitzOn_volume_image_le {f : V → V} {S T : Set V} {K : ℝ≥0}
    (hf : AntilipschitzWith K (S.domRestrict f)) (hT : T ⊆ S) :
    volume T ≤ (K : ℝ≥0∞)^3 * volume (f '' T) := by
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hf.injective (show S.domRestrict f ⟨x,hx⟩ =
      S.domRestrict f ⟨y,hy⟩ from hxy))
  have hm : MapsTo (invFunOn f S) (f '' S) S := fun _ hy => invFunOn_mem hy
  have hr : RightInvOn (invFunOn f S) f (f '' S) := fun _ hy => invFunOn_eq hy
  have hL : LipschitzOnWith K (invFunOn f S) (f '' S) := by
    intro x hx y hy
    exact (hf.to_rightInvOn' hm hr) ⟨x,hx⟩ ⟨y,hy⟩
  calc
    volume T = volume (invFunOn f S '' (f '' T)) :=
      congrArg volume (hinj.invFunOn_image hT).symm
    _ ≤ (K : ℝ≥0∞)^3 * volume (f '' T) :=
      lipschitz_volume_image_le (hL.mono (image_mono hT))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Three independent output directions at the minorization collision -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def minorizationDirections : Fin 3 → V :=
  ![(1/4 : ℝ) • (firstAxis+3 • beamAxis),
    (Real.sqrt 2/2) • secondAxis,(1/2 : ℝ) • (firstAxis-beamAxis)]

theorem minorizationDirections_independent : LinearIndependent ℝ minorizationDirections := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have h₀ := congrArg (fun v : V => v 0) hg
  have h₁ := congrArg (fun v : V => v 1) hg
  have h₂ := congrArg (fun v : V => v 2) hg
  simp [minorizationDirections,Fin.sum_univ_succ,firstAxis,secondAxis,beamAxis,
    EuclideanSpace.single] at h₀ h₁ h₂
  have hg₁ : g 1 = 0 := by
    have hp : 0 < Real.sqrt 2/2 := by positivity
    nlinarith
  norm_num at h₀ h₂
  fin_cases i <;> dsimp <;> linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
