import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Clocks

namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def scheduleVelocity {m : ℕ} (v : Fin m → Space → Space) : Field :=
  fun t x => ∑ i, scheduledPulse m i t • v i x

theorem continuous_integrableOn_cell {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : Continuous g) : IntegrableOn g fundamentalCell := by
  apply (hg.integrableOn_Icc (a := (0 : Space)) (b := fun _ => 10)).mono_set
  intro x hx
  constructor
  · intro j
    exact (hx j (Set.mem_univ j)).1
  · intro j
    exact (hx j (Set.mem_univ j)).2.le

theorem scheduleVelocity_smooth {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i)) : Smooth (scheduleVelocity v) := by
  apply ContDiff.sum
  intro i _
  exact ((scheduledPulse_contDiff i).comp contDiff_fst).smul ((hv i).comp contDiff_snd)

theorem scheduleVelocity_spatially_periodic {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i x k, v i (x + deck k) = v i x) :
    SpatiallyPeriodic (scheduleVelocity v) := by
  intro t x k
  exact Finset.sum_congr rfl (fun i _ => congrArg (scheduledPulse m i t • ·) (hv i x k))

theorem scheduleVelocity_onePeriodic {m : ℕ} (v : Fin m → Space → Space) :
    OnePeriodic (scheduleVelocity v) := by
  intro t x
  apply Finset.sum_congr rfl
  intro i _
  rw [scheduledPulse_periodic i t]

theorem scheduleVelocity_meanZero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Continuous (v i)) (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0) :
    MeanZero (scheduleVelocity v) := by
  intro t
  dsimp [scheduleVelocity]
  rw [integral_finsetSum]
  · simp only [integral_smul, hz, smul_zero, Finset.sum_const_zero]
  · intro i _
    exact (continuous_integrableOn_cell (hv i)).smul (scheduledPulse m i t)

theorem scheduleVelocity_integerCollars {m : ℕ} (v : Fin m → Space → Space) :
    IntegerCollars (scheduleVelocity v) := by
  refine ⟨1/4, by norm_num, ?_⟩
  intro n t x ht
  apply Finset.sum_eq_zero
  intro i _
  rw [scheduledPulse_integer_collar i n ht, zero_smul]

theorem scheduleVelocity_initial {m : ℕ} (v : Fin m → Space → Space) (x : Space) :
    scheduleVelocity v 0 x = 0 := by
  rcases scheduleVelocity_integerCollars v with ⟨ε, hε, h⟩
  exact h 0 0 x (by simpa using hε)

theorem scheduleVelocity_at_time {m : ℕ} (v : Fin m → Space → Space) (t : ℝ) :
    scheduleVelocity v t = 0 ∨
      ∃ i, scheduleVelocity v t = scheduledPulse m i t • v i := by
  by_cases ht : ∃ i, scheduledPulse m i t ≠ 0
  · obtain ⟨i, hi⟩ := ht
    right
    refine ⟨i, ?_⟩
    funext x
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [(scheduledPulse_disjoint hji t).resolve_right hi, zero_smul]
    · simp
  · left
    push Not at ht
    funext x
    simp [scheduleVelocity, ht]

theorem scheduleVelocity_divergence_free {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Differentiable ℝ (v i))
    (hz : ∀ i x, ∑ j : Fin 3, fderiv ℝ (v i) x (basis j) j = 0) :
    DivergenceFree (scheduleVelocity v) := by
  intro t x
  rcases scheduleVelocity_at_time v t with ht | ⟨i, hi⟩
  · simp [divergence, spatialPartial, ht]
  · dsimp [divergence, spatialPartial]
    rw [hi, fderiv_const_smul (hv i x)]
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, hz, mul_zero]

theorem scheduleVelocity_advection_zero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Differentiable ℝ (v i))
    (hz : ∀ i x, fderiv ℝ (v i) x (v i x) = 0) :
    ∀ t x, advection (scheduleVelocity v) t x = 0 := by
  intro t x
  rcases scheduleVelocity_at_time v t with ht | ⟨i, hi⟩
  · simp [advection, ht]
  · dsimp [advection]
    rw [hi, fderiv_const_smul (hv i x)]
    simp only [smul_apply, Pi.smul_apply, map_smul, hz, smul_zero]

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directional (g : E → F) (v : E) : E → F := fun x => fderiv ℝ g x v

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

theorem directional_directional {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v w x : E) :
    directional (directional g v) w x = fderiv ℝ (fderiv ℝ g) x w v := by
  change fderiv ℝ (fun y => fderiv ℝ g y v) x w = _
  rw [fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hg).2.differentiable (by simp) x)
    (differentiableAt_const v)]
  simp

theorem directional_commute {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v w : E) :
    directional (directional g v) w = directional (directional g w) v := by
  funext x
  rw [directional_directional hg, directional_directional hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq w v

theorem directional_translation {g : E → F} (hg : Differentiable ℝ g)
    {c : E} (hc : ∀ x, g (x + c) = g x) (v x : E) :
    directional g v (x + c) = directional g v x := by
  have hd := (hg (x + c)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const c)
  have he : (fun y => g (y + c)) = g := funext hc
  have hd' : HasFDerivAt g (fderiv ℝ g (x + c)) x := by simpa only [Function.comp_def, id_eq, he, ContinuousLinearMap.comp_id] using hd
  exact (congrArg (fun L : E →L[ℝ] F => L v) hd'.fderiv).symm

@[simp] theorem directional_zero (v : E) : directional (0 : E → F) v = 0 := by
  funext x
  simp [directional]

end DirectionalCalculus

def fullTimePartial (u : Field) : Field := fun t x => deriv (fun s => u s x) t

def fieldDirectional (u : Field) (v : SpaceTime) : Field :=
  fun t x => directional (Function.uncurry u) v (t, x)

theorem fieldDirectional_smooth {u : Field} (hu : Smooth u) (v : SpaceTime) :
    Smooth (fieldDirectional u v) := directional_contDiff hu v

theorem spatialPartial_eq_fieldDirectional {u : Field} (hu : Smooth u) (j : Fin 3) :
    spatialPartial u j = fieldDirectional u (0, basis j) := by
  funext t x
  have h := (hu.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have he : fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) := h.fderiv
  change fderiv ℝ (u t) x (basis j) = _
  rw [he]
  rfl

theorem fullTimePartial_eq_fieldDirectional {u : Field} (hu : Smooth u) :
    fullTimePartial u = fieldDirectional u (1, 0) := by
  funext t x
  exact ((hu.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

theorem smooth_spatialPartial {u : Field} (hu : Smooth u) (j : Fin 3) :
    Smooth (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_smooth hu _

theorem smooth_fullTimePartial {u : Field} (hu : Smooth u) : Smooth (fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hu]
  exact fieldDirectional_smooth hu _

theorem smooth_laplacian {u : Field} (hu : Smooth u) : Smooth (laplacian u) := by
  exact ContDiff.sum (fun j _ => smooth_spatialPartial (smooth_spatialPartial hu j) j)

theorem smooth_spatial_slice {u : Field} (hu : Smooth u) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (u t) := hu.comp (contDiff_const.prodMk contDiff_id)

theorem smooth_temporal_slice {u : Field} (hu : Smooth u) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => u t x) := hu.comp (contDiff_id.prodMk contDiff_const)

theorem timePartial_eq_fullTimePartial {u : Field} (hu : Smooth u)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timePartial u t x = fullTimePartial u t x :=
  ((smooth_temporal_slice hu x).differentiable (by simp) t).derivWithin
    (uniqueDiffOn_Ici 0 t ht)

def globalDirectForce (ν : ℝ) (u : Field) : Field :=
  fun t x => fullTimePartial u t x - ν • laplacian u t x

theorem globalDirectForce_eq_directForce {u : Field} (hu : Smooth u)
    (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    globalDirectForce ν u t x = directForce ν u t x := by
  simp only [globalDirectForce, directForce, timePartial_eq_fullTimePartial hu ht x]

theorem globalDirectForce_smooth {u : Field} (hu : Smooth u) (ν : ℝ) :
    Smooth (globalDirectForce ν u) :=
  (smooth_fullTimePartial hu).sub ((contDiff_const (c := ν)).smul (smooth_laplacian hu))

theorem fieldDirectional_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (v : SpaceTime) : SpatiallyPeriodic (fieldDirectional u v) := by
  intro t x k
  unfold fieldDirectional
  have he : ((t, x + deck k) : SpaceTime) = (t, x) + (0, deck k) := by simp
  rw [he]
  exact directional_translation (g := Function.uncurry u) (hu.differentiable (by simp))
    (c := (0, deck k)) (fun z => by simpa [Function.uncurry] using hp z.1 z.2 k) v (t, x)

theorem fieldDirectional_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (v : SpaceTime) : OnePeriodic (fieldDirectional u v) := by
  intro t x
  unfold fieldDirectional
  have he : ((t + 1, x) : SpaceTime) = (t, x) + (1, 0) := by simp
  rw [he]
  exact directional_translation (g := Function.uncurry u) (hu.differentiable (by simp))
    (c := (1, 0)) (fun z => by simpa [Function.uncurry] using hp z.1 z.2) v (t, x)

theorem spatialPartial_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (j : Fin 3) : SpatiallyPeriodic (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_spatially_periodic hu hp _

theorem spatialPartial_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (j : Fin 3) : OnePeriodic (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_onePeriodic hu hp _

theorem globalDirectForce_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (ν : ℝ) : SpatiallyPeriodic (globalDirectForce ν u) := by
  have ht : SpatiallyPeriodic (fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_spatially_periodic hu hp _
  have hl : SpatiallyPeriodic (laplacian u) := by
    intro t x k
    exact Finset.sum_congr rfl (fun j _ =>
      spatialPartial_spatially_periodic (smooth_spatialPartial hu j)
        (spatialPartial_spatially_periodic hu hp j) j t x k)
  intro t x k
  simp only [globalDirectForce, ht t x k, hl t x k]

theorem globalDirectForce_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (ν : ℝ) : OnePeriodic (globalDirectForce ν u) := by
  have ht : OnePeriodic (fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_onePeriodic hu hp _
  have hl : OnePeriodic (laplacian u) := by
    intro t x
    exact Finset.sum_congr rfl (fun j _ =>
      spatialPartial_onePeriodic (smooth_spatialPartial hu j)
        (spatialPartial_onePeriodic hu hp j) j t x)
  intro t x
  simp only [globalDirectForce, ht t x, hl t x]

theorem globalDirectForce_classicalSolution {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (hdiv : DivergenceFree u)
    (hzero : ∀ x, u 0 x = 0) (hadv : ∀ t x, advection u t x = 0) (ν : ℝ) :
    ClassicalSolution ν (globalDirectForce ν u) u (0 : Pressure) where
  spatial_periodic_u := hp
  spatial_periodic_p := by intro t x k; rfl
  continuous_u := fun _ _ => hu.continuous.continuousOn
  differentiable_t := fun t _ x =>
    ((smooth_temporal_slice hu x).differentiable (by simp) t).differentiableWithinAt
  continuous_t := by
    intro T _
    apply (smooth_fullTimePartial hu).continuous.continuousOn.congr
    intro z hz
    exact timePartial_eq_fullTimePartial hu hz.1.1 z.2
  differentiable_x := fun t _ => (smooth_spatial_slice hu t).differentiable (by simp)
  continuous_x := fun _ _ j => (smooth_spatialPartial hu j).continuous.continuousOn
  differentiable_xx := fun t _ j =>
    (smooth_spatial_slice (smooth_spatialPartial hu j) t).differentiable (by simp)
  continuous_xx := fun _ _ i j =>
    (smooth_spatialPartial (smooth_spatialPartial hu i) j).continuous.continuousOn
  continuous_p := fun _ _ => continuous_const.continuousOn
  differentiable_p := fun _ _ => differentiable_const _
  continuous_px := by
    intro T _
    simp only [gradient_zero]
    exact continuous_const.continuousOn
  pressure_mean_zero := by intro t _; simp
  incompressible := fun t _ x => hdiv t x
  initial := hzero
  equation := by
    intro t ht x
    rw [globalDirectForce_eq_directForce hu ν ht]
    exact directForce_equation ν u hadv t x

end Solenoidal
end

end OAI
