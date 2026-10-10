import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Differential

namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem mixedDerivative_contDiff {u : Field} (hu : Smooth u) (α : List (Fin 4)) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDerivative u α) := by
  induction α with
  | nil => exact hu
  | cons j α ih => exact directional_contDiff ih (spacetimeBasis j)

theorem mixedDerivative_translation {u : Field} (hu : Smooth u)
    (c : SpaceTime) (hc : ∀ z : SpaceTime, u (z + c).1 (z + c).2 = u z.1 z.2)
    (α : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u α (z + c) = mixedDerivative u α z := by
  induction α generalizing z with
  | nil => exact hc z
  | cons j α ih =>
    exact directional_translation ((mixedDerivative_contDiff hu α).differentiable (by simp))
      ih (spacetimeBasis j) z

theorem mixedDerivative_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (α : List (Fin 4)) :
    SpatiallyPeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x k
  have h := mixedDerivative_translation hu (0, deck k)
    (fun z => by simpa using hp z.1 z.2 k) α (t, x)
  simpa using h

theorem mixedDerivative_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (α : List (Fin 4)) :
    OnePeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x
  have h := mixedDerivative_translation hu (1, 0)
    (fun z => by simpa using hp z.1 z.2) α (t, x)
  simpa using h

def wrapSpace (x : Space) : Space := fun j => 10 * Int.fract (x j / 10)

theorem wrapSpace_mem (x : Space) : wrapSpace x ∈ Set.Icc 0 (fun _ => 10) := by
  constructor <;> intro j
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  · have := Int.fract_lt_one (x j / 10)
    change 10 * Int.fract (x j / 10) ≤ 10
    linarith

theorem wrapSpace_add_deck (x : Space) :
    wrapSpace x + deck (fun j => ⌊x j / 10⌋) = x := by
  ext j
  simp only [Pi.add_apply, wrapSpace, deck, Int.fract]
  ring

theorem periodic_field_reduction {u : Field} (hspace : SpatiallyPeriodic u)
    (htime : OnePeriodic u) (t : ℝ) (x : Space) :
    u t x = u (Int.fract t) (wrapSpace x) := by
  calc
    u t x = u t (wrapSpace x) := by
      conv_lhs => rw [← wrapSpace_add_deck x]
      exact hspace t (wrapSpace x) _
    _ = u (Int.fract t) (wrapSpace x) := by
      have hp : Function.Periodic (fun s => u s (wrapSpace x)) 1 :=
        fun s => htime s (wrapSpace x)
      have h := hp.int_mul ⌊t⌋ (Int.fract t)
      simpa only [mul_one, Int.fract_add_floor] using h

theorem periodic_continuous_bounded {u : Field}
    (hu : Continuous (fun z : SpaceTime => u z.1 z.2))
    (hspace : SpatiallyPeriodic u) (htime : OnePeriodic u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x, ‖u t x‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : SpaceTime))
    (b := (1, fun _ => 10))).exists_bound_of_continuousOn hu.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t x => ?_⟩
  rw [periodic_field_reduction hspace htime]
  apply (hC (Int.fract t, wrapSpace x) ?_).trans (le_max_left _ _)
  exact ⟨⟨Int.fract_nonneg t, (wrapSpace_mem x).1⟩,
    ⟨(Int.fract_lt_one t).le, (wrapSpace_mem x).2⟩⟩

theorem periodic_smooth_mixed_bounded {u : Field} (hu : Smooth u)
    (hspace : SpatiallyPeriodic u) (htime : OnePeriodic u) (α : List (Fin 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := periodic_continuous_bounded
    (u := fun t x => mixedDerivative u α (t, x))
    (mixedDerivative_contDiff hu α).continuous
    (mixedDerivative_spatially_periodic hu hspace α)
    (mixedDerivative_onePeriodic hu htime α)
  exact ⟨B, hB, fun z => hbound z.1 z.2⟩

theorem fieldDirectional_commute {u : Field} (hu : Smooth u) (v w : SpaceTime) :
    fieldDirectional (fieldDirectional u v) w =
      fieldDirectional (fieldDirectional u w) v := by
  have h := directional_commute (g := Function.uncurry u) hu v w
  funext t x
  exact congrFun h (t, x)

theorem directional_component {g : SpaceTime → Space} (hg : Differentiable ℝ g)
    (v z : SpaceTime) (j : Fin 3) :
    directional (fun y => g y j) v z = directional g v z j := by
  dsimp [directional]
  rw [fderiv_apply (hg z) j]
  rfl

theorem divergence_fieldDirectional {u : Field} (hu : Smooth u)
    (v : SpaceTime) (t : ℝ) (x : Space) :
    divergence (fieldDirectional u v) t x =
      directional (fun z : SpaceTime => divergence u z.1 z.2) v (t, x) := by
  have hg (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : SpaceTime => spatialPartial u j z.1 z.2 j) :=
    (contDiff_apply ℝ ℝ j).comp (smooth_spatialPartial hu j)
  change (∑ j, spatialPartial (fieldDirectional u v) j t x j) =
    fderiv ℝ (fun z : SpaceTime => ∑ j, spatialPartial u j z.1 z.2 j) (t, x) v
  rw [fderiv_fun_sum (fun j _ => (hg j).differentiable (by simp) (t, x))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [spatialPartial_eq_fieldDirectional (fieldDirectional_smooth hu v) j,
    fieldDirectional_commute hu v (0, basis j)]
  have he := directional_component
    ((smooth_spatialPartial hu j).differentiable (by simp)) v (t, x) j
  rw [spatialPartial_eq_fieldDirectional hu j] at he ⊢
  exact he.symm

theorem fieldDirectional_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (v : SpaceTime) : DivergenceFree (fieldDirectional u v) := by
  intro t x
  rw [divergence_fieldDirectional hu]
  have hz : (fun z : SpaceTime => divergence u z.1 z.2) = 0 :=
    funext (fun z => hdiv z.1 z.2)
  rw [hz, directional_zero]
  rfl

theorem spatialPartial_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (j : Fin 3) : DivergenceFree (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu]
  exact fieldDirectional_divergence_free hu hdiv _

theorem fullTimePartial_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) : DivergenceFree (fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hu]
  exact fieldDirectional_divergence_free hu hdiv _

theorem divergence_sub {u v : Field} (hu : Smooth u) (hv : Smooth v) (t : ℝ) (x : Space) :
    divergence (u - v) t x = divergence u t x - divergence v t x := by
  change (∑ j, fderiv ℝ (u t - v t) x (basis j) j) = _
  rw [fderiv_sub ((smooth_spatial_slice hu t).differentiable (by simp) x)
    ((smooth_spatial_slice hv t).differentiable (by simp) x)]
  simp only [sub_apply, Pi.sub_apply, Finset.sum_sub_distrib]
  rfl

theorem divergence_smul {u : Field} (hu : Smooth u) (c t : ℝ) (x : Space) :
    divergence (c • u) t x = c * divergence u t x := by
  change (∑ j, fderiv ℝ (c • u t) x (basis j) j) = _
  rw [fderiv_const_smul ((smooth_spatial_slice hu t).differentiable (by simp) x) c]
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rfl

theorem divergence_sum {ι : Type*} [Fintype ι] (u : ι → Field)
    (hu : ∀ i, Smooth (u i)) (t : ℝ) (x : Space) :
    divergence (∑ i, u i) t x = ∑ i, divergence (u i) t x := by
  have hsum : (∑ i, u i) t = ∑ i, u i t := by simp
  unfold divergence spatialPartial
  rw [hsum, fderiv_sum (fun i _ => (smooth_spatial_slice (hu i) t).differentiable (by simp) x)]
  simp only [sum_apply, Finset.sum_apply]
  exact Finset.sum_comm

theorem laplacian_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) : DivergenceFree (laplacian u) := by
  intro t x
  have hL : laplacian u = ∑ j, spatialPartial (spatialPartial u j) j := by
    funext t x
    simp [laplacian]
  rw [hL, divergence_sum _ (fun j => smooth_spatialPartial (smooth_spatialPartial hu j) j)]
  apply Finset.sum_eq_zero
  intro j _
  exact spatialPartial_divergence_free (smooth_spatialPartial hu j)
    (spatialPartial_divergence_free hu hdiv j) j t x

theorem globalDirectForce_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (ν : ℝ) : DivergenceFree (globalDirectForce ν u) := by
  intro t x
  change divergence (fullTimePartial u - ν • laplacian u) t x = 0
  have hv : Smooth (ν • laplacian u) :=
    (contDiff_const (c := ν)).smul (smooth_laplacian hu)
  rw [divergence_sub (smooth_fullTimePartial hu) hv,
    divergence_smul (smooth_laplacian hu),
    fullTimePartial_divergence_free hu hdiv t x, laplacian_divergence_free hu hdiv t x]
  simp

theorem cell_ae_eq_Icc : fundamentalCell =ᵐ[volume] Set.Icc (0 : Space) (fun _ => 10) :=
  Measure.univ_pi_Ico_ae_eq_Icc

theorem face_front_eq_back_deck (j : Fin 3) (y : Fin 2 → ℝ) :
    j.insertNth (10 : ℝ) y = j.insertNth 0 y + deck (Pi.single j 1) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp [deck]
  · simp [deck]

theorem periodic_integral_divergence_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Fin 3 → Space → E)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j x k, g j (x + deck k) = g j x) :
    (∫ x in fundamentalCell, ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) = 0 := by
  rw [setIntegral_congr_set cell_ae_eq_Icc]
  have hder : Continuous (fun x : Space => ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) :=
    (ContDiff.sum (fun j _ => directional_contDiff (hg j) (basis j))).continuous
  simp only [basis] at *
  rw [integral_divergence_of_hasFDerivAt_off_countable' (0 : Space) (fun _ => 10)
    (fun _ => by norm_num) g (fun j => fderiv ℝ (g j)) ∅ Set.countable_empty
    (fun j => (hg j).continuous.continuousOn)
    (fun x _ j => (hg j).differentiable (by simp) x |>.hasFDerivAt)
    hder.integrableOn_Icc]
  apply Finset.sum_eq_zero
  intro j _
  have he : (fun y : Fin 2 → ℝ => g j (j.insertNth 10 y)) =
      (fun y : Fin 2 → ℝ => g j (j.insertNth 0 y)) := by
    funext y
    rw [face_front_eq_back_deck]
    exact hp j _ _
  change (∫ y in Set.Icc _ _, g j (j.insertNth 10 y)) -
    (∫ y in Set.Icc _ _, g j (j.insertNth 0 y)) = 0
  rw [he, sub_self]

theorem periodic_integral_partial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : ∀ x k, g (x + deck k) = g x) (j : Fin 3) :
    (∫ x in fundamentalCell, fderiv ℝ g x (basis j)) = 0 := by
  classical
  have h := periodic_integral_divergence_zero (fun k => if k = j then g else 0)
    (fun k => by split_ifs <;> first | exact hg | exact contDiff_const)
    (fun k x l => by split_ifs <;> first | exact hp x l | rfl)
  have he (k : Fin 3) (x : Space) :
      fderiv ℝ (if k = j then g else 0) x (basis k) =
        if k = j then fderiv ℝ g x (basis j) else 0 := by
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem spatialPartial_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (j : Fin 3) : MeanZero (spatialPartial u j) := by
  intro t
  exact periodic_integral_partial_zero (smooth_spatial_slice hu t) (hp t) j

theorem meanZero_sum {ι : Type*} [Fintype ι] (u : ι → Field)
    (hu : ∀ i, Smooth (u i)) (hz : ∀ i, MeanZero (u i)) : MeanZero (∑ i, u i) := by
  intro t
  simp only [Finset.sum_apply]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    continuous_integrableOn_cell (smooth_spatial_slice (hu i) t).continuous)]
  exact Finset.sum_eq_zero (fun i _ => hz i t)

theorem laplacian_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) : MeanZero (laplacian u) := by
  have hL : laplacian u = ∑ j, spatialPartial (spatialPartial u j) j := by
    funext t x
    simp [laplacian]
  rw [hL]
  exact meanZero_sum _ (fun j => smooth_spatialPartial (smooth_spatialPartial hu j) j)
    (fun j => spatialPartial_mean_zero (smooth_spatialPartial hu j)
      (spatialPartial_spatially_periodic hu hp j) j)

theorem scheduleVelocity_fullTimePartial {m : ℕ} (v : Fin m → Space → Space)
    (t : ℝ) (x : Space) :
    fullTimePartial (scheduleVelocity v) t x = ∑ i, deriv (scheduledPulse m i) t • v i x := by
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((scheduledPulse_contDiff i).differentiable (by simp) t).hasDerivAt.smul_const
      (v i x)))).deriv

theorem scheduleVelocity_fullTimePartial_mean_zero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Continuous (v i)) (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0) :
    MeanZero (fullTimePartial (scheduleVelocity v)) := by
  intro t
  simp_rw [scheduleVelocity_fullTimePartial]
  rw [integral_finsetSum Finset.univ
    (f := fun i x => deriv (scheduledPulse m i) t • v i x) (fun i _ =>
    (continuous_integrableOn_cell (hv i)).smul (deriv (scheduledPulse m i) t))]
  simp only [integral_smul, hz, smul_zero, Finset.sum_const_zero]

theorem globalDirectForce_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (ht : MeanZero (fullTimePartial u)) (ν : ℝ) :
    MeanZero (globalDirectForce ν u) := by
  intro t
  change (∫ x in fundamentalCell, fullTimePartial u t x - ν • laplacian u t x) = 0
  rw [integral_sub (f := fullTimePartial u t) (g := fun x => ν • laplacian u t x)
    (continuous_integrableOn_cell (smooth_spatial_slice (smooth_fullTimePartial hu) t).continuous)
    ((continuous_integrableOn_cell (smooth_spatial_slice (smooth_laplacian hu) t).continuous).smul ν),
    ht t, integral_smul, laplacian_mean_zero hu hp t]
  simp

theorem scheduled_direct_forcing {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i))
    (hp : ∀ i x k, v i (x + deck k) = v i x)
    (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0)
    (hdiv : ∀ i, DivergenceFree (fun _ => v i))
    (hadv : ∀ i x, fderiv ℝ (v i) x (v i x) = 0) (ν : ℝ) :
    let u := scheduleVelocity v
    let f := globalDirectForce ν u
    SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧ Smooth f ∧ Smooth u ∧
    MeanZero f ∧ MeanZero u ∧ DivergenceFree f ∧ DivergenceFree u ∧
    OnePeriodic f ∧ OnePeriodic u ∧
    ClassicalSolution ν f u (0 : Pressure) ∧ IntegerCollars u ∧
    (∀ t x, advection u t x = 0) ∧
    (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative f α z‖ ≤ B) ∧
    (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative u α z‖ ≤ B) := by
  dsimp only
  have hs := scheduleVelocity_smooth v hv
  have hsp := scheduleVelocity_spatially_periodic v hp
  have htp := scheduleVelocity_onePeriodic v
  have hd := scheduleVelocity_divergence_free v (fun i => (hv i).differentiable (by simp)) (fun i x => hdiv i 0 x)
  have ha := scheduleVelocity_advection_zero v (fun i => (hv i).differentiable (by simp)) hadv
  have hfs := globalDirectForce_smooth hs ν
  have hfsp := globalDirectForce_spatially_periodic hs hsp ν
  have hftp := globalDirectForce_onePeriodic hs htp ν
  refine ⟨hfsp, hsp, hfs, hs, ?_, ?_, ?_, hd, hftp, htp, ?_,
    scheduleVelocity_integerCollars v, ha, ?_, ?_⟩
  · exact globalDirectForce_mean_zero hs hsp
      (scheduleVelocity_fullTimePartial_mean_zero v (fun i => (hv i).continuous) hz) ν
  · exact scheduleVelocity_meanZero v (fun i => (hv i).continuous) hz
  · exact globalDirectForce_divergence_free hs hd ν
  · exact globalDirectForce_classicalSolution hs hsp hd (scheduleVelocity_initial v) ha ν
  · exact periodic_smooth_mixed_bounded hfs hfsp hftp
  · exact periodic_smooth_mixed_bounded hs hsp htp

end Solenoidal
end
end

end OAI
