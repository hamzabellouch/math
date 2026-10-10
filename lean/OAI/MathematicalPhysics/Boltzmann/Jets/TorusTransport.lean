import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusChart
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

section

/-! # Free transport and its measure-preserving characteristic coordinates on the torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def flight (t : ℝ) (p : Phase) : Phase := (p.1+torusProjection (t • p.2),p.2)

theorem continuous_flight : Continuous (fun z : ℝ × Phase => flight z.1 z.2) := by
  unfold flight torusProjection
  fun_prop

theorem measurable_flight : Measurable (fun z : ℝ × Phase => flight z.1 z.2) :=
  continuous_flight.measurable

theorem flight_add (t s : ℝ) (p : Phase) : flight t (flight s p) = flight (t+s) p := by
  apply Prod.ext
  · funext i
    change (p.1 i+(s*p.2 i : ℝ))+(t*p.2 i : ℝ) = p.1 i+((t+s)*p.2 i : ℝ)
    rw [add_mul,AddCircle.coe_add]
    abel
  · rfl

@[simp] theorem flight_zero (p : Phase) : flight 0 p = p := by
  apply Prod.ext
  · funext i
    simp [flight,torusProjection]
  · rfl

@[simp] theorem flight_neg (t : ℝ) (p : Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add,neg_add_cancel,flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add,add_neg_cancel,flight_zero]

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (flight t) (volume : Measure Phase) volume := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : Position) =>
      x+torusProjection (t • v))) := by
    unfold Function.uncurry torusProjection
    fun_prop
  have hskew := (MeasurePreserving.id (volume : Measure Velocity)).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right (volume : Measure Position)
      (torusProjection (t • v))).map_eq))
  have he : flight t = Prod.swap ∘ (fun z : Velocity × Position =>
      (z.1,z.2+torusProjection (t • z.1))) ∘ Prod.swap := rfl
  rw [he,Measure.volume_eq_prod]
  exact (Measure.measurePreserving_swap (μ := (volume : Measure Velocity)) (ν := volume)).comp
    (hskew.comp Measure.measurePreserving_swap)

def along (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ := F (z.1,flight z.1 z.2)

theorem along_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight z.1 z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight t p) measurable_flight
    (ae_of_all _ (fun t => (flight_measurePreserving t).map_eq))

theorem back_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight (-z.1) z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight (-t) p)
    (measurable_flight.comp ((measurable_fst.neg).prodMk measurable_snd))
    (ae_of_all _ (fun t => (flight_measurePreserving (-t)).map_eq))

theorem weak_along {μ : Measure ℝ} [SFinite μ] {F : ℕ → ℝ × Phase → ℝ} {g : ℝ × Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) (h : Published.WeakL1Converges (μ.prod volume) F g) :
    Published.WeakL1Converges (μ.prod volume) (fun n => along (F n)) (along g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (back_measurePreserving μ)
    (fun n => (hF n).comp (along_measurePreserving μ).measurable)
    (h.1.comp (along_measurePreserving μ).measurable)
  simpa only [along,Function.comp_def,neg_flight] using h

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Strong L¹ continuity of free transport on the physical torus -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

local instance : (volume : Measure Phase).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

def continuousFlight (t : ℝ) : C(Phase,Phase) :=
  ⟨flight t,continuous_flight.comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_continuousFlight : Continuous continuousFlight :=
  ContinuousMap.continuous_of_continuous_uncurry continuousFlight continuous_flight

theorem tendsto_flight_L1 {f : Phase → ℝ} (hf : Integrable f) (t : ℝ) :
    Tendsto (fun s => eLpNorm (fun p => f (flight s p)-f (flight t p)) 1 volume)
      (𝓝 t) (𝓝 0) := by
  let hf₁ := memLp_one_iff_integrable.mpr hf
  let u : Lp ℝ 1 (volume : Measure Phase) := hf₁.toLp f
  have hu : u =ᵐ[volume] f := hf₁.coeFn_toLp
  have hc : Continuous (fun s => Lp.compMeasurePreserving (continuousFlight s)
      (flight_measurePreserving s) u) :=
    continuous_const.compMeasurePreservingLp continuous_continuousFlight flight_measurePreserving (by norm_num)
  have hrep s : Lp.compMeasurePreserving (continuousFlight s) (flight_measurePreserving s) u =ᵐ[volume]
      (fun p => f (flight s p)) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (flight_measurePreserving s),
      (flight_measurePreserving s).quasiMeasurePreserving.ae hu] with p hp hpu
    exact hp.trans hpu
  have he s : edist (Lp.compMeasurePreserving (continuousFlight s) (flight_measurePreserving s) u)
      (Lp.compMeasurePreserving (continuousFlight t) (flight_measurePreserving t) u) =
      eLpNorm (fun p => f (flight s p)-f (flight t p)) 1 volume := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hrep s).sub (hrep t))
  have ht := tendsto_iff_edist_tendsto_0.mp (hc.tendsto t)
  simpa only [he] using ht

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Integrals in characteristic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def flightEquiv (t : ℝ) : Phase ≃ᵐ Phase where
  toFun := flight t
  invFun := flight (-t)
  left_inv := flight_neg t
  right_inv := neg_flight t
  measurable_toFun := measurable_flight.comp (measurable_const.prodMk measurable_id)
  measurable_invFun := measurable_flight.comp (measurable_const.prodMk measurable_id)

theorem integral_flight (f : Phase → ℝ) (t : ℝ) :
    (∫ p, f (flight t p)) = ∫ p, f p :=
  (flight_measurePreserving t).integral_comp (flightEquiv t).measurableEmbedding f

end BoltzmannNonuniqueness.TorusFlight

namespace BoltzmannNonuniqueness.Published

theorem integral_timePrimitive {μ : Measure ℝ} [SFinite μ]
    {R : ℝ × Phase → ℝ} (hRi : Integrable R (μ.prod volume))
    (t : ℝ) :
    (∫ p, timePrimitive μ R (t,p)) = ∫ s, if s ≤ t then ∫ p, R (s,p) else 0 ∂μ := by
  have hi : Integrable (fun z : ℝ × Phase => if z.1 ≤ t then R z else 0) (μ.prod volume) :=
    hRi.indicator (measurableSet_le measurable_fst measurable_const)
  have hs := integral_integral_swap (f := fun s p => if s ≤ t then R (s,p) else 0) hi
  change (∫ p, ∫ s, (if s ≤ t then R (s,p) else 0) ∂μ) = _
  rw [← hs]
  apply integral_congr_ae
  filter_upwards [] with s
  split_ifs <;> simp_all

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Integrating the periodic free-characteristic change of variables -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness

namespace TorusFlight

theorem integral_along {μ : Measure ℝ} [SFinite μ] {f : ℝ × Phase → ℝ}
    (hi : Integrable f (μ.prod volume)) :
    (∫ z, along f z ∂μ.prod volume) = ∫ z, f z ∂μ.prod volume := by
  have hai : Integrable (along f) (μ.prod volume) :=
    (along_measurePreserving μ).integrable_comp_of_integrable hi
  rw [integral_prod _ hai,integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => integral_flight (fun p => f (t,p)) t)

end TorusFlight

end BoltzmannNonuniqueness

end

end

section

/-! # The derivatives of periodic tests along physical free transport -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem centered_characteristic_projection (p : Phase) (t s : ℝ) :
    torusProjection (torusRepresentative (TorusFlight.flight t p).1+(s-t) • p.2) =
      (TorusFlight.flight s p).1 := by
  funext i
  have hr := congrFun (torusProjection_representative (TorusFlight.flight t p).1) i
  change ((torusRepresentative (TorusFlight.flight t p).1) i : AddCircle (1:ℝ)) =
    p.1 i+(t*p.2 i : ℝ) at hr
  change (((torusRepresentative (TorusFlight.flight t p).1) i+(s-t)*p.2 i : ℝ) : AddCircle (1:ℝ)) =
    p.1 i+(s*p.2 i : ℝ)
  rw [AddCircle.coe_add,hr,add_assoc,← AddCircle.coe_add]
  congr 2
  ring

theorem KineticTest.hasDerivAt_along (φ : KineticTest) (p : Phase) (t : ℝ) :
    HasDerivAt (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2)
      (φ.transportDerivative t (TorusFlight.flight t p)) t := by
  let x := torusRepresentative (TorusFlight.flight t p).1
  let L : ℝ → LiftedSpaceTimePhase := fun s => (s,(x+(s-t) • p.2,p.2))
  have hx : HasDerivAt (fun s => x+(s-t) • p.2) p.2 t := by
    simpa using (((hasDerivAt_id t).sub_const t).smul_const p.2).const_add x
  have hL : HasDerivAt L (1,p.2,0) t :=
    (hasDerivAt_id t).prodMk (hx.prodMk (hasDerivAt_const t p.2))
  have h := ((φ.regular.differentiable (by simp)) (L t)).hasFDerivAt.comp_hasDerivAt t hL
  have he : (fun s => φ.toFun (L s).1 (torusProjection (L s).2.1) (L s).2.2) =
      (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2) := by
    funext s
    exact congrArg (fun y => φ.toFun s y p.2) (centered_characteristic_projection p t s)
  dsimp only [Function.comp_def] at h
  rw [he] at h
  simpa only [L,x,sub_self,zero_smul,add_zero,KineticTest.transportDerivative,TorusFlight.flight] using h

theorem MassTest.hasDerivAt_along (φ : MassTest) (p : Phase) (t : ℝ) :
    HasDerivAt (fun s => φ.toFun s (TorusFlight.flight s p).1)
      (φ.transportDerivative t (TorusFlight.flight t p)) t := by
  let x := torusRepresentative (TorusFlight.flight t p).1
  let L : ℝ → ℝ × Velocity := fun s => (s,x+(s-t) • p.2)
  have hx : HasDerivAt (fun s => x+(s-t) • p.2) p.2 t := by
    simpa using (((hasDerivAt_id t).sub_const t).smul_const p.2).const_add x
  have hL : HasDerivAt L (1,p.2) t := (hasDerivAt_id t).prodMk hx
  have h := ((φ.regular.differentiable (by simp)) (L t)).hasFDerivAt.comp_hasDerivAt t hL
  have he : (fun s => φ.toFun (L s).1 (torusProjection (L s).2)) =
      (fun s => φ.toFun s (TorusFlight.flight s p).1) := by
    funext s
    exact congrArg (φ.toFun s) (centered_characteristic_projection p t s)
  dsimp only [Function.comp_def] at h
  rw [he] at h
  simpa only [L,x,sub_self,zero_smul,add_zero,MassTest.transportDerivative,TorusFlight.flight] using h

end BoltzmannNonuniqueness

end

end

section

/-! # Time-translated periodic tests for pasting a global continuation -/

noncomputable section

namespace BoltzmannNonuniqueness

private theorem time_shift_support {R τ t : ℝ} (h : R+|τ| < |t|) : R < |t+τ| := by
  have ht : |t| ≤ |t+τ|+|τ| := by
    calc
      _ = |(t+τ)+(-τ)| := by congr 1; ring
      _ ≤ |t+τ|+|-τ| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith

def KineticTest.timeShift (φ : KineticTest) (τ : ℝ) : KineticTest where
  toFun t x v := φ.toFun (t+τ) x v
  regular := φ.regular.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun z : LiftedSpaceTimePhase => (z.1+τ,z.2)) from by fun_prop)
  compact_time_velocity := by
    obtain ⟨R,hR,hzero⟩ := φ.compact_time_velocity
    refine ⟨R+|τ|,by positivity,?_⟩
    intro t x v ht
    apply hzero
    rcases ht with ht | hv
    · exact Or.inl (time_shift_support ht)
    · exact Or.inr (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg τ)) hv)

@[simp] theorem KineticTest.timeShift_toFun (φ : KineticTest) (τ t : ℝ) (x : Position) (v : Velocity) :
    (φ.timeShift τ).toFun t x v = φ.toFun (t+τ) x v := rfl

theorem KineticTest.timeShift_transportDerivative (φ : KineticTest) (τ t : ℝ) (p : Phase) :
    (φ.timeShift τ).transportDerivative t p = φ.transportDerivative (t+τ) p := by
  let L : LiftedSpaceTimePhase → ℝ := fun z => φ.toFun z.1 (torusProjection z.2.1) z.2.2
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := L)
    (x := (t,torusRepresentative p.1,p.2)) (τ,0,0)
  have he : (fun z : LiftedSpaceTimePhase => L (z+(τ,0,0))) =
      (fun z => (φ.timeShift τ).toFun z.1 (torusProjection z.2.1) z.2.2) := by
    funext z
    simp only [L,timeShift_toFun,Prod.add_def,add_zero]
  rw [he] at h
  simp only [Prod.add_def,add_zero] at h
  exact congrArg (fun A : LiftedSpaceTimePhase →L[ℝ] ℝ => A (1,p.2,0)) h

def MassTest.timeShift (φ : MassTest) (τ : ℝ) : MassTest where
  toFun t x := φ.toFun (t+τ) x
  regular := φ.regular.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Velocity => (z.1+τ,z.2)) from by fun_prop)
  compact_time := by
    obtain ⟨R,hR,hzero⟩ := φ.compact_time
    exact ⟨R+|τ|,by positivity,fun t x ht => hzero (t+τ) x (time_shift_support ht)⟩

@[simp] theorem MassTest.timeShift_toFun (φ : MassTest) (τ t : ℝ) (x : Position) :
    (φ.timeShift τ).toFun t x = φ.toFun (t+τ) x := rfl

theorem MassTest.timeShift_transportDerivative (φ : MassTest) (τ t : ℝ) (p : Phase) :
    (φ.timeShift τ).transportDerivative t p = φ.transportDerivative (t+τ) p := by
  let L : ℝ × Velocity → ℝ := fun z => φ.toFun z.1 (torusProjection z.2)
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := L)
    (x := (t,torusRepresentative p.1)) (τ,0)
  have he : (fun z : ℝ × Velocity => L (z+(τ,0))) =
      (fun z => (φ.timeShift τ).toFun z.1 (torusProjection z.2)) := by
    funext z
    simp only [L,timeShift_toFun,Prod.add_def,add_zero]
  rw [he] at h
  simp only [Prod.add_def,add_zero] at h
  exact congrArg (fun A : (ℝ × Velocity) →L[ℝ] ℝ => A (1,p.2)) h

end BoltzmannNonuniqueness

end

end

section

/-! # Measurable representatives for periodic kinetic and mass tests -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

@[fun_prop] theorem measurable_torusRepresentative : Measurable torusRepresentative := by
  have hm : Measurable (fun x : Position => fun i : Fin 3 =>
      ((AddCircle.equivIco (1:ℝ) 0) (x i) : ℝ)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (T := (1:ℝ)) 0).measurable.comp (measurable_pi_apply i))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hm

private theorem measurable_kineticTestPoint : Measurable (fun p : ℝ × Phase =>
    (p.1,(torusRepresentative p.2.1,p.2.2))) :=
  measurable_fst.prodMk ((measurable_torusRepresentative.comp measurable_snd.fst).prodMk measurable_snd.snd)

@[fun_prop] theorem KineticTest.measurable_toFun (φ : KineticTest) :
    Measurable (fun p : ℝ × Phase => φ.toFun p.1 p.2.1 p.2.2) := by
  have h := φ.regular.continuous.measurable.comp measurable_kineticTestPoint
  convert h using 1
  funext p
  exact congrArg (fun x => φ.toFun p.1 x p.2.2) (torusProjection_representative p.2.1).symm

@[fun_prop] theorem KineticTest.measurable_transportDerivative (φ : KineticTest) :
    Measurable (fun p : ℝ × Phase => φ.transportDerivative p.1 p.2) := by
  have hm := (φ.regular.continuous_fderiv (by simp)).measurable.comp measurable_kineticTestPoint
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
    (hm.prodMk (measurable_const.prodMk (measurable_snd.snd.prodMk measurable_const)))

@[fun_prop] theorem MassTest.measurable_toFun (φ : MassTest) :
    Measurable (fun p : ℝ × Phase => φ.toFun p.1 p.2.1) := by
  have hm : Measurable (fun p : ℝ × Phase => (p.1,torusRepresentative p.2.1)) :=
    measurable_fst.prodMk (measurable_torusRepresentative.comp measurable_snd.fst)
  have h := φ.regular.continuous.measurable.comp hm
  convert h using 1
  funext p
  exact congrArg (φ.toFun p.1) (torusProjection_representative p.2.1).symm

@[fun_prop] theorem MassTest.measurable_transportDerivative (φ : MassTest) :
    Measurable (fun p : ℝ × Phase => φ.transportDerivative p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × Phase => (p.1,torusRepresentative p.2.1)) :=
    measurable_fst.prodMk (measurable_torusRepresentative.comp measurable_snd.fst)
  have hd := (φ.regular.continuous_fderiv (by simp)).measurable.comp hm
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
    (hd.prodMk (measurable_const.prodMk measurable_snd.snd))

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform bounds for periodic tests on a finite time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness

private def fundamentalCube : Set Velocity :=
  WithLp.toLp 2 '' (univ.pi (fun _ : Fin 3 => Icc (0:ℝ) 1))

private theorem fundamentalCube_compact : IsCompact fundamentalCube :=
  (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)).image
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))

private theorem representative_mem_cube (x : Position) : torusRepresentative x ∈ fundamentalCube := by
  refine ⟨_,?_,rfl⟩
  intro i _
  have h := ((AddCircle.equivIco (1:ℝ) 0) (x i)).property
  exact ⟨h.1,by simpa using h.2.le⟩

private theorem kinetic_lift_support (φ : KineticTest) {R : ℝ}
    (hzero : ∀ t x v, R < |t| ∨ R < ‖v‖ → φ.toFun t x v = 0) :
    tsupport (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2) ⊆
      {z | ‖z.2.2‖ ≤ R} := by
  apply closure_minimal
  · intro z hz
    by_contra hn
    exact hz (hzero z.1 (torusProjection z.2.1) z.2.2 (Or.inr (lt_of_not_ge hn)))
  · exact isClosed_le (continuous_snd.snd.norm) continuous_const

private theorem kinetic_bounds_on_box (φ : KineticTest) (T R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase, ‖p.2‖ ≤ R →
      |φ.toFun t p.1 p.2| ≤ C ∧
      ‖fderiv ℝ (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2)
        (t,torusRepresentative p.1,p.2)‖ ≤ C := by
  let K : Set LiftedSpaceTimePhase := Icc 0 T ×ˢ (fundamentalCube ×ˢ Metric.closedBall 0 R)
  have hK : IsCompact K := isCompact_Icc.prod
    (fundamentalCube_compact.prod (isCompact_closedBall (0:Velocity) R))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn φ.regular.continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (φ.regular.continuous_fderiv (by simp)).continuousOn
  refine ⟨|B|+|D|,by positivity,?_⟩
  intro t ht p hv
  have hp : (t,torusRepresentative p.1,p.2) ∈ K :=
    ⟨ht,representative_mem_cube p.1,by simpa using hv⟩
  have hb : |φ.toFun t p.1 p.2| ≤ B := by
    simpa only [torusProjection_representative,Real.norm_eq_abs] using hB _ hp
  have hd := hD _ hp
  constructor
  · linarith [le_abs_self B,abs_nonneg D]
  · exact hd.trans (by linarith [le_abs_self D,abs_nonneg B])

private theorem velocity_fderiv_zero {L : LiftedSpaceTimePhase → ℝ} {R : ℝ}
    (hs : tsupport L ⊆ {z | ‖z.2.2‖ ≤ R}) (z : LiftedSpaceTimePhase) (hz : R < ‖z.2.2‖) :
    fderiv ℝ L z = 0 := by
  have hout : z ∉ tsupport L := fun h => (not_le_of_gt hz) (hs h)
  exact fderiv_of_notMem_tsupport ℝ hout

private theorem kinetic_derivative_zero (φ : KineticTest) {R : ℝ}
    (hzero : ∀ t x v, R < |t| ∨ R < ‖v‖ → φ.toFun t x v = 0)
    (t : ℝ) (p : Phase) (hv : R < ‖p.2‖) : φ.transportDerivative t p = 0 := by
  let L : LiftedSpaceTimePhase → ℝ := fun z => φ.toFun z.1 (torusProjection z.2.1) z.2.2
  have hs : tsupport L ⊆ {z | ‖z.2.2‖ ≤ R} := kinetic_lift_support φ hzero
  exact congrArg (fun A : LiftedSpaceTimePhase →L[ℝ] ℝ => A ((1:ℝ),p.2,0))
    (velocity_fderiv_zero hs (t,torusRepresentative p.1,p.2) hv)

theorem KineticTest.bounded_on_time (φ : KineticTest) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase,
      |φ.toFun t p.1 p.2| ≤ C ∧ |φ.transportDerivative t p| ≤ C := by
  obtain ⟨R,hR,hzero⟩ := φ.compact_time_velocity
  obtain ⟨B,hB,hbounds⟩ := kinetic_bounds_on_box φ T R
  refine ⟨B*(1+R),by positivity,?_⟩
  intro t ht p
  by_cases hv : ‖p.2‖ ≤ R
  · obtain ⟨hb,hd⟩ := hbounds t ht p hv
    have htangent : ‖((1:ℝ),p.2,(0:Velocity))‖ ≤ 1+R := by
      simp only [Prod.norm_def,Real.norm_eq_abs,abs_one,norm_zero,max_eq_left (norm_nonneg p.2)]
      exact max_le (by linarith) (by linarith)
    constructor
    · nlinarith
    · change ‖fderiv ℝ (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2)
        (t,torusRepresentative p.1,p.2) ((1:ℝ),p.2,0)‖ ≤ _
      exact ((fderiv ℝ _ _).le_opNorm _).trans
        (mul_le_mul hd htangent (norm_nonneg _) hB)
  · rw [hzero t p.1 p.2 (Or.inr (lt_of_not_ge hv)),kinetic_derivative_zero φ hzero t p (lt_of_not_ge hv)]
    simp only [abs_zero]
    constructor <;> positivity

theorem MassTest.bounded_on_time (φ : MassTest) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase,
      |φ.toFun t p.1| ≤ C ∧ |φ.transportDerivative t p| ≤ C*(1+‖p.2‖) := by
  let K : Set (ℝ × Velocity) := Icc 0 T ×ˢ fundamentalCube
  have hK : IsCompact K := isCompact_Icc.prod fundamentalCube_compact
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn φ.regular.continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (φ.regular.continuous_fderiv (by simp)).continuousOn
  refine ⟨|B|+|D|,by positivity,?_⟩
  intro t ht p
  have hp : (t,torusRepresentative p.1) ∈ K := ⟨ht,representative_mem_cube p.1⟩
  have hb : |φ.toFun t p.1| ≤ |B| := by
    simpa only [torusProjection_representative,Real.norm_eq_abs] using
      (hB _ hp).trans (le_abs_self B)
  have hd : ‖fderiv ℝ (fun z : ℝ × Velocity => φ.toFun z.1 (torusProjection z.2))
      (t,torusRepresentative p.1)‖ ≤ |D| := (hD _ hp).trans (le_abs_self D)
  have htangent : ‖((1:ℝ),p.2)‖ ≤ 1+‖p.2‖ := by
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_one]
    exact max_le (by linarith [norm_nonneg p.2]) (by linarith)
  constructor
  · linarith [abs_nonneg D]
  · change ‖fderiv ℝ (fun z : ℝ × Velocity => φ.toFun z.1 (torusProjection z.2))
      (t,torusRepresentative p.1) ((1:ℝ),p.2)‖ ≤ _
    exact ((fderiv ℝ _ _).le_opNorm _).trans (mul_le_mul
      (hd.trans (by linarith [abs_nonneg B])) htangent (norm_nonneg _) (by positivity))

end BoltzmannNonuniqueness

end

end

section

/-! # Free transport preserves strong L1 continuity of an integrable curve -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.TorusFlight

theorem strong_curve_flight {T : ℝ} {C : ℝ → Density}
    (hC : ∀ s ∈ Icc 0 T, Integrable (C s)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hc : Tendsto (fun s => eLpNorm (fun p => C s p-C t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (fun p => C s (flight (-s) p)-C t (flight (-t) p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝[Icc 0 T] t) (𝓝 (-t)) :=
    continuous_neg.continuousAt.tendsto.mono_left inf_le_left
  have hfixed := (tendsto_flight_L1 (hC t ht) (-t)).comp hneg
  have hu := hc.add hfixed
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Filter.Eventually.of_forall (fun _ => zero_le))
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdiff : Integrable (fun p => C s p-C t p) := (hC s hs).sub (hC t ht)
  have hi := eLpNorm_comp_measurePreserving hdiff.aestronglyMeasurable
    (flight_measurePreserving (-s)) (p := 1)
  have he : (fun p => C s (flight (-s) p)-C t (flight (-t) p)) =
      (fun p => C s (flight (-s) p)-C t (flight (-s) p))+
        (fun p => C t (flight (-s) p)-C t (flight (-t) p)) := by
    funext p
    simp only [Pi.add_apply]
    ring
  rw [he]
  apply (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
  exact add_le_add hi.le le_rfl

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Smoothness of periodic tests on each free characteristic -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem KineticTest.contDiff_along (φ : KineticTest) (p : Phase) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      (s,(torusRepresentative p.1+s • p.2,p.2))) := by fun_prop
  have h := φ.regular.comp hL
  convert h using 1
  funext s
  have he := centered_characteristic_projection p 0 s
  simp only [TorusFlight.flight_zero,sub_zero] at he
  exact congrArg (fun x => φ.toFun s x p.2) he.symm

theorem MassTest.contDiff_along (φ : MassTest) (p : Phase) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => φ.toFun s (TorusFlight.flight s p).1) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      (s,torusRepresentative p.1+s • p.2)) := by fun_prop
  have h := φ.regular.comp hL
  convert h using 1
  funext s
  have he := centered_characteristic_projection p 0 s
  simp only [TorusFlight.flight_zero,sub_zero] at he
  exact congrArg (φ.toFun s) he.symm

end BoltzmannNonuniqueness

end

end

section

/-! # Entropy moments under free transport on the torus -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness

theorem FiniteEntropyDatum.comp_flight {f : Density} (hf : FiniteEntropyDatum f) (t : ℝ) :
    FiniteEntropyDatum (fun p => f (TorusFlight.flight t p)) := by
  have hmp := TorusFlight.flight_measurePreserving t
  refine ⟨hmp.quasiMeasurePreserving.ae hf.1,
    hf.2.1.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving,?_⟩
  have he : entropyMoment (fun p => f (TorusFlight.flight t p)) =
      (entropyMoment f) ∘ TorusFlight.flight t := rfl
  rw [he]
  exact hmp.integrable_comp_of_integrable hf.2.2

theorem TorusFlight.entropyMoment_integral_comp {f : Density} (hfm : Measurable f) (t : ℝ) :
    (∫ p, entropyMoment (fun q => f (TorusFlight.flight t q)) p) = ∫ p, entropyMoment f p := by
  exact Published.integral_comp_measurePreserving (TorusFlight.flight_measurePreserving t)
    (PeriodicApproximation.entropyGauge_measurable hfm)

end BoltzmannNonuniqueness

end

end

end OAI
