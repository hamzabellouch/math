import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ParabolicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ScalarMass
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfilesIntegrableImpulse
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CylinderDLift
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculusTimeDEqDeriv
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MildScalarContDiffScalar
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfilesLocalSupportImpulse
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingArray

namespace OAI

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding UniformDerivatives JointCalculus SmoothProfiles TailSpace
variable (A : RoutingData) (ν : ℝ)

theorem force_finiteCylinderSupport (hν : 0 < ν) (p : Coord 2) (T : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t, 0 ≤ t → t ≤ T →
      ∀ X : Coord 3, horizontal X ∉ K → force A ν p t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt T
  let a : ℝ × Coord 2 → Coord 2 :=
    fun q => ∑ n ∈ Finset.range Q, stage A ν n q.1 q.2
  have ha : HasCompactSupport a := by
    simpa only [Finset.sum_fn, a] using HasCompactSupport.finset_sum
      (fun n (_ : n ∈ Finset.range Q) => compactSupport_stage A ν hν n)
  let K : Set (Coord 2) := (Prod.snd '' tsupport (residual ν a)) ∪ tsupport (spatialPulse p)
  refine ⟨K, ((compactSupport_residual ν ha).image continuous_snd).union
    (compactSupport_spatialPulse p), ?_⟩
  intro t ht0 ht X hX
  have hev : uncurry (field A ν) =ᶠ[𝓝 (t, horizontal X)] a := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds (ht.trans_lt hQ)] with q hq
    exact field_eq_finite A ν hν hq q.2
  have hr : residual ν a (t, horizontal X) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hX (Or.inl ⟨(t, horizontal X), h, rfl⟩)
  have hg : spatialPulse p (horizontal X) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hX (Or.inr h)
  simp only [force, lift, projection_apply,
    (eventuallyEq_residual ν hev).eq_of_nhds, hr, Pi.zero_apply, uncurry_apply_pair, impulse, hg,
    mul_zero]
  ext i
  fin_cases i <;> rfl

theorem force_NavierStokes (hν : 0 < ν) (p : Coord 2) (ρ : ScalarField 2)
    (hρ : ∀ t, 0 ≤ t → ∀ X, timeD ρ t X + advection (field A ν) ρ t X =
      ν * laplacian ρ t X + impulse p t X) (hρ0 : ∀ X, ρ 0 X = 0) :
    NavierStokes ν (liftVelocity (field A ν) ρ) 0
      (force A ν p) := by
  have hn := triangular_reduction ν (field A ν) ρ (impulse p)
    (fun t _ => divergence_field A ν hν t) hρ
    (field_at_rest A ν hν (by norm_num)) hρ0
  refine ⟨?_, hn.2⟩
  intro t ht X i
  rw [force_eq_triangular A ν hν p ht]
  exact hn.1 t ht X i

theorem localSupport_field (hν : 0 < ν) (i : Fin 2) :
    LocalHorizontalSupport (fun t X => field A ν t X i) := by
  intro T hT
  obtain ⟨K, hK, hzero⟩ := finiteCylinderSupport A ν hν T
  refine ⟨K, hK, ?_⟩
  intro t ht X hX
  by_cases ht0 : 0 ≤ t
  · exact congrFun (hzero t ht0 ((le_abs_self t).trans ht) X hX) i
  · have h := field_at_rest A ν hν (show t ≤ 1 by linarith) X
    exact congrFun h i

theorem field_C1Tails (hν : 0 < ν) (i : Fin 2) :
    C1Tails (fun t X => field A ν t X i) :=
  c1Tails_of_smooth_support ((contDiff_apply ℝ ℝ i).comp (contDiff_field A ν hν))
    (localSupport_field A ν hν i)

theorem field_D_Tails (hν : 0 < ν) (i k : Fin 2) :
    ContinuousTails (spatialD k (fun t X => field A ν t X i)) :=
  (spatial_c1Tails_of_smooth_support (f := fun t X => field A ν t X i)
    ((contDiff_apply ℝ ℝ i).comp (contDiff_field A ν hν))
    (localSupport_field A ν hν i) k).continuous

theorem field_DD_Tails (hν : 0 < ν) (i k l : Fin 2) :
    ContinuousTails (spatialD l (spatialD k (fun t X => field A ν t X i))) :=
  second_continuousTails_of_smooth_support (f := fun t X => field A ν t X i)
    ((contDiff_apply ℝ ℝ i).comp (contDiff_field A ν hν))
    (localSupport_field A ν hν i) k l

theorem comparisonClass_of_scalar_tails (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ))) :
    Cylinder.ComparisonClass
      (fun t x => liftVelocity (field A ν) ρ t (Cylinder.join x))
      (fun _ _ => 0) := by
  let v : ℝ → Coord 2 → Cylinder.Vect := fun t X =>
    ![field A ν t X 0, field A ν t X 1, ρ t X]
  have heq : (fun t x => liftVelocity (field A ν) ρ t (Cylinder.join x)) =
      (fun (t : ℝ) (x : Cylinder.Space) => v t x.1) := by
    funext t x
    have hh : horizontal (Cylinder.join x) = x.1 :=
      congrArg Prod.fst (Cylinder.split_join x)
    simp only [liftVelocity, hh, v]
  rw [heq]
  apply Cylinder.comparisonClass_lift_of_tails v
  · intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp (contDiff_field A ν hν)
    · exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp (contDiff_field A ν hν)
    · exact hρ
  · intro i
    fin_cases i
    · exact field_C1Tails A ν hν 0
    · exact field_C1Tails A ν hν 1
    · exact hr
  · intro i k
    fin_cases i
    · exact field_D_Tails A ν hν 0 k
    · exact field_D_Tails A ν hν 1 k
    · exact hD k
  · intro i k l
    fin_cases i
    · exact field_DD_Tails A ν hν 0 k l
    · exact field_DD_Tails A ν hν 1 k l
    · exact hDD k l

theorem field_slice_component (hν : 0 < ν) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun X => field A ν t X i) :=
  ((contDiff_apply ℝ ℝ i).comp
    (SpatialCalculus.contDiff_slice (contDiff_field A ν hν) t)).of_le (by simp)

theorem compactSupport_field_component (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (i : Fin 2) :
    HasCompactSupport (fun X => field A ν t X i) := by
  obtain ⟨K, hK, hzero⟩ := finiteCylinderSupport A ν hν t
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro X hX
  by_contra hnot
  exact hX (congrFun (hzero t ht le_rfl X hnot) i)

theorem scalar_mass (hν : 0 < ν) (p : Coord 2) {ρ : ScalarField 2}
    {r dr : ℝ → Lp ℝ 1 (volume : Measure (Coord 2))}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (hi : ∀ t, 0 ≤ t → ∀ i, Integrable (SpatialCalculus.partialD i (ρ t)))
    (hii : ∀ t, 0 ≤ t → ∀ i,
      Integrable (SpatialCalculus.partialD i (SpatialCalculus.partialD i (ρ t))))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field A ν) ρ t X =
        ν * laplacian ρ t X + impulse p t X)
    (hrep : ∀ t, (fun X => r t X) =ᵐ[volume] ρ t)
    (hdrep : ∀ t, 0 ≤ t → (fun X => dr t X) =ᵐ[volume] (fun X => deriv (fun s => ρ s X) t))
    (hr : ∀ t, 0 ≤ t → HasDerivWithinAt r (dr t) (Ici 0) t)
    (hzero : ∀ X, ρ 0 X = 0) : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t := by
  refine ScalarMass.mass_eq_primitive hρ hi hii (fun t _ => integrable_impulse p t)
    (fun t _ i => field_slice_component A ν hν t i)
    (fun t ht i => compactSupport_field_component A ν hν ht i)
    (fun t _ X => divergence_field A ν hν t X)
    heq hrep hdrep hr ?_ ?_
  · intro t _
    rw [integral_impulse]
    exact (differentiable_step t).hasDerivAt.hasDerivWithinAt
  · simp only [hzero, integral_zero]
    exact Real.smoothTransition.zero.symm

theorem scalar_properties_of_C1Tails (hν : 0 < ν) (p : Coord 2) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ)))
    (heq : ∀ t ≥ 0, ∀ X, timeD ρ t X + advection (field A ν) ρ t X =
      ν * laplacian ρ t X + impulse p t X)
    (hzero : ∀ X, ρ 0 X = 0) :
    (∀ t ≥ 0, ∀ X, 0 ≤ ρ t X) ∧ (∀ t, Integrable (ρ t)) ∧
      (∀ t ≥ 0, (∫ X, ρ t X) = step t) := by
  have hd (t : ℝ) (ht : 0 ≤ t) (X : Coord 2) : timeD ρ t X = deriv (fun s => ρ s X) t :=
    JointCalculus.timeD_eq_deriv ht X (hρ.differentiable (by simp) (t, X))
  have heq' (t : ℝ) (ht : 0 ≤ t) (X : Coord 2) :
      deriv (fun s => ρ s X) t + advection (field A ν) ρ t X =
        ν * laplacian ρ t X + impulse p t X := by
    rw [← hd t ht X]
    exact heq t ht X
  obtain ⟨F, hFc, hFr⟩ := hr.continuous.C0_rep
  have hF2 : ContDiff ℝ 2 (fun q : ℝ × Coord 2 => F q.1 q.2) := by
    simpa only [hFr, Function.uncurry_def] using hρ.of_le (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hp := ParabolicComparison.nonnegative_of_continuous_C0 F hν.le hFc hF2
    (by simpa only [hFr] using heq') (fun X => by simpa only [hFr, hzero] using (le_refl (0 : ℝ)))
    (fun t _ X => impulse_nonneg p X t)
  obtain ⟨G, dG, -, -, hGa, hdGa, hGd⟩ := hr.L1_rep
  have hi (t : ℝ) (_ht : 0 ≤ t) (i : Fin 2) : Integrable (SpatialCalculus.partialD i (ρ t)) :=
    (hD i).integrable t
  have hii (t : ℝ) (_ht : 0 ≤ t) (i : Fin 2) :
      Integrable (SpatialCalculus.partialD i (SpatialCalculus.partialD i (ρ t))) :=
    (hDD i i).integrable t
  refine ⟨?_, fun t => hr.continuous.integrable t, ?_⟩
  · simpa only [hFr] using hp
  · apply scalar_mass A ν hν p (hρ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hi hii heq' hGa ?_ hGd hzero
    intro t ht
    have hh := hdGa t ht
    exact hh.trans (Filter.Eventually.of_forall (hd t ht))

def driftData (hν : 0 < ν) (i : Fin 2) : MildScalar.SupportedData :=
  ⟨fun t X => field A ν t X i,
    (contDiff_apply ℝ ℝ i).comp (contDiff_field A ν hν),
    localSupport_field A ν hν i⟩

@[simp] theorem driftData_scalar (hν : 0 < ν) (i : Fin 2) (t : ℝ) (X : Coord 2) :
    (driftData A ν hν i).scalar t X = field A ν t X i := rfl

def scalarSolution (hν : 0 < ν) (p : Coord 2) : ScalarField 2 :=
  MildScalar.scalar hν (driftData A ν hν) (impulseData p)

theorem contDiff_scalarSolution (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (scalarSolution A ν hν p)) :=
  MildScalar.contDiff_scalar hν _ _ (impulseData_nonpos p)

theorem scalarSolution_C1Tails (hν : 0 < ν) (p : Coord 2) :
    C1Tails (scalarSolution A ν hν p) :=
  MildScalar.scalar_C1Tails hν _ _

theorem scalarSolution_D_Tails (hν : 0 < ν) (p : Coord 2) (i : Fin 2) :
    ContinuousTails (spatialD i (scalarSolution A ν hν p)) :=
  MildScalar.scalar_D_Tails hν _ _ i

theorem scalarSolution_DD_Tails (hν : 0 < ν) (p : Coord 2) (i j : Fin 2) :
    ContinuousTails (spatialD j (spatialD i (scalarSolution A ν hν p))) :=
  MildScalar.scalar_DD_Tails hν _ _ i j

theorem scalarSolution_equation (hν : 0 < ν) (p : Coord 2) {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalarSolution A ν hν p) t X +
      advection (field A ν) (scalarSolution A ν hν p) t X =
        ν * laplacian (scalarSolution A ν hν p) t X + impulse p t X := by
  exact MildScalar.scalar_equation hν (driftData A ν hν) (impulseData p)
    (fun t _ X => divergence_field A ν hν t X) ht X

@[simp] theorem scalarSolution_zero (hν : 0 < ν) (p X : Coord 2) :
    scalarSolution A ν hν p 0 X = 0 :=
  MildScalar.scalar_zero hν _ _ X

theorem scalarSolution_properties (hν : 0 < ν) (p : Coord 2) :
    (∀ t ≥ 0, ∀ X, 0 ≤ scalarSolution A ν hν p t X) ∧
    (∀ t, Integrable (scalarSolution A ν hν p t)) ∧
    (∀ t ≥ 0, (∫ X, scalarSolution A ν hν p t X) = step t) :=
  scalar_properties_of_C1Tails A ν hν p
    (contDiff_scalarSolution A ν hν p)
    (scalarSolution_C1Tails A ν hν p)
    (scalarSolution_D_Tails A ν hν p)
    (scalarSolution_DD_Tails A ν hν p)
    (fun _ ht => scalarSolution_equation A ν hν p ht)
    (scalarSolution_zero A ν hν p)

def velocity (hν : 0 < ν) (p : Coord 2) : VectorField 3 :=
  liftVelocity (field A ν) (scalarSolution A ν hν p)

theorem contDiff_velocity (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (velocity A ν hν p)) := by
  convert JointCalculus.contDiff_lift (contDiff_field A ν hν)
    (contDiff_scalarSolution A ν hν p) using 1
  funext q
  simp only [uncurry, velocity, liftVelocity, JointCalculus.lift, JointCalculus.projection_apply]

theorem velocity_comparisonClass (hν : 0 < ν) (p : Coord 2) :
    Cylinder.ComparisonClass
      (fun t x => velocity A ν hν p t (Cylinder.join x)) (fun _ _ => 0) :=
  comparisonClass_of_scalar_tails A ν hν
    (contDiff_scalarSolution A ν hν p)
    (scalarSolution_C1Tails A ν hν p)
    (scalarSolution_D_Tails A ν hν p)
    (scalarSolution_DD_Tails A ν hν p)

theorem velocity_NavierStokes (hν : 0 < ν) (p : Coord 2) :
    NavierStokes ν (velocity A ν hν p) (fun _ _ => 0)
      (force A ν p) :=
  force_NavierStokes A ν hν p _
    (fun _ ht => scalarSolution_equation A ν hν p ht)
    (scalarSolution_zero A ν hν p)

theorem velocity_unique (hν : 0 < ν) (p : Coord 2) {v : VectorField 3} {q : ScalarField 3}
    (hv : Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
      (fun t x => q t (Cylinder.join x)))
    (hNS : NavierStokes ν v q (force A ν p)) :
    ∀ t ≥ 0, (∀ x, v t x = velocity A ν hν p t x) ∧ (∀ x, q t x = 0) :=
  Cylinder.comparison_unique_coordinates hν.le
    (velocity_comparisonClass A ν hν p) hv
    (velocity_NavierStokes A ν hν p) hNS

end VelocityDetection.RoutingArray
end

end OAI
