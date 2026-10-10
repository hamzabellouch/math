import OAI.Geometry.EinsteinFour.BoundedAngularMeanValue
import OAI.Geometry.EinsteinFour.CP2Overlap
import OAI.Geometry.EinsteinFour.CP2UnitGeometry
import OAI.Geometry.EinsteinFour.ComplexPairAlignment
import OAI.Geometry.EinsteinFour.ComplexProjectiveTriangle
import OAI.Geometry.EinsteinFour.FiniteExceptionalMeanValue
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.GeodesicGeometry12
import OAI.Geometry.EinsteinFour.LocalIncrementMeanValue
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences

namespace OAI


section

/-! Real complex circles are exactly multiplication by unit complex scalars. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
noncomputable section

def complexPhase (t : ℝ) : ℂ := ⟨Real.cos t, Real.sin t⟩

theorem complexPhase_norm (t : ℝ) : ‖complexPhase t‖ = 1 := by
  have h : ‖complexPhase t‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]
    change Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1
    nlinarith [Real.cos_sq_add_sin_sq t]
  nlinarith [norm_nonneg (complexPhase t)]

theorem complexPhase_arg (a : ℂ) (ha : ‖a‖ = 1) : complexPhase a.arg = a := by
  have hz : a ≠ 0 := by
    intro h
    rw [h,norm_zero] at ha
    exact zero_ne_one ha
  apply Complex.ext
  · change Real.cos a.arg = a.re
    rw [Complex.cos_arg hz,ha,div_one]
  · change Real.sin a.arg = a.im
    rw [Complex.sin_arg,ha,div_one]

theorem complexCoordinates_circle_standard (q : FourSpace) (t : ℝ) :
    complexCoordinates (complexCircleVector (twoFormMatrix standardSelfDualForm) q t) =
      complexPhase (-t) • complexCoordinates q := by
  rw [complexCircleVector, map_add, map_smul, map_smul, complexCoordinates_standard_complex]
  ext i
  apply Complex.ext <;> simp [complexPhase, Complex.mul_re, Complex.mul_im] <;>
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]

theorem complexCircle_standard_of_phase (p q : FourSpace) (a : ℂ) (ha : ‖a‖ = 1)
    (hpq : complexCoordinates p = a • complexCoordinates q) :
    p = complexCircleVector (twoFormMatrix standardSelfDualForm) q (-a.arg) := by
  apply complexCoordinates.injective
  rw [complexCoordinates_circle_standard, neg_neg, complexPhase_arg a ha]
  exact hpq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternionic direction frame preserves the standard
complex structure, so it can be used without changing the parallel form. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Angular
open scoped Manifold ContDiff
noncomputable section

theorem directionFrameMatrix_standard_complex (q : Directions) :
    directionFrameMatrix q * twoFormMatrix standardSelfDualForm =
      twoFormMatrix standardSelfDualForm * directionFrameMatrix q := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [directionFrameMatrix,standardSelfDualForm,twoFormMatrix,Fin.sum_univ_succ]

theorem twoFormFrameAction_direction_standard (q : Directions) :
    twoFormFrameAction (directionFrameMatrix q) standardSelfDualForm = standardSelfDualForm := by
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction,Matrix.mul_assoc,← directionFrameMatrix_standard_complex,
    ← Matrix.mul_assoc,directionFrameMatrix_orthogonal,Matrix.one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_direction_standard (w : M → TwoFormFour) (e : FrameBundle g)
    (hstd : twoFormFrameValue o w e = standardSelfDualForm) (q : Directions) :
    twoFormFrameValue o w (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) =
      standardSelfDualForm := by
  rw [twoFormFrameValue_rotate,hstd]
  exact twoFormFrameAction_direction_standard q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit projective polar points at the Ricci-three scale. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped BigOperators
noncomputable section

def complexPolarLift (t : ℝ) (q : Directions) : CP2Vector :=
  WithLp.toLp 2 ![(Real.cos (t / Real.sqrt 2) : ℂ),
    (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0,
    (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1]

theorem complexPolarLift_norm (t : ℝ) (q : Directions) : ‖complexPolarLift t q‖ = 1 := by
  have hq : ‖complexCoordinates q.val 0‖ ^ 2 + ‖complexCoordinates q.val 1‖ ^ 2 = 1 := by
    calc
      _ = ‖complexCoordinates q.val‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [complexCoordinates.norm_map, q.property]; norm_num
  have hn : ‖complexPolarLift t q‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    change ‖(Real.cos (t / Real.sqrt 2) : ℂ)‖ ^ 2 +
      ‖(Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0‖ ^ 2 +
      ‖(Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1‖ ^ 2 = 1
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (t / Real.sqrt 2),
      congrArg (fun r => Real.sin (t / Real.sqrt 2) ^ 2 * r) hq]
  nlinarith [norm_nonneg (complexPolarLift t q)]

theorem complexPolarLift_ne_zero (t : ℝ) (q : Directions) : complexPolarLift t q ≠ 0 := by
  intro h
  have hn := complexPolarLift_norm t q
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

def complexProjectivePolar (t : ℝ) (q : Directions) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexPolarLift t q) (complexPolarLift_ne_zero t q)

theorem complexPolarLift_inner (t s : ℝ) (q p : Directions) :
    inner ℂ (complexPolarLift t q) (complexPolarLift s p) =
      ((Real.cos (t / Real.sqrt 2) * Real.cos (s / Real.sqrt 2) : ℝ) : ℂ) +
        ((Real.sin (t / Real.sqrt 2) * Real.sin (s / Real.sqrt 2) : ℝ) : ℂ) *
          inner ℂ (complexCoordinates q.val) (complexCoordinates p.val) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  change (Real.cos (s / Real.sqrt 2) : ℂ) * star (Real.cos (t / Real.sqrt 2) : ℂ) +
    ((Real.sin (s / Real.sqrt 2) : ℂ) * complexCoordinates p.val 0) *
      star ((Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0) +
    ((Real.sin (s / Real.sqrt 2) : ℂ) * complexCoordinates p.val 1) *
      star ((Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1) = _
  simp only [Pi.star_apply]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem fubiniStudyDistance_complexPolar (t s : ℝ) (q p : Directions) :
    fubiniStudyDistance (complexProjectivePolar t q) (complexProjectivePolar s p) =
      Real.arccos ‖((Real.cos (t / Real.sqrt 2) * Real.cos (s / Real.sqrt 2) : ℝ) : ℂ) +
        ((Real.sin (t / Real.sqrt 2) * Real.sin (s / Real.sqrt 2) : ℝ) : ℂ) *
          inner ℂ (complexCoordinates q.val) (complexCoordinates p.val)‖ := by
  rw [complexProjectivePolar, complexProjectivePolar, fubiniStudyDistance_mk,
    complexPolarLift_norm, complexPolarLift_norm, one_mul, div_one, complexPolarLift_inner]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential is minimizing and injective inside the complex conjugate ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_minimizing (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ complexJacobiRadius) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    rw [complex_cut_time_all_directions hRic hminus hdim e he q]
    exact hv
  rwa [hrad] at hm

theorem complex_direction_injective (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) complexJacobiRadius)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (complexJacobiRadius - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < complexJacobiRadius := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_complex_minimizing hRic hminus hdim F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)

theorem frameExponential_complex_injOn_ball (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (Metric.ball 0 complexJacobiRadius) := by
  intro v hv w hw heq
  have hvπ : ‖v‖ < complexJacobiRadius := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwπ : ‖w‖ < complexJacobiRadius := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hn : ‖v‖ = ‖w‖ := by
    rw [← frameExponential_complex_minimizing hRic hminus hdim e he v hvπ.le,
      ← frameExponential_complex_minimizing hRic hminus hdim e he w hwπ.le, heq]
  by_cases hz : v = 0
  · subst v
    have hwzero : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hwzero.symm
  have hwz : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa only [h, norm_zero] using hn))
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let p : Directions := ⟨‖w‖⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwz)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hp : ‖v‖ • p.val = w := by
    change ‖v‖ • (‖w‖⁻¹ • w) = w
    rw [hn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwz), one_smul]
  have hqp : q = p := complex_direction_injective hRic hminus hdim e he q p
    ‖v‖ ⟨norm_pos_iff.mpr hz, hvπ⟩ (by rwa [hq, hp])
  rw [← hq, hqp, hp]


end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit representatives with nonnegative real first coordinate, for the
closed-ball polar description of the actual projective plane. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2_exists_first_aligned (p : ComplexProjective2) :
    ∃ z : CP2Vector, ∃ hz : z ≠ 0,
      ‖z‖ = 1 ∧ Projectivization.mk ℂ z hz = p ∧
      (z 0).im = 0 ∧ 0 ≤ (z 0).re := by
  let x := cp2UnitRep p
  have hx : x ≠ 0 := cp2UnitRep_ne_zero p
  by_cases hz : x 0 = 0
  · exact ⟨x,hx,cp2UnitRep_norm p,cp2UnitRep_mk p,by rw [hz]; rfl,
      by rw [hz]; exact le_rfl⟩
  let a : ℂ := (‖x 0‖ : ℂ) / x 0
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hz) hz
  have han : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, norm_ne_zero_iff.mpr hz]
  let z := a • x
  have hzn : z ≠ 0 := smul_ne_zero ha hx
  have hz0 : z 0 = (‖x 0‖ : ℂ) := by
    change a * x 0 = _
    exact div_mul_cancel₀ _ hz
  refine ⟨z,hzn,?_,?_,?_,?_⟩
  · change ‖a • x‖ = 1
    rw [norm_smul, han, cp2UnitRep_norm, mul_one]
  · rw [← cp2UnitRep_mk p]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a,rfl⟩
  · rw [hz0]
    rfl
  · rw [hz0]
    exact norm_nonneg _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Norm and inner product of the actual homogeneous projective coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexHeadTail (a : ℂ) (u : EuclideanSpace ℂ (Fin 2)) : CP2Vector :=
  WithLp.toLp 2 ![a,u 0,u 1]

theorem complexHeadTail_norm_sq (a : ℂ) (u : EuclideanSpace ℂ (Fin 2)) :
    ‖complexHeadTail a u‖ ^ 2 = ‖a‖ ^ 2 + ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
  change ‖a‖ ^ 2 + ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = ‖a‖ ^ 2 + (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2)
  ring

theorem complexHeadTail_inner (a b : ℂ) (u v : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (complexHeadTail a u) (complexHeadTail b v) =
      b * star a + inner ℂ u v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two,
    Pi.star_apply]
  change b * star a + v 0 * star (u 0) + v 1 * star (u 1) =
    b * star a + (v 0 * star (u 0) + v 1 * star (u 1))
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The projective quotient preserves the polar radius and is injective
at every strictly positive radius before the boundary. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

theorem complexPolar_angle_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) :
    t / Real.sqrt 2 ∈ Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨div_nonneg ht.1 (Real.sqrt_nonneg _), ?_⟩
  have h := div_le_div_of_nonneg_right ht.2 (Real.sqrt_nonneg 2)
  unfold complexJacobiRadius at h
  rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact h

theorem complexProjectivePolar_radius_eq {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius)
    (hs : s ∈ Icc (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar s p) : t = s := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have hn : ‖a‖ = 1 := by
    have h := congrArg norm ha
    simpa only [norm_smul, complexPolarLift_norm, mul_one] using h
  have h0 := congrArg (fun z : CP2Vector => z 0) ha
  have hc : Real.cos (s / Real.sqrt 2) = Real.cos (t / Real.sqrt 2) := by
    have h := congrArg norm h0
    change ‖a * (Real.cos (s / Real.sqrt 2) : ℂ)‖ =
      ‖(Real.cos (t / Real.sqrt 2) : ℂ)‖ at h
    rw [norm_mul, hn, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [(complexPolar_angle_mem hs).1, Real.pi_pos], (complexPolar_angle_mem hs).2⟩),
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [(complexPolar_angle_mem ht).1, Real.pi_pos], (complexPolar_angle_mem ht).2⟩)] at h
    exact h
  have ht' := complexPolar_angle_mem ht
  have hs' := complexPolar_angle_mem hs
  have h := congrArg Real.arccos hc
  rw [Real.arccos_cos hs'.1 (by linarith [hs'.2,Real.pi_pos]),
    Real.arccos_cos ht'.1 (by linarith [ht'.2,Real.pi_pos])] at h
  exact (div_left_inj' (by positivity : Real.sqrt 2 ≠ 0)).mp h.symm

theorem complexProjectivePolar_interior_injective {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar t p) : q = p := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have hangle := complexPolar_angle_mem ⟨ht.1.le,ht.2.le⟩
  have hlt : t / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right ht.2 (by positivity : 0 < Real.sqrt 2)
    unfold complexJacobiRadius at h
    rwa [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hc : (Real.cos (t / Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hangle.1,Real.pi_pos], hlt⟩).ne'
  have h0 := congrArg (fun z : CP2Vector => z 0) ha
  change a * (Real.cos (t / Real.sqrt 2) : ℂ) =
    (Real.cos (t / Real.sqrt 2) : ℂ) at h0
  have ha1 : a = 1 := (mul_eq_right₀ hc).mp h0
  have hs : (Real.sin (t / Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi
      (div_pos ht.1 (by positivity)) (by linarith [hlt,Real.pi_pos])).ne'
  rw [ha1,one_smul] at ha
  apply Subtype.ext
  apply complexCoordinates.injective
  ext i
  fin_cases i
  · have h := congrArg (fun z : CP2Vector => z 1) ha
    exact (mul_left_cancel₀ hs h).symm
  · have h := congrArg (fun z : CP2Vector => z 2) ha
    exact (mul_left_cancel₀ hs h).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three exact metric factors in a standard complex normal frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem heatNormalMetric_first_standard (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : 0 < t) :
    heatNormalMetric g o e (t • coordinateVector 0) = Matrix.diagonal
      ![1,(complexJacobiFast t / t)^2,(complexJacobiSlow t / t)^2,(complexJacobiSlow t / t)^2] := by
  rw [heatNormalMetric_first_parallel_form hRic hminus hnorm w hstar hw hz e he t ht,hstd]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp [jacobiBlockMatrix,Matrix.diagonal,Ne.symm (Fin.succ_ne_zero j)]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix,Matrix.diagonal]
    · simp only [jacobiBlockMatrix,Fin.cons_succ]
      fin_cases i <;> fin_cases j <;>
        norm_num [complexJacobiGram,standardSelfDualForm,Matrix.vecMulVec_apply,
          Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.diagonal,div_pow]
      all_goals ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual closed complex-conjugate ball covers the manifold. Its
interior and boundary are distinguished by the actual distance from the center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualMinimizingTangentDomain_complex (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualMinimizingTangentDomain g o e = Metric.closedBall 0 complexJacobiRadius := by
  ext v
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hv
    by_cases hz : v = 0
    · simpa only [hz, norm_zero] using complexJacobiRadius_pos.le
    let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hcut := (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖
      (norm_nonneg _)).mp (hq.symm ▸ hv)
    rwa [complex_cut_time_all_directions hRic hminus hdim e he q] at hcut
  · exact frameExponential_complex_minimizing hRic hminus hdim e he v

theorem frameExponential_complex_closedBall_image (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius = univ := by
  rw [← actualMinimizingTangentDomain_complex hRic hminus hdim e he]
  exact actualMinimizingTangentDomain_image g o hRic e he

theorem frameExponential_complex_fiber_norm (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) {v w : FourSpace}
    (hv : ‖v‖ ≤ complexJacobiRadius) (hw : ‖w‖ ≤ complexJacobiRadius)
    (heq : frameExponential g o e v = frameExponential g o e w) : ‖v‖ = ‖w‖ := by
  rw [← frameExponential_complex_minimizing hRic hminus hdim e he v hv,
    ← frameExponential_complex_minimizing hRic hminus hdim e he w hw, heq]

theorem frameExponential_complex_interior_fiber (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) {v w : FourSpace}
    (hv : ‖v‖ < complexJacobiRadius) (hw : ‖w‖ ≤ complexJacobiRadius)
    (heq : frameExponential g o e v = frameExponential g o e w) : v = w := by
  have hn := frameExponential_complex_fiber_norm hRic hminus hdim e he hv.le hw heq
  apply frameExponential_complex_injOn_ball hRic hminus hdim e he
    (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
    (by simpa only [Metric.mem_ball, dist_zero_right, ← hn] using hv) heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine chart of CP2 and its exact polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexAffineLift (z : EuclideanSpace ℂ (Fin 2)) : CP2Vector :=
  WithLp.toLp 2 ![1,z 0,z 1]

theorem complexAffineLift_ne_zero (z : EuclideanSpace ℂ (Fin 2)) : complexAffineLift z ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : CP2Vector => v 0) h
  exact one_ne_zero h0

def complexAffinePoint (z : EuclideanSpace ℂ (Fin 2)) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexAffineLift z) (complexAffineLift_ne_zero z)

theorem complexAffinePoint_injective : Function.Injective complexAffinePoint := by
  intro z w h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrArg (fun v : CP2Vector => v 0) ha
  have ha1 : a = 1 := by
    change a * 1 = 1 at h0
    simpa only [mul_one] using h0
  rw [ha1,one_smul] at ha
  ext i
  fin_cases i
  · exact (congrArg (fun v : CP2Vector => v 1) ha).symm
  · exact (congrArg (fun v : CP2Vector => v 2) ha).symm

theorem complexProjectivePolar_affine (t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) complexJacobiRadius) (q : Directions) :
    complexProjectivePolar t q =
      complexAffinePoint ((Real.tan (t / Real.sqrt 2)) • complexCoordinates q.val) := by
  have hangle := complexPolar_angle_mem ⟨ht.1,ht.2.le⟩
  have hlt : t / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right ht.2 (by positivity : 0 < Real.sqrt 2)
    unfold complexJacobiRadius at h
    rwa [div_div,← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hc : Real.cos (t / Real.sqrt 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hangle.1,Real.pi_pos],hlt⟩).ne'
  have hcs : (Real.cos (t / Real.sqrt 2) : ℂ) * (Real.tan (t / Real.sqrt 2) : ℂ) =
      (Real.sin (t / Real.sqrt 2) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.tan_eq_sin_div_cos]
    congr 1
    field_simp
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(Real.cos (t / Real.sqrt 2) : ℂ),?_⟩
  ext i
  fin_cases i
  · change (Real.cos (t / Real.sqrt 2) : ℂ) * 1 = _
    exact mul_one _
  · change (Real.cos (t / Real.sqrt 2) : ℂ) *
      ((Real.tan (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0) = _
    rw [← mul_assoc,hcs]
    rfl
  · change (Real.cos (t / Real.sqrt 2) : ℂ) *
      ((Real.tan (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1) = _
    rw [← mul_assoc,hcs]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full bilinear exponential metric in standard complex coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem complex_diagonal_pairing (a b : ℝ) (u v : FourSpace) :
    WithLp.ofLp u ⬝ᵥ (Matrix.diagonal ![1,b^2,a^2,a^2] *ᵥ WithLp.ofLp v) =
      a^2 * inner ℝ u v + (1-a^2)*u 0*v 0 + (b^2-a^2)*u 1*v 1 := by
  simp [dotProduct,Matrix.mulVec_diagonal,Fin.sum_univ_four,PiLp.inner_apply,RCLike.inner_apply]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_first_pairing (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : 0 < t) (u v : FourSpace) :
    g.inner (frameExponential g o e (t • coordinateVector 0))
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) u)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) v) =
        (complexJacobiSlow t / t)^2 * inner ℝ u v +
          (1-(complexJacobiSlow t / t)^2)*u 0*v 0 +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*u 1*v 1 := by
  have hp := heatNormalMetric_pairing g o e (t • coordinateVector 0)
    (WithLp.ofLp u) (WithLp.ofLp v)
  simp only [WithLp.toLp_ofLp] at hp
  rw [← hp,heatNormalMetric_first_standard hRic hminus hnorm w hstar hw hz e he hstd t ht]
  exact complex_diagonal_pairing _ _ u v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact boundary equivalence relation of the projective polar ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complexPolar_radius_angle : complexJacobiRadius / Real.sqrt 2 = Real.pi / 2 := by
  rw [complexJacobiRadius,div_div,← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem complexPolarLift_radius (q : Directions) :
    complexPolarLift complexJacobiRadius q =
      WithLp.toLp 2 ![0,complexCoordinates q.val 0,complexCoordinates q.val 1] := by
  simp [complexPolarLift,complexPolar_radius_angle]

theorem complexProjectivePolar_boundary_phase (q p : Directions)
    (heq : complexProjectivePolar complexJacobiRadius q =
      complexProjectivePolar complexJacobiRadius p) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ complexCoordinates p.val = a • complexCoordinates q.val := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq.symm
  refine ⟨a,?_,?_⟩
  · have h := congrArg norm ha
    simpa only [norm_smul,complexPolarLift_norm,mul_one] using h
  · apply Eq.symm
    ext i
    fin_cases i
    · have h := congrArg (fun z : CP2Vector => z 1) ha
      simp only [complexPolarLift_radius] at h
      exact h
    · have h := congrArg (fun z : CP2Vector => z 2) ha
      simp only [complexPolarLift_radius] at h
      exact h

theorem complexProjectivePolar_boundary_circle (q p : Directions)
    (heq : complexProjectivePolar complexJacobiRadius q =
      complexProjectivePolar complexJacobiRadius p) :
    ∃ t : ℝ, p.val = complexCircleVector (twoFormMatrix standardSelfDualForm) q.val t := by
  obtain ⟨a,ha,hpq⟩ := complexProjectivePolar_boundary_phase q p heq
  exact ⟨-a.arg,complexCircle_standard_of_phase p.val q.val a ha hpq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every point of CP2 occurs in the explicit closed polar ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped BigOperators
noncomputable section

private theorem exists_radial_direction (v : FourSpace) :
    ∃ q : Directions, ‖v‖ • q.val = v := by
  by_cases hv : v = 0
  · exact ⟨firstDirection, by simp [hv]⟩
  refine ⟨⟨‖v‖⁻¹ • v, ?_⟩, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · exact (smul_smul _ _ _).trans (by
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul])

theorem complexProjectivePolar_surjective (p : ComplexProjective2) :
    ∃ t ∈ Icc (0 : ℝ) complexJacobiRadius, ∃ q : Directions,
      complexProjectivePolar t q = p := by
  obtain ⟨z,hz,hn,hp,him,hre⟩ := cp2_exists_first_aligned p
  let a := (z 0).re
  let u : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![z 1,z 2]
  let v := complexCoordinates.symm u
  have hhead : z 0 = (a : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  have hvn : ‖v‖ = ‖u‖ := complexCoordinates.symm.norm_map u
  have hsquare : a ^ 2 + ‖v‖ ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hn
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hhead] at h
    rw [hvn, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simpa only [u, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, one_pow, add_assoc] using h
  have ha0 : 0 ≤ a := hre
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg ‖v‖]
  let θ := Real.arccos a
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg a
  have hθ1 : θ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr ha0
  have hcos : Real.cos θ = a := Real.cos_arccos (by linarith) ha1
  have hsin : Real.sin θ = ‖v‖ := by
    rw [Real.sin_arccos]
    rw [show 1 - a ^ 2 = ‖v‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg _)
  obtain ⟨q,hq⟩ := exists_radial_direction v
  have hu : ‖v‖ • complexCoordinates q.val = u := by
    have h := congrArg complexCoordinates hq
    simpa only [map_smul, v, LinearIsometryEquiv.apply_symm_apply] using h
  let t := Real.sqrt 2 * θ
  have hdivide : t / Real.sqrt 2 = θ := by
    dsimp only [t]
    exact mul_div_cancel_left₀ θ (by positivity)
  have hscale : Real.sqrt 2 * (Real.pi / 2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ht : t ∈ Icc (0 : ℝ) complexJacobiRadius :=
    ⟨mul_nonneg (Real.sqrt_nonneg _) hθ0,
      (mul_le_mul_of_nonneg_left hθ1 (Real.sqrt_nonneg _)).trans_eq hscale⟩
  have hlift : complexPolarLift t q = z := by
    ext i
    fin_cases i
    · change (Real.cos (t / Real.sqrt 2) : ℂ) = z 0
      rw [hdivide,hcos,hhead]
    · have h := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x 0) hu
      change (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0 = z 1
      rw [hdivide,hsin]
      exact h
    · have h := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x 1) hu
      change (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1 = z 2
      rw [hdivide,hsin]
      exact h
  refine ⟨t,ht,q,?_⟩
  simpa only [complexProjectivePolar, hlift] using hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normal coordinates for every point strictly before the complex cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_complex_interior_coordinates (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (x : M)
    (hR : metricDistance g e.base x < complexJacobiRadius) (hx : x ≠ e.base) :
    ∃ v : FourSpace, v ≠ 0 ∧ ‖v‖ < complexJacobiRadius ∧ frameExponential g o e v = x := by
  have hx' : x ∈ frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius := by
    rw [frameExponential_complex_closedBall_image hRic hminus hdim e he]
    trivial
  obtain ⟨v,hv,hvx⟩ := hx'
  have hvR : ‖v‖ ≤ complexJacobiRadius := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hdist := frameExponential_complex_minimizing hRic hminus hdim e he v hvR
  rw [hvx] at hdist
  refine ⟨v,?_,by rwa [← hdist],hvx⟩
  intro hz
  rw [hz,frameExponential_zero] at hvx
  exact hx hvx.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact logarithm of the standard projective affine chart, in the
Ricci-three normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexAffineRadius (z : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  Real.sqrt 2 * Real.arctan ‖z‖

def complexAffineLog (z : EuclideanSpace ℂ (Fin 2)) : FourSpace :=
  (complexAffineRadius z / ‖z‖) • complexCoordinates.symm z

theorem complexAffineRadius_mem (z : EuclideanSpace ℂ (Fin 2)) :
    complexAffineRadius z ∈ Ico (0 : ℝ) complexJacobiRadius := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.arctan_nonneg.mpr (norm_nonneg _)),?_⟩
  have h := mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two ‖z‖)
    (by positivity : 0 < Real.sqrt 2)
  have heq : Real.sqrt 2 * (Real.pi / 2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact h.trans_eq heq

theorem complexAffineLog_norm (z : EuclideanSpace ℂ (Fin 2)) :
    ‖complexAffineLog z‖ = complexAffineRadius z := by
  by_cases hz : z = 0
  · simp [hz,complexAffineLog,complexAffineRadius]
  rw [complexAffineLog,norm_smul,complexCoordinates.symm.norm_map,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (complexAffineRadius_mem z).1 (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem complexAffinePoint_polar_log (z : EuclideanSpace ℂ (Fin 2)) :
    ∃ q : Directions,
      complexProjectivePolar (complexAffineRadius z) q = complexAffinePoint z ∧
      complexAffineRadius z • q.val = complexAffineLog z := by
  have ht := complexAffineRadius_mem z
  by_cases hz : z = 0
  · refine ⟨firstDirection,?_,?_⟩
    · simpa [hz,complexAffineRadius] using complexProjectivePolar_affine 0
        ⟨le_rfl,complexJacobiRadius_pos⟩ firstDirection
    · simp [hz,complexAffineRadius,complexAffineLog]
  let q : Directions := ⟨‖z‖⁻¹ • complexCoordinates.symm z,by
    rw [norm_smul,complexCoordinates.symm.norm_map,Real.norm_eq_abs,abs_inv,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hq : complexCoordinates q.val = ‖z‖⁻¹ • z := by
    change complexCoordinates (‖z‖⁻¹ • complexCoordinates.symm z) = _
    rw [map_smul,LinearIsometryEquiv.apply_symm_apply]
  have hd : complexAffineRadius z / Real.sqrt 2 = Real.arctan ‖z‖ := by
    exact mul_div_cancel_left₀ _ (by positivity)
  refine ⟨q,?_,?_⟩
  · rw [complexProjectivePolar_affine _ ht,hq,hd,Real.tan_arctan,smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]
  · change complexAffineRadius z • (‖z‖⁻¹ • complexCoordinates.symm z) = _
    rw [smul_smul,complexAffineLog,div_eq_mul_inv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrary-direction form of the actual complex radial metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

def complexCompanion (q : Directions) : FourSpace :=
  WithLp.toLp 2 ![-q.val 1,q.val 0,-q.val 3,q.val 2]

theorem complexCoordinates_companion (q : Directions) :
    complexCoordinates (complexCompanion q) = Complex.I • complexCoordinates q.val := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCompanion,complexCoordinates,complexCoordinatesLinear]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_pairing (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) z) =
        (complexJacobiSlow t / t)^2 * inner ℝ w z +
          (1-(complexJacobiSlow t / t)^2)*inner ℝ q.val w * inner ℝ q.val z +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*
            inner ℝ (complexCompanion q) w * inner ℝ (complexCompanion q) z := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hpoint : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hbase : frameExponential g o f (t • coordinateVector 0) =
      frameExponential g o e (t • q.val) := by
    rw [frameExponential_rotate]
    exact congrArg (frameExponential g o e) hpoint
  have hD (u : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) u =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L u) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) u
    change _ = mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L u) at h
    rwa [hpoint] at h
  have hzero (u : FourSpace) : (L.symm u) 0 = inner ℝ q.val u := by
    have h := L.inner_map_map (coordinateVector 0) (L.symm u)
    rw [hfirst, L.apply_symm_apply] at h
    simpa [PiLp.inner_apply, coordinateVector] using h.symm
  have hsecond : L (coordinateVector 1) = complexCompanion q := by
    change WithLp.toLp 2 ((directionFrameMatrix q) *ᵥ Pi.single 1 1) = _
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> rfl
  have hone (u : FourSpace) : (L.symm u) 1 = inner ℝ (complexCompanion q) u := by
    have h := L.inner_map_map (coordinateVector 1) (L.symm u)
    rw [hsecond,L.apply_symm_apply] at h
    simpa [PiLp.inner_apply,coordinateVector] using h.symm
  have hinner : inner ℝ (L.symm w) (L.symm z) = inner ℝ w z := by
    simpa only [L.apply_symm_apply] using
      (L.inner_map_map (L.symm w) (L.symm z)).symm
  have hfstd : twoFormFrameValue o W.val f = standardSelfDualForm :=
    twoFormFrameValue_direction_standard W.val e hstd q
  have h := frameExponential_complex_first_pairing hRic hminus hnorm W hstar hw hz
    f hf hfstd t ht (L.symm w) (L.symm z)
  let B₁ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o f (t • coordinateVector 0))
  let B₂ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o e (t • q.val))
  let D₁ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0)
  let D₂ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o e) (t • q.val)
  have hB : B₁ = B₂ := by
    dsimp only [B₁, B₂]
    rw [hbase]
  have hD' (u : FourSpace) : D₁ u = D₂ (L u) := hD u
  change B₁ (D₁ (L.symm w)) (D₁ (L.symm z)) = _ at h
  change B₂ (D₂ w) (D₂ z) = _
  rw [hB, hD', hD', L.apply_symm_apply, L.apply_symm_apply, hinner,
    hzero, hzero, hone, hone] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact distance to the north pole in the projective polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexProjectiveNorth : ComplexProjective2 := complexProjectivePolar 0 firstDirection

theorem complexProjectivePolar_zero (q : Directions) :
    complexProjectivePolar 0 q = complexProjectiveNorth := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1,by simp [complexPolarLift]⟩

theorem fubiniStudyDistance_north_polar (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    fubiniStudyDistance complexProjectiveNorth (complexProjectivePolar t q) = t / Real.sqrt 2 := by
  rw [complexProjectiveNorth,fubiniStudyDistance_complexPolar]
  simp only [zero_div,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,Complex.ofReal_zero,
    add_zero,Complex.norm_real,Real.norm_eq_abs]
  have ha := complexPolar_angle_mem ht
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ha.1,Real.pi_pos],ha.2⟩),
    Real.arccos_cos ha.1 (by linarith [ha.2,Real.pi_pos])]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hausdorff topology determined by the actual projective overlaps. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexProjectiveEvaluation (p : ComplexProjective2) : ComplexProjective2 → ℝ :=
  fun q => cp2Overlap q p

@[instance_reducible] def complexProjectiveTopology : TopologicalSpace ComplexProjective2 :=
  TopologicalSpace.induced complexProjectiveEvaluation inferInstance

attribute [local instance] complexProjectiveTopology

theorem complexProjectiveEvaluation_injective : Function.Injective complexProjectiveEvaluation := by
  intro p q hpq
  have h := congrFun hpq p
  change cp2Overlap p p = cp2Overlap p q at h
  rw [cp2Overlap_self] at h
  exact (cp2Overlap_eq_one_iff p q).mp h.symm

theorem complexProjectiveEvaluation_isEmbedding : Topology.IsEmbedding complexProjectiveEvaluation :=
  complexProjectiveEvaluation_injective.isEmbedding_induced

theorem complexProjective_t2Space : T2Space ComplexProjective2 :=
  complexProjectiveEvaluation_isEmbedding.t2Space

theorem complexPolarLift_continuous :
    Continuous (fun x : ℝ × Directions => complexPolarLift x.1 x.2) := by
  have hC : Continuous (fun x : ℝ × Directions => complexCoordinates x.2.val) :=
    complexCoordinates.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous (fun x : ℝ × Directions =>
      (![(Real.cos (x.1 / Real.sqrt 2) : ℂ),
        (Real.sin (x.1 / Real.sqrt 2) : ℂ) * complexCoordinates x.2.val 0,
        (Real.sin (x.1 / Real.sqrt 2) : ℂ) * complexCoordinates x.2.val 1] : Fin 3 → ℂ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.continuous.comp hf

theorem complexProjectivePolar_continuous :
    Continuous (fun x : ℝ × Directions => complexProjectivePolar x.1 x.2) := by
  apply complexProjectiveEvaluation_isEmbedding.continuous_iff.mpr
  apply continuous_pi
  intro p
  change Continuous (fun x : ℝ × Directions => cp2Overlap p (complexProjectivePolar x.1 x.2))
  have heq (x : ℝ × Directions) : cp2Overlap p (complexProjectivePolar x.1 x.2) =
      ‖inner ℂ (cp2UnitRep p) (complexPolarLift x.1 x.2)‖ :=
    cp2Overlap_of_unit_representatives _ _ _ _ (cp2UnitRep_ne_zero p)
      (complexPolarLift_ne_zero x.1 x.2) (cp2UnitRep_norm p)
      (complexPolarLift_norm x.1 x.2) (cp2UnitRep_mk p) rfl
  simp_rw [heq]
  exact (continuous_const.inner complexPolarLift_continuous).norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential factors through the projective polar quotient.
The resulting map is surjective. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section

structure ComplexProjectivePolarData (p : ComplexProjective2) where
  time : ℝ
  time_mem : time ∈ Icc (0 : ℝ) complexJacobiRadius
  direction : Directions
  point_eq : complexProjectivePolar time direction = p

def complexProjectivePolarData (p : ComplexProjective2) : ComplexProjectivePolarData p := by
  exact Classical.choice (by
    obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
    exact ⟨⟨t,ht,q,hq⟩⟩)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def actualComplexProjectiveMap (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (p : ComplexProjective2) : M :=
  let D := complexProjectivePolarData p
  frameExponential g o e (D.time • D.direction.val)

theorem frameExponential_eq_of_projective_polar_eq (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius)
    (hs : s ∈ Icc (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar s p) :
    frameExponential g o e (t • q.val) = frameExponential g o e (s • p.val) := by
  have hts := complexProjectivePolar_radius_eq ht hs q p heq
  subst s
  by_cases h0 : t = 0
  · simp [h0]
  by_cases hR : t = complexJacobiRadius
  · subst t
    obtain ⟨r,hr⟩ := complexProjectivePolar_boundary_circle q p heq
    rw [hr]
    symm
    simpa only [hstd] using frameExponential_complex_boundary_circle
      hRic hminus hnorm w hstar hw hz e he q r
  · have hqp := complexProjectivePolar_interior_injective
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 hR⟩ q p heq
    rw [hqp]

theorem actualComplexProjectiveMap_polar (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    actualComplexProjectiveMap g o e (complexProjectivePolar t q) =
      frameExponential g o e (t • q.val) := by
  let D := complexProjectivePolarData (complexProjectivePolar t q)
  exact frameExponential_eq_of_projective_polar_eq hRic hminus hnorm w hstar hw hz
    e he hstd D.time_mem ht D.direction q D.point_eq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the actual affine logarithm, including its removable
singularity at the affine origin. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem complexAffineLog_zero : complexAffineLog 0 = 0 := by
  simp [complexAffineLog,complexAffineRadius]

theorem complexAffineRadius_continuous : Continuous complexAffineRadius :=
  continuous_const.mul (Real.continuous_arctan.comp continuous_norm)

theorem complexAffineLog_continuous : Continuous complexAffineLog := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    change Tendsto complexAffineLog (𝓝 0) (𝓝 (complexAffineLog 0))
    rw [complexAffineLog_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hfun : (fun z => ‖complexAffineLog z‖) = complexAffineRadius :=
      funext complexAffineLog_norm
    rw [hfun]
    convert complexAffineRadius_continuous.tendsto 0 using 1
    simp [complexAffineRadius]
  · exact (complexAffineRadius_continuous.continuousAt.div continuous_norm.continuousAt
      (norm_ne_zero_iff.mpr hz)).smul complexCoordinates.symm.continuous.continuousAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the Fubini--Study distance in the projective overlap topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section
attribute [local instance] complexProjectiveTopology

theorem fubiniStudyDistance_left_continuous (P : ComplexProjective2) :
    Continuous (fubiniStudyDistance P) := by
  have h : Continuous (fun Q : ComplexProjective2 => cp2Overlap P Q) :=
    (continuous_apply P).comp complexProjectiveEvaluation_isEmbedding.continuous
  change Continuous (fun Q => fubiniStudyDistance P Q)
  simp_rw [fubiniStudyDistance_eq_arccos]
  exact Real.continuous_arccos.comp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial and complex-radial real components are the real and
imaginary parts of the Hermitian inner product. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexCoordinates_inner_re (u v : FourSpace) :
    (inner ℂ (complexCoordinates u) (complexCoordinates v)).re = inner ℝ u v := by
  change RCLike.re (inner ℂ (complexCoordinates u) (complexCoordinates v)) = inner ℝ u v
  rw [← real_inner_eq_re_inner ℂ]
  exact complexCoordinates.inner_map_map u v

theorem complexCoordinates_inner_im (q : Angular.Directions) (v : FourSpace) :
    (inner ℂ (complexCoordinates q.val) (complexCoordinates v)).im =
      inner ℝ (complexCompanion q) v := by
  have h := complexCoordinates_inner_re (complexCompanion q) v
  rw [complexCoordinates_companion,inner_smul_left] at h
  simpa using h

theorem complexCoordinates_inner_norm_sq (q : Angular.Directions) (v : FourSpace) :
    ‖inner ℂ (complexCoordinates q.val) (complexCoordinates v)‖ ^ 2 =
      (inner ℝ q.val v)^2 + (inner ℝ (complexCompanion q) v)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply,complexCoordinates_inner_re,complexCoordinates_inner_im]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact polar parametrization is a genuine quotient onto CP2. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

abbrev ComplexPolarDomain := Icc (0 : ℝ) complexJacobiRadius × Directions

def complexPolarProjection (p : ComplexPolarDomain) : ComplexProjective2 :=
  complexProjectivePolar p.1.val p.2

theorem complexPolarProjection_surjective : Function.Surjective complexPolarProjection := by
  intro p
  obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
  exact ⟨(⟨t,ht⟩,q),hq⟩

theorem complexPolarProjection_continuous : Continuous complexPolarProjection := by
  have ht : Continuous (fun p : ComplexPolarDomain => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hq : Continuous (fun p : ComplexPolarDomain => p.2) := continuous_snd
  have hpair : Continuous (fun p : ComplexPolarDomain => (p.1.val,p.2)) := ht.prodMk hq
  change Continuous ((fun x : ℝ × Directions => complexProjectivePolar x.1 x.2) ∘
    (fun p : ComplexPolarDomain => (p.1.val,p.2)))
  exact Continuous.comp complexProjectivePolar_continuous hpair

theorem complexPolarProjection_isQuotientMap : Topology.IsQuotientMap complexPolarProjection := by
  exact Topology.IsQuotientMap.of_surjective_continuous
    complexPolarProjection_surjective complexPolarProjection_continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual globally defined projective map covers the manifold and
preserves all radial distances at the Ricci-three scale. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_radial (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    metricDistance g e.base (actualComplexProjectiveMap g o e (complexProjectivePolar t q)) = t := by
  have hn : ‖t • q.val‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,q.property,mul_one]
  rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
    w hstar hw hz e he hstd t ht q,
    frameExponential_complex_minimizing hRic hminus hdim e he _ (by rw [hn]; exact ht.2),hn]

theorem actualComplexProjectiveMap_surjective (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm) :
    Function.Surjective (actualComplexProjectiveMap g o e) := by
  intro x
  have hx : x ∈ frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius := by
    rw [frameExponential_complex_closedBall_image hRic hminus hdim e he]
    trivial
  obtain ⟨v,hv,hx⟩ := hx
  have hvr : ‖v‖ ≤ complexJacobiRadius := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  by_cases h0 : v = 0
  · refine ⟨complexProjectivePolar 0 firstDirection,?_⟩
    rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd 0 ⟨le_rfl,complexJacobiRadius_pos.le⟩ firstDirection,zero_smul]
    simpa only [h0] using hx
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0),one_smul]
  refine ⟨complexProjectivePolar ‖v‖ q,?_⟩
  rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
    w hstar hw hz e he hstd ‖v‖ ⟨norm_nonneg _,hvr⟩ q,hq]
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit homogeneous differential of the projective polar map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexCoordinates_linear_norm_sq (q : Directions) (v : FourSpace) (a b : ℝ) :
    ‖a • complexCoordinates q.val + b • complexCoordinates v‖ ^ 2 =
      a^2 + 2*a*b*inner ℝ q.val v + b^2*‖v‖^2 := by
  rw [norm_add_sq_real,norm_smul,norm_smul,real_inner_smul_left,real_inner_smul_right,
    complexCoordinates.inner_map_map,complexCoordinates.norm_map,complexCoordinates.norm_map,q.property]
  simp only [Real.norm_eq_abs,mul_pow,sq_abs,mul_one]
  ring

def complexPolarLiftDifferential (t : ℝ) (q : Directions) (v : FourSpace) : CP2Vector :=
  let x := inner ℝ q.val v
  let a := (Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * x
  let b := Real.sin (t / Real.sqrt 2) / t
  complexHeadTail ((-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * x : ℝ) : ℂ)
    (a • complexCoordinates q.val + b • complexCoordinates v)

theorem complexPolarLiftDifferential_norm_sq (t : ℝ) (q : Directions) (v : FourSpace) :
    ‖complexPolarLiftDifferential t q v‖ ^ 2 =
      (-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * inner ℝ q.val v)^2 +
      ((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * inner ℝ q.val v)^2 +
      2*((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * inner ℝ q.val v)*
        (Real.sin (t / Real.sqrt 2) / t)*inner ℝ q.val v +
      (Real.sin (t / Real.sqrt 2) / t)^2*‖v‖^2 := by
  rw [complexPolarLiftDifferential,complexHeadTail_norm_sq,complexCoordinates_linear_norm_sq,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the genuine projective map, including its boundary fibers. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_continuous (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm) :
    Continuous (actualComplexProjectiveMap g o e) := by
  apply complexPolarProjection_isQuotientMap.continuous_iff.mpr
  have heq : actualComplexProjectiveMap g o e ∘ complexPolarProjection =
      fun p : ComplexPolarDomain => frameExponential g o e (p.1.val • p.2.val) := by
    funext p
    exact actualComplexProjectiveMap_polar hRic hminus
      (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
      p.1.val p.1.property p.2
  rw [heq]
  exact (frameExponential_continuous g o e).comp
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact radial distance and uniqueness of the actual projective map
away from the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_from_center (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (p : ComplexProjective2) :
    metricDistance g e.base (actualComplexProjectiveMap g o e p) =
      Real.sqrt 2 * fubiniStudyDistance complexProjectiveNorth p := by
  obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
  rw [← hq,actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd t ht q,
    fubiniStudyDistance_north_polar t ht q]
  field_simp

theorem actualComplexProjectiveMap_fiber_eq_of_radial_lt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (p q : ComplexProjective2)
    (heq : actualComplexProjectiveMap g o e p = actualComplexProjectiveMap g o e q)
    (hlt : metricDistance g e.base (actualComplexProjectiveMap g o e p) < complexJacobiRadius) :
    p = q := by
  obtain ⟨t,ht,u,hp⟩ := complexProjectivePolar_surjective p
  obtain ⟨s,hs,v,hq⟩ := complexProjectivePolar_surjective q
  have hpt := actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd t ht u
  have hqs := actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd s hs v
  rw [hp] at hpt
  rw [hq] at hqs
  have hts : t = s := hpt.symm.trans ((congrArg (metricDistance g e.base) heq).trans hqs)
  rw [← hts] at hs hq
  have htR : t < complexJacobiRadius := hpt ▸ hlt
  by_cases ht0 : t = 0
  · rw [← hp,← hq,ht0,complexProjectivePolar_zero,complexProjectivePolar_zero]
  have heq' : frameExponential g o e (t • u.val) = frameExponential g o e (t • v.val) := by
    rw [← actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd t ht u,
      ← actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd t hs v,hp,hq]
    exact heq
  have huv := complex_direction_injective hRic hminus hdim e he u v t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),htR⟩ heq'
  rw [← hp,← hq,huv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The phase component of the homogeneous polar differential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexPolarLift_headTail (t : ℝ) (q : Directions) :
    complexPolarLift t q = complexHeadTail (Real.cos (t / Real.sqrt 2))
      (Real.sin (t / Real.sqrt 2) • complexCoordinates q.val) := by
  ext i
  fin_cases i <;> rfl

theorem complexPolarLiftDifferential_inner (t : ℝ) (q : Directions) (v : FourSpace) :
    inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v) =
      ((Real.sin (t / Real.sqrt 2)^2 / t * inner ℝ (complexCompanion q) v : ℝ) : ℂ) * Complex.I := by
  rw [complexPolarLift_headTail,complexPolarLiftDifferential,complexHeadTail_inner,
    inner_smul_left_eq_smul,inner_add_right,inner_smul_right_eq_smul,inner_smul_right_eq_smul,
    inner_self_eq_norm_sq_to_K,complexCoordinates.norm_map,q.property]
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,Complex.ofReal_re,Complex.ofReal_im,
      Complex.star_def,Complex.conj_ofReal,Complex.I_re,Complex.I_im,
      complexCoordinates_inner_re,complexCoordinates_inner_im] <;> norm_num <;> ring

theorem complexPolarLiftDifferential_inner_norm_sq (t : ℝ) (q : Directions) (v : FourSpace) :
    ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2 =
      (Real.sin (t / Real.sqrt 2)^2 / t)^2 * (inner ℝ (complexCompanion q) v)^2 := by
  rw [complexPolarLiftDifferential_inner,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine projective map in the ordinary affine chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_affine (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (z : EuclideanSpace ℂ (Fin 2)) :
    actualComplexProjectiveMap g o e (complexAffinePoint z) =
      frameExponential g o e (complexAffineLog z) := by
  obtain ⟨q,hq,hlog⟩ := complexAffinePoint_polar_log z
  rw [← hq,actualComplexProjectiveMap_polar hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
    (complexAffineRadius z) ⟨(complexAffineRadius_mem z).1,(complexAffineRadius_mem z).2.le⟩ q,hlog]

theorem actualComplexProjectiveMap_affine_continuous (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    : Continuous (fun z : EuclideanSpace ℂ (Fin 2) =>
      actualComplexProjectiveMap g o e (complexAffinePoint z)) := by
  have heq : (fun z : EuclideanSpace ℂ (Fin 2) => actualComplexProjectiveMap g o e (complexAffinePoint z)) =
      fun z => frameExponential g o e (complexAffineLog z) :=
    funext (actualComplexProjectiveMap_affine hRic hminus hdim w hstar hw hz e he hstd)
  rw [heq]
  exact (frameExponential_continuous g o e).comp complexAffineLog_continuous

theorem actualComplexProjectiveMap_affine_injective (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    : Function.Injective (fun z : EuclideanSpace ℂ (Fin 2) =>
      actualComplexProjectiveMap g o e (complexAffinePoint z)) := by
  intro z y hzy
  apply complexAffinePoint_injective
  apply actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim w hstar hw hz e he hstd _ _ hzy
  rw [actualComplexProjectiveMap_affine hRic hminus hdim w hstar hw hz e he hstd,
    frameExponential_complex_minimizing hRic hminus hdim e he _
      (by rw [complexAffineLog_norm]; exact (complexAffineRadius_mem z).2.le),complexAffineLog_norm]
  exact (complexAffineRadius_mem z).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The homogeneous lift of the actual normal-coordinate projective map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

def complexNormalLift (v : FourSpace) : CP2Vector :=
  complexHeadTail (Real.cos (‖v‖ / Real.sqrt 2))
    ((Real.sin (‖v‖ / Real.sqrt 2) / ‖v‖) • complexCoordinates v)

theorem complexNormalLift_radial (t : ℝ) (ht : 0 < t) (q : Directions) :
    complexNormalLift (t • q.val) = complexPolarLift t q := by
  have hn : ‖t • q.val‖ = t := by rw [norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  rw [complexNormalLift,hn,complexPolarLift_headTail,map_smul,smul_smul,
    div_mul_cancel₀ _ ht.ne']

theorem hasDerivAt_norm_radial {c : ℝ → FourSpace} {v : FourSpace} {s t : ℝ}
    (hc : HasDerivAt c v s) (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    HasDerivAt (fun r => ‖c r‖) (inner ℝ q.val v) s := by
  have hn : ‖c s‖ = t := by rw [hcs,norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  have hd := hc.norm_sq.sqrt (by rw [hn]; positivity)
  have hfun : (fun r => Real.sqrt (‖c r‖ ^ 2)) = fun r => ‖c r‖ := by
    funext r
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun,Real.sqrt_sq (norm_nonneg _),hn,hcs,real_inner_smul_left] at hd
  convert hd using 1
  field_simp

theorem complexHeadTail_hasDerivAt {a : ℝ → ℂ} {b : ℝ → EuclideanSpace ℂ (Fin 2)}
    {a' : ℂ} {b' : EuclideanSpace ℂ (Fin 2)} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun r => complexHeadTail (a r) (b r)) (complexHeadTail a' b') s := by
  have hb' := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s hb
  have hp : HasDerivAt (fun r => (![a r,b r 0,b r 1] : Fin 3 → ℂ))
      (![a',b' 0,b' 1] : Fin 3 → ℂ) s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hasDerivAt_pi.mp hb' 0
    · exact hasDerivAt_pi.mp hb' 1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The horizontal homogeneous metric agrees with the actual two-frequency
normal metric. The normalization is Ricci equal to three times the metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complex_projective_differential_gram (t : ℝ) (q : Directions) (v : FourSpace) :
    2 * (‖complexPolarLiftDifferential t q v‖^2 -
      ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2) =
        (complexJacobiSlow t / t)^2 * ‖v‖^2 +
          (1-(complexJacobiSlow t / t)^2)*(inner ℝ q.val v)^2 +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*
            (inner ℝ (complexCompanion q) v)^2 := by
  have hA : (complexJacobiSlow t / t)^2 = 2*(Real.sin (t / Real.sqrt 2)/t)^2 := by
    rw [div_pow,complexJacobiSlow_sq]
    ring
  have hB : (complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2 =
      -2*(Real.sin (t / Real.sqrt 2)^2/t)^2 := by
    rw [div_pow,div_pow,← sub_div,complexJacobiFast_sq_sub_slow_sq]
    ring
  rw [complexPolarLiftDifferential_norm_sq,complexPolarLiftDifferential_inner_norm_sq,hB,hA]
  have hroot : (Real.sqrt 2)⁻¹^2 = (1/2 : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    _ = 2 * ((Real.sqrt 2)⁻¹^2 *
        (Real.sin (t / Real.sqrt 2)^2 + Real.cos (t / Real.sqrt 2)^2) * (inner ℝ q.val v)^2 -
        (Real.sin (t / Real.sqrt 2)/t)^2 * (inner ℝ q.val v)^2 +
        (Real.sin (t / Real.sqrt 2)/t)^2 * ‖v‖^2 -
        (Real.sin (t / Real.sqrt 2)^2/t)^2 * (inner ℝ (complexCompanion q) v)^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq,hroot]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation of the homogeneous normal lift along actual curves. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexNormalLift_hasDerivAt {c : ℝ → FourSpace} {v : FourSpace} {s t : ℝ}
    (hc : HasDerivAt c v s) (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    HasDerivAt (fun r => complexNormalLift (c r)) (complexPolarLiftDifferential t q v) s := by
  have hn := hasDerivAt_norm_radial hc ht q hcs
  have hnval : ‖c s‖ = t := by
    rw [hcs,norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  have hroot : Real.sqrt 2 ≠ 0 := by positivity
  have htheta := hn.div_const (Real.sqrt 2)
  have hcoef : HasDerivAt (fun r => Real.sin (‖c r‖ / Real.sqrt 2) / ‖c r‖)
      (((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) / t) *
        inner ℝ q.val v) s := by
    have hd := htheta.sin.div hn (by rw [hnval]; exact ht.ne')
    rw [hnval] at hd
    convert hd using 1
    field_simp
  have hcoordinates : HasDerivAt (fun r => complexCoordinates (c r)) (complexCoordinates v) s :=
    complexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hc
  have htail := hcoef.smul hcoordinates
  have htail' : HasDerivAt
      (fun r => (Real.sin (‖c r‖ / Real.sqrt 2) / ‖c r‖) • complexCoordinates (c r))
      (((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) *
          inner ℝ q.val v) • complexCoordinates q.val +
        (Real.sin (t / Real.sqrt 2) / t) • complexCoordinates v) s := by
    convert htail using 1
    rw [hnval,hcs,map_smul,smul_smul,add_comm]
    congr 1
    field_simp
  have hhead := htheta.cos.ofReal_comp
  have hhead' : HasDerivAt (fun r => (Real.cos (‖c r‖ / Real.sqrt 2) : ℂ))
      ((-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * inner ℝ q.val v : ℝ) : ℂ) s := by
    convert hhead using 1
    rw [hnval]
    congr 1
    ring
  exact complexHeadTail_hasDerivAt hhead' htail'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality between the genuine metric and the horizontal homogeneous metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_metric_eq_horizontal (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (q : Directions) (t : ℝ) (ht : 0 < t) (v : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) v)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) v) =
        2 * (‖complexPolarLiftDifferential t q v‖^2 -
          ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2) := by
  rw [frameExponential_complex_pairing hRic hminus hnorm W hstar hw hz e he hstd q t ht,
    complex_projective_differential_gram,real_inner_self_eq_norm_sq]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal homogeneous lift represents the actual projective quotient map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section

theorem complexNormalLift_norm (v : FourSpace) : ‖complexNormalLift v‖ = 1 := by
  by_cases hv : v = 0
  · subst v
    simp [complexNormalLift,complexHeadTail,EuclideanSpace.norm_eq,Fin.sum_univ_three]
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have hrad : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
    rw [← hrad,complexNormalLift_radial ‖v‖ (norm_pos_iff.mpr hv),complexPolarLift_norm]

theorem complexNormalLift_ne_zero (v : FourSpace) : complexNormalLift v ≠ 0 := by
  intro h
  have hn := complexNormalLift_norm v
  rw [h,norm_zero] at hn
  exact zero_ne_one hn

def complexNormalPoint (v : FourSpace) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexNormalLift v) (complexNormalLift_ne_zero v)

theorem complexNormalPoint_radial (t : ℝ) (ht : 0 < t) (q : Directions) :
    complexNormalPoint (t • q.val) = complexProjectivePolar t q := by
  simp only [complexNormalPoint,complexProjectivePolar,complexNormalLift_radial t ht q]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_normal (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (v : FourSpace) (hv : v ≠ 0) (hr : ‖v‖ ≤ complexJacobiRadius) :
    actualComplexProjectiveMap g o e (complexNormalPoint v) = frameExponential g o e v := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  rw [← hrad,complexNormalPoint_radial ‖v‖ (norm_pos_iff.mpr hv)]
  exact actualComplexProjectiveMap_polar hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
    ‖v‖ ⟨norm_nonneg _,hr⟩ q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The speed of the actual exponential curve in homogeneous coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_curve_speed (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {c : ℝ → FourSpace} {s t : ℝ} (hc : DifferentiableAt ℝ c s)
    (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    Real.sqrt 2 * Real.sqrt (‖deriv (fun r => complexNormalLift (c r)) s‖^2 -
      ‖inner ℂ (complexNormalLift (c s)) (deriv (fun r => complexNormalLift (c r)) s)‖^2) =
        metricTangentNorm g (frameExponential g o e (c s))
          (mfderiv 𝓘(ℝ, ℝ) I4 (fun r => frameExponential g o e (c r)) s 1) := by
  have hlift := complexNormalLift_hasDerivAt hc.hasDerivAt ht q hcs
  have hm := mfderiv_comp s
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (c s)) hc.mdifferentiableAt
  have hDc : mfderiv 𝓘(ℝ, ℝ) I4 c s 1 = deriv c s := by
    simpa only [mfderiv_eq_fderiv] using! (fderiv_apply_one_eq_deriv (f := c) (x := s))
  have hD : mfderiv 𝓘(ℝ, ℝ) I4 (fun r => frameExponential g o e (c r)) s 1 =
      mfderiv I4 I4 (frameExponential g o e) (c s) (deriv c s) := by
    have h := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hm
    exact h.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (c s)) hDc)
  rw [hD,metricTangentNorm_eq_sqrt,hlift.deriv]
  let v : FourSpace := deriv c s
  change Real.sqrt 2 * Real.sqrt (‖complexPolarLiftDifferential t q v‖^2 -
    ‖inner ℂ (complexNormalLift (c s)) (complexPolarLiftDifferential t q v)‖^2) =
    Real.sqrt (g.inner (frameExponential g o e (c s))
      (mfderiv I4 I4 (frameExponential g o e) (c s) v)
      (mfderiv I4 I4 (frameExponential g o e) (c s) v))
  rw [hcs,complexNormalLift_radial t ht q,
    frameExponential_complex_metric_eq_horizontal hRic hminus hnorm W hstar hw hz e he hstd q t ht,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine logarithm is differentiable away from its center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complexAffineRadius_pos {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    0 < complexAffineRadius z :=
  mul_pos (by positivity) (Real.arctan_pos.mpr (norm_pos_iff.mpr hz))

theorem complexAffineLog_ne_zero {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    complexAffineLog z ≠ 0 := by
  apply norm_pos_iff.mp
  rw [complexAffineLog_norm]
  exact complexAffineRadius_pos hz

theorem complexAffineLog_differentiableAt {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    DifferentiableAt ℝ complexAffineLog z := by
  have hn : DifferentiableAt ℝ (fun z : EuclideanSpace ℂ (Fin 2) => ‖z‖) z :=
    (differentiableAt_id : DifferentiableAt ℝ (fun w : EuclideanSpace ℂ (Fin 2) => w) z).norm ℝ hz
  have hr : DifferentiableAt ℝ complexAffineRadius z := hn.arctan.const_mul (Real.sqrt 2)
  have hq : DifferentiableAt ℝ (fun w => complexAffineRadius w / ‖w‖) z :=
    by simpa only [Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv] using!
      hr.mul (hn.inv (norm_ne_zero_iff.mpr hz))
  have hlin : DifferentiableAt ℝ (fun w => complexCoordinates.symm w) z :=
    complexCoordinates.symm.toContinuousLinearEquiv.differentiableAt
  exact hq.smul hlin

theorem complexNormalPoint_affineLog {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    complexNormalPoint (complexAffineLog z) = complexAffinePoint z := by
  obtain ⟨q,hq,hlog⟩ := complexAffinePoint_polar_log z
  rw [← hlog,complexNormalPoint_radial _ (complexAffineRadius_pos hz),hq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal projection and the phase-invariant projective speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexHorizontalPart (u v : CP2Vector) : CP2Vector := v - (inner ℂ u v) • u

theorem complexHorizontalPart_orthogonal (u v : CP2Vector) (hu : ‖u‖ = 1) :
    inner ℂ u (complexHorizontalPart u v) = 0 := by
  simp [complexHorizontalPart,inner_self_eq_norm_sq_to_K,hu]

theorem complexHorizontalPart_norm_sq (u v : CP2Vector) (hu : ‖u‖ = 1) :
    ‖complexHorizontalPart u v‖^2 = ‖v‖^2 - ‖inner ℂ u v‖^2 := by
  have hsum : (inner ℂ u v) • u + complexHorizontalPart u v = v := by
    dsimp [complexHorizontalPart]
    abel
  have hn := norm_add_sq (𝕜 := ℂ) ((inner ℂ u v) • u) (complexHorizontalPart u v)
  rw [hsum,inner_smul_left,complexHorizontalPart_orthogonal u v hu,mul_zero] at hn
  simp only [map_zero,mul_zero,add_zero,norm_smul,hu,mul_one] at hn
  linarith

theorem complexHorizontalPart_phase (u v : CP2Vector) (hu : ‖u‖ = 1)
    (a b : ℂ) (ha : ‖a‖ = 1) :
    complexHorizontalPart (a • u) (b • u + a • v) = a • complexHorizontalPart u v := by
  have haa : star a * a = 1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',ha]
    norm_num
  have hi : inner ℂ (a • u) (b • u + a • v) = star a * b + inner ℂ u v := by
    simp only [inner_smul_left,inner_add_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hu]
    norm_num only [RCLike.ofReal_one,one_pow,mul_one]
    simp only [starRingEnd_apply]
    calc
      _ = star a * b + (star a * a) * inner ℂ u v := by ring
      _ = _ := by rw [haa,one_mul]
  have hs : (star a * b + inner ℂ u v) * a = b + a * inner ℂ u v := by
    calc
      _ = (star a * a) * b + a * inner ℂ u v := by ring
      _ = _ := by rw [haa,one_mul]
  rw [complexHorizontalPart,hi,smul_smul,hs]
  dsimp [complexHorizontalPart]
  module

theorem complexHorizontalPart_phase_norm (u v : CP2Vector) (hu : ‖u‖ = 1)
    (a b : ℂ) (ha : ‖a‖ = 1) :
    ‖complexHorizontalPart (a • u) (b • u + a • v)‖ = ‖complexHorizontalPart u v‖ := by
  rw [complexHorizontalPart_phase u v hu a b ha,norm_smul,ha,one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal great circles of unit homogeneous representatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexGreatCircle (p q : CP2Vector) (t : ℝ) : CP2Vector :=
  Real.cos t • p + Real.sin t • q

def complexGreatCircleVelocity (p q : CP2Vector) (t : ℝ) : CP2Vector :=
  -Real.sin t • p + Real.cos t • q

theorem complexGreatCircle_hasDerivAt (p q : CP2Vector) (t : ℝ) :
    HasDerivAt (complexGreatCircle p q) (complexGreatCircleVelocity p q t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const p).add ((Real.hasDerivAt_sin t).smul_const q)

theorem complexGreatCircle_norm (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : ‖complexGreatCircle p q t‖ = 1 := by
  have hr : inner ℝ p q = 0 := by
    simpa only [Complex.zero_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hpq
  have hs : ‖complexGreatCircle p q t‖^2 = 1 := by
    rw [complexGreatCircle,norm_add_sq_real,norm_smul,norm_smul,
      real_inner_smul_left,real_inner_smul_right,hr,hp,hq]
    simp only [Real.norm_eq_abs,mul_one,mul_zero,add_zero,sq_abs]
    exact Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (complexGreatCircle p q t)]

theorem complexGreatCircleVelocity_norm (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : ‖complexGreatCircleVelocity p q t‖ = 1 := by
  have hr : inner ℝ p q = 0 := by
    simpa only [Complex.zero_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hpq
  have hs : ‖complexGreatCircleVelocity p q t‖^2 = 1 := by
    rw [complexGreatCircleVelocity,norm_add_sq_real,norm_smul,norm_smul,
      real_inner_smul_left,real_inner_smul_right,hr,hp,hq]
    simp only [Real.norm_eq_abs,mul_one,mul_zero,add_zero,abs_neg,sq_abs]
    exact Real.sin_sq_add_cos_sq t
  nlinarith [norm_nonneg (complexGreatCircleVelocity p q t)]

theorem complexGreatCircle_horizontal (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) :
    inner ℂ (complexGreatCircle p q t) (complexGreatCircleVelocity p q t) = 0 := by
  have hqp : inner ℂ q p = 0 := by rw [← inner_conj_symm,hpq]; simp
  simp only [complexGreatCircle,complexGreatCircleVelocity,inner_add_left,inner_add_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,inner_self_eq_norm_sq_to_K,hp,hq,hpq,hqp]
  norm_num
  ring

theorem complexGreatCircle_horizontal_speed (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) :
    ‖complexHorizontalPart (complexGreatCircle p q t) (complexGreatCircleVelocity p q t)‖ = 1 := by
  rw [complexHorizontalPart,complexGreatCircle_horizontal p q hp hq hpq,zero_smul,sub_zero,
    complexGreatCircleVelocity_norm p q hp hq hpq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Horizontal speed is independent of a differentiable unit lift. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem complex_unit_aligned_coefficient (u w : CP2Vector) (hu : ‖u‖ = 1)
    (heq : ∃ a : ℂ, w = a • u) :
    w = (inner ℂ u w) • u := by
  obtain ⟨a,rfl⟩ := heq
  simp [inner_self_eq_norm_sq_to_K,hu]

theorem complexHorizontalPart_curve_invariant {u w : ℝ → CP2Vector}
    {u' w' : CP2Vector} {s : ℝ}
    (hu : ∀ r, ‖u r‖ = 1) (hw : ∀ r, ‖w r‖ = 1)
    (heq : ∀ᶠ r in 𝓝 s, ∃ a : ℂ, w r = a • u r)
    (hdu : HasDerivAt u u' s) (hdw : HasDerivAt w w' s) :
    ‖complexHorizontalPart (w s) w'‖ = ‖complexHorizontalPart (u s) u'‖ := by
  let a : ℝ → ℂ := fun r => inner ℂ (u r) (w r)
  have halign : ∀ᶠ r in 𝓝 s, w r = a r • u r := by
    filter_upwards [heq] with r hr
    exact complex_unit_aligned_coefficient (u r) (w r) (hu r) hr
  have ha : ‖a s‖ = 1 := by
    have h := hw s
    rw [halign.self_of_nhds,norm_smul,hu s,mul_one] at h
    exact h
  let b : ℂ := inner ℂ (u s) w' + inner ℂ u' (w s)
  have hda : HasDerivAt a b s := hdu.inner ℂ hdw
  have hd : HasDerivAt (fun r => a r • u r) (a s • u' + b • u s) s := hda.smul hdu
  have hv : w' = b • u s + a s • u' :=
    (hdw.unique (hd.congr_of_eventuallyEq halign)).trans (add_comm _ _)
  calc
    _ = ‖complexHorizontalPart (a s • u s) (b • u s + a s • u')‖ := by
      congr 2
      · exact halign.self_of_nhds
    _ = _ := complexHorizontalPart_phase_norm (u s) u' (hu s) (a s) b ha

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cauchy--Schwarz for the horizontal part of a projective velocity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_real_inner_mul_self (z a : ℂ) :
    inner ℝ z (a*z) = ‖z‖^2 * a.re := by
  change ((a*z)*star z).re = _
  rw [mul_assoc,Complex.star_def,Complex.mul_conj',← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

theorem complexHorizontalPairing (p u w : CP2Vector)
    (hw : (inner ℂ u w).re = 0) :
    inner ℝ (inner ℂ p u) (inner ℂ p w) =
      inner ℝ (inner ℂ p u) (inner ℂ p (complexHorizontalPart u w)) := by
  have hdec : inner ℂ p w = (inner ℂ u w) * inner ℂ p u +
      inner ℂ p (complexHorizontalPart u w) := by
    simp only [complexHorizontalPart,inner_sub_right,inner_smul_right]
    ring
  rw [hdec,inner_add_right,complex_real_inner_mul_self,hw,mul_zero,zero_add]

theorem complex_horizontal_inner_bound (p u w : CP2Vector) (hu : ‖u‖ = 1) :
    ‖inner ℂ p (complexHorizontalPart u w)‖ ≤
      ‖complexHorizontalPart u p‖ * ‖complexHorizontalPart u w‖ := by
  have heq : inner ℂ (complexHorizontalPart u p) (complexHorizontalPart u w) =
      inner ℂ p (complexHorizontalPart u w) := by
    rw [complexHorizontalPart,inner_sub_left,inner_smul_left,
      complexHorizontalPart_orthogonal u w hu,mul_zero,sub_zero]
  rw [← heq]
  exact norm_inner_le_norm _ _

theorem complex_unit_curve_tangent {u : ℝ → UnitSphere CP2Vector} {t : ℝ}
    {w : CP2Vector} (hd : HasDerivAt (fun s => (u s).val) w t) :
    (inner ℂ (u t).val w).re = 0 := by
  have h := hd.norm_sq
  have heq : (fun s => ‖(u s).val‖^2) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    rw [(u s).property,one_pow]
  rw [heq] at h
  have hz := h.unique (hasDerivAt_const t (1 : ℝ))
  have hr : inner ℝ (u t).val w = 0 := by linarith
  simpa only [← real_inner_eq_re_inner ℂ] using! hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Affine coordinates of an actual homogeneous vector and their regularity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexTailLinear : CP2Vector →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun v := WithLp.toLp 2 ![v 1,v 2]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def complexTailCLM : CP2Vector →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  complexTailLinear.toContinuousLinearMap

def complexVectorAffine (v : CP2Vector) : EuclideanSpace ℂ (Fin 2) :=
  (v 0)⁻¹ • complexTailCLM v

theorem complexVectorAffine_differentiableAt {v : CP2Vector} (hv : v 0 ≠ 0) :
    DifferentiableAt ℝ complexVectorAffine v := by
  have hh : DifferentiableAt ℝ (fun u : CP2Vector => u 0) v :=
    ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 => ℂ) 0).restrictScalars ℝ).differentiableAt
  exact (hh.inv hv).smul (complexTailCLM.restrictScalars ℝ).differentiableAt

theorem complexAffinePoint_vector (v : CP2Vector) (hv : v 0 ≠ 0) (hv0 : v ≠ 0) :
    complexAffinePoint (complexVectorAffine v) = Projectivization.mk ℂ v hv0 := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(v 0)⁻¹,?_⟩
  ext i
  fin_cases i
  · change (v 0)⁻¹ * v 0 = 1
    exact inv_mul_cancel₀ hv
  · rfl
  · rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! C1 regularity of the affine logarithm used for projective paths. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexAffineLog_contDiffAt {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 complexAffineLog z := by
  have hn : ContDiffAt ℝ 1 (fun w : EuclideanSpace ℂ (Fin 2) => ‖w‖) z :=
    contDiffAt_norm ℝ hz
  have hr : ContDiffAt ℝ 1 complexAffineRadius z := contDiffAt_const.mul hn.arctan
  have hq : ContDiffAt ℝ 1 (fun w => complexAffineRadius w / ‖w‖) z := by
    simpa only [Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv] using!
      hr.mul (hn.inv (norm_ne_zero_iff.mpr hz))
  have hl : ContDiffAt ℝ 1 (fun w => complexCoordinates.symm w) z :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.contDiffAt
  exact hq.smul hl

theorem complexVectorAffine_contDiffAt {v : CP2Vector} (hv : v 0 ≠ 0) :
    ContDiffAt ℝ 1 complexVectorAffine v := by
  have hh : ContDiffAt ℝ 1 (fun u : CP2Vector => u 0) v :=
    ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 => ℂ) 0).restrictScalars ℝ).contDiff.contDiffAt
  have ht : ContDiffAt ℝ 1 (fun u => complexTailCLM u) v :=
    (complexTailCLM.restrictScalars ℝ).contDiff.contDiffAt
  exact (hh.inv hv).smul ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit-sphere representatives of the horizontal projective great circles. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexGreatCircleUnit (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (t : ℝ) : UnitSphere CP2Vector :=
  ⟨complexGreatCircle p q t,complexGreatCircle_norm p q hp hq hpq t⟩

theorem complexGreatCircle_contDiff (p q : CP2Vector) : ContDiff ℝ 1 (complexGreatCircle p q) := by
  unfold complexGreatCircle
  fun_prop

theorem complexGreatCircleUnit_continuous (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) : Continuous (complexGreatCircleUnit p q hp hq hpq) :=
  (complexGreatCircle_contDiff p q).continuous.subtype_mk _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit-sphere projection to the projective overlap topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section
attribute [local instance] complexProjectiveTopology

def complexSphereProjection (p : UnitSphere CP2Vector) : ComplexProjective2 :=
  Projectivization.mk ℂ p.val (unitSphere_ne_zero p)

theorem complexSphereProjection_continuous : Continuous complexSphereProjection := by
  apply complexProjectiveEvaluation_isEmbedding.continuous_iff.mpr
  apply continuous_pi
  intro p
  change Continuous (fun q : UnitSphere CP2Vector => cp2Overlap p (complexSphereProjection q))
  have heq (q : UnitSphere CP2Vector) : cp2Overlap p (complexSphereProjection q) =
      ‖inner ℂ (cp2UnitRep p) q.val‖ :=
    cp2Overlap_of_unit_representatives _ _ _ _ (cp2UnitRep_ne_zero p)
      (unitSphere_ne_zero q) (cp2UnitRep_norm p) q.property (cp2UnitRep_mk p) rfl
  simp_rw [heq]
  exact (continuous_const.inner continuous_subtype_val).norm

theorem complexSphereProjection_affine (p : UnitSphere CP2Vector) (hp : p.val 0 ≠ 0) :
    complexSphereProjection p = complexAffinePoint (complexVectorAffine p.val) := by
  exact (complexAffinePoint_vector p.val hp (unitSphere_ne_zero p)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nontrivial complex sine/cosine combination has at most one zero in a quadrant. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_trigonometric_zeros_subsingleton (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    {t : ℝ | t ∈ Ioo 0 (Real.pi/2) ∧
      (Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b = 0}.Subsingleton := by
  have hc (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi/2)) : (Real.cos t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ht.1],ht.2⟩).ne'
  have heq (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi/2))
      (hz : (Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b = 0) :
      a + (Real.tan t : ℂ)*b = 0 := by
    calc
      _ = (Real.cos t : ℂ)⁻¹ * ((Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b) := by
        rw [Real.tan_eq_sin_div_cos,Complex.ofReal_div]
        rw [mul_add,← mul_assoc,inv_mul_cancel₀ (hc t ht),one_mul]
        ring
      _ = 0 := by rw [hz,mul_zero]
  intro s hs t ht
  by_cases hb : b = 0
  · have ha := (hab.resolve_right (by simpa using hb))
    have h := heq s hs.1 hs.2
    rw [hb,mul_zero,add_zero] at h
    exact (ha h).elim
  have hdiff : ((Real.tan s : ℂ)-(Real.tan t : ℂ))*b = 0 := by
    linear_combination heq s hs.1 hs.2 - heq t ht.1 ht.2
  have htan : Real.tan s = Real.tan t := by
    have h := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hb)
    exact_mod_cast h
  exact Real.injOn_tan ⟨by linarith [hs.1.1,Real.pi_pos],hs.1.2⟩
    ⟨by linarith [ht.1.1,Real.pi_pos],ht.1.2⟩ htan

theorem complexGreatCircle_coordinate_zeros_finite (p q : CP2Vector) (i : Fin 3)
    (hi : p i ≠ 0 ∨ q i ≠ 0) :
    {t : ℝ | t ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q t i = 0}.Finite := by
  have h := (complex_trigonometric_zeros_subsingleton (p i) (q i) hi).finite
  convert h using 1
  ext t
  simp only [complexGreatCircle,PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pair of aligned projective representatives lies on an explicit horizontal circle. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_aligned_circle (p v : CP2Vector) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hc : inner ℂ p v = (c : ℂ)) :
    ∃ q : CP2Vector, ‖q‖ = 1 ∧ inner ℂ p q = 0 ∧
      complexGreatCircle p q (Real.arccos c) = v := by
  let θ := Real.arccos c
  have hcos : Real.cos θ = c := Real.cos_arccos (by linarith) hc1.le
  have hθ : θ ∈ Icc 0 (Real.pi/2) :=
    ⟨Real.arccos_nonneg c,Real.arccos_le_pi_div_two.mpr hc0⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi
    (Real.arccos_pos.mpr hc1) (by linarith [hθ.2,Real.pi_pos])
  let D : CP2Vector := v-c • p
  have hr : inner ℝ p v = c := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hc
  have hrv : inner ℝ v p = c := (real_inner_comm p v).trans hr
  have hD : ‖D‖^2 = 1-c^2 := by
    rw [norm_sub_sq_real,norm_smul,hp,hv,real_inner_smul_right,hrv]
    simp only [Real.norm_eq_abs,mul_one,sq_abs]
    ring
  have hDn : ‖D‖ = Real.sin θ := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [hcos] at ht
    nlinarith [norm_nonneg D]
  let q : CP2Vector := (Real.sin θ)⁻¹ • D
  have hq : ‖q‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hsin.le),hDn,inv_mul_cancel₀ hsin.ne']
  have horth : inner ℂ p q = 0 := by
    change inner ℂ p ((Real.sin θ)⁻¹ • (v-c • p)) = 0
    rw [inner_smul_right_eq_smul,inner_sub_right,inner_smul_right_eq_smul,
      inner_self_eq_norm_sq_to_K,hp,hc]
    norm_num
  refine ⟨q,hq,horth,?_⟩
  change Real.cos θ • p + Real.sin θ • ((Real.sin θ)⁻¹ • (v-c • p)) = v
  rw [hcos,smul_smul,mul_inv_cancel₀ hsin.ne',one_smul]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! A projective great circle not contained in the cut hyperplane has only
finitely many exceptional affine parameters. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_orthonormal_pair_tail (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) : ∃ i : Fin 3, i ≠ 0 ∧ (p i ≠ 0 ∨ q i ≠ 0) := by
  by_cases h1 : p 1 ≠ 0 ∨ q 1 ≠ 0
  · exact ⟨1,by decide,h1⟩
  by_cases h2 : p 2 ≠ 0 ∨ q 2 ≠ 0
  · exact ⟨2,by decide,h2⟩
  have hp1 : p 1 = 0 := not_ne_iff.mp (not_or.mp h1).1
  have hq1 : q 1 = 0 := not_ne_iff.mp (not_or.mp h1).2
  have hp2 : p 2 = 0 := not_ne_iff.mp (not_or.mp h2).1
  have hq2 : q 2 = 0 := not_ne_iff.mp (not_or.mp h2).2
  have hp0 : p 0 ≠ 0 := by
    intro hz
    have h : p = 0 := by ext i; fin_cases i <;> assumption
    rw [h,norm_zero] at hp
    exact zero_ne_one hp
  have hq0 : q 0 ≠ 0 := by
    intro hz
    have h : q = 0 := by ext i; fin_cases i <;> assumption
    rw [h,norm_zero] at hq
    exact zero_ne_one hq
  have hh : q 0 * star (p 0) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three,
      Pi.star_apply,hp1,hp2,hq1,hq2] using hpq
  exact ((mul_ne_zero hq0 (star_ne_zero.mpr hp0)) hh).elim

theorem complexVectorAffine_ne_zero_of_coordinate (v : CP2Vector) (hhead : v 0 ≠ 0)
    (i : Fin 3) (hi : i ≠ 0) (hv : v i ≠ 0) : complexVectorAffine v ≠ 0 := by
  intro hz
  fin_cases i
  · exact hi rfl
  · have h := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z 0) hz
    change (v 0)⁻¹ * v 1 = 0 at h
    exact (mul_ne_zero (inv_ne_zero hhead) hv) h
  · have h := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z 1) hz
    change (v 0)⁻¹ * v 2 = 0 at h
    exact (mul_ne_zero (inv_ne_zero hhead) hv) h

theorem complexGreatCircle_regular_off_finite (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) (hhead : p 0 ≠ 0 ∨ q 0 ≠ 0) :
    ∃ E : Finset ℝ, ∀ t ∈ Ioo 0 (Real.pi/2), t ∉ E →
      complexGreatCircle p q t 0 ≠ 0 ∧ complexVectorAffine (complexGreatCircle p q t) ≠ 0 := by
  classical
  obtain ⟨i,hi,hcoord⟩ := complex_orthonormal_pair_tail p q hp hq hpq
  have h0 := complexGreatCircle_coordinate_zeros_finite p q 0 hhead
  have h1 := complexGreatCircle_coordinate_zeros_finite p q i hcoord
  refine ⟨(h0.union h1).toFinset,?_⟩
  intro t ht he
  have hn : t ∉ {s : ℝ | s ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q s 0 = 0} ∪
      {s : ℝ | s ∈ Ioo 0 (Real.pi/2) ∧ complexGreatCircle p q s i = 0} := by
    simpa only [Set.Finite.mem_toFinset] using he
  have hn0 : complexGreatCircle p q t 0 ≠ 0 := fun h => hn (Or.inl ⟨ht,h⟩)
  have hni : complexGreatCircle p q t i ≠ 0 := fun h => hn (Or.inr ⟨ht,h⟩)
  exact ⟨hn0,complexVectorAffine_ne_zero_of_coordinate _ hn0 i hi hni⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate nonvanishing and distance continuity for actual unit representatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem cp2UnitRep_coordinate_ne_zero_of_unit (u : UnitSphere CP2Vector) (i : Fin 3)
    (hi : u.val i ≠ 0) : cp2UnitRep (complexSphereProjection u) i ≠ 0 := by
  have heq : Projectivization.mk ℂ (cp2UnitRep (complexSphereProjection u))
      (cp2UnitRep_ne_zero _) = Projectivization.mk ℂ u.val (unitSphere_ne_zero u) :=
    cp2UnitRep_mk _
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at ha
    exact cp2UnitRep_ne_zero _ ha.symm
  have hai := congrArg (fun v : CP2Vector => v i) ha
  change a * u.val i = cp2UnitRep (complexSphereProjection u) i at hai
  rw [← hai]
  exact mul_ne_zero ha0 hi

theorem fubiniStudyDistance_sphere_continuous (Q : ComplexProjective2) :
    Continuous (fun u : UnitSphere CP2Vector => fubiniStudyDistance (complexSphereProjection u) Q) := by
  have heq (u : UnitSphere CP2Vector) :
      fubiniStudyDistance (complexSphereProjection u) Q =
        Real.arccos ‖inner ℂ u.val (cp2UnitRep Q)‖ := by
    rw [fubiniStudyDistance_eq_arccos]
    exact congrArg Real.arccos (cp2Overlap_of_unit_representatives
      (complexSphereProjection u) Q u.val (cp2UnitRep Q)
      (unitSphere_ne_zero u) (cp2UnitRep_ne_zero Q) u.property (cp2UnitRep_norm Q)
      rfl (cp2UnitRep_mk Q))
  simp_rw [heq]
  exact Real.continuous_arccos.comp (continuous_subtype_val.inner continuous_const).norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity everywhere and C1 regularity in regular homogeneous affine coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_unit_continuous (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) :
    Continuous (fun u : UnitSphere CP2Vector =>
      actualComplexProjectiveMap g o e (complexSphereProjection u)) :=
  (actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd).comp
    complexSphereProjection_continuous

theorem actualComplexProjectiveMap_lift_contMDiffAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {u : ℝ → UnitSphere CP2Vector} {s : ℝ}
    (hu : ContDiffAt ℝ 1 (fun r => (u r).val) s)
    (hhead : (u s).val 0 ≠ 0) (htail : complexVectorAffine (u s).val ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℝ) I4 1
      (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) s := by
  let z : ℝ → EuclideanSpace ℂ (Fin 2) := fun r => complexVectorAffine (u r).val
  let α : ℝ → FourSpace := fun r => complexAffineLog (z r)
  have hdz : ContDiffAt ℝ 1 z s := by
    exact ContDiffAt.comp (f := fun r => (u r).val) (g := complexVectorAffine) s
      (complexVectorAffine_contDiffAt hhead) hu
  have hdα : ContDiffAt ℝ 1 α s := by
    exact ContDiffAt.comp (f := z) (g := complexAffineLog) s
      (complexAffineLog_contDiffAt htail) hdz
  have hhead' : ∀ᶠ r in 𝓝 s, (u r).val 0 ≠ 0 :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0).continuousAt.comp
      hu.continuousAt).eventually_ne hhead
  have hγ : (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) =ᶠ[𝓝 s]
      (fun r => frameExponential g o e (α r)) := by
    filter_upwards [hhead'] with r hr
    rw [complexSphereProjection_affine (u r) hr]
    exact actualComplexProjectiveMap_affine hRic hminus hdim W hstar hw hz e he hstd _
  have hcmp : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 (fun r => frameExponential g o e (α r)) s :=
    (frameExponential_contMDiff g o e).contMDiffAt.comp s hdα.contMDiffAt
  exact hcmp.congr_of_eventuallyEq hγ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine projective map has the expected speed in every regular affine lift. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_lift_speed (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {u : ℝ → UnitSphere CP2Vector} {u' : CP2Vector} {s : ℝ}
    (hdu : HasDerivAt (fun r => (u r).val) u' s)
    (hhead : (u s).val 0 ≠ 0) (htail : complexVectorAffine (u s).val ≠ 0) :
    Real.sqrt 2 * ‖complexHorizontalPart (u s).val u'‖ =
      metricTangentNorm g (actualComplexProjectiveMap g o e (complexSphereProjection (u s)))
        (mfderiv 𝓘(ℝ, ℝ) I4
          (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) s 1) := by
  let z : ℝ → EuclideanSpace ℂ (Fin 2) := fun r => complexVectorAffine (u r).val
  let α : ℝ → FourSpace := fun r => complexAffineLog (z r)
  have hdz : DifferentiableAt ℝ z s := by
    exact DifferentiableAt.comp (f := fun r => (u r).val) (g := complexVectorAffine) s
      (complexVectorAffine_differentiableAt hhead) hdu.differentiableAt
  have hdα : DifferentiableAt ℝ α s := by
    exact DifferentiableAt.comp (f := z) (g := complexAffineLog) s
      (complexAffineLog_differentiableAt htail) hdz
  have hα0 : α s ≠ 0 := complexAffineLog_ne_zero htail
  let q : Directions := ⟨‖α s‖⁻¹ • α s,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hα0)]⟩
  have hrad : α s = ‖α s‖ • q.val := by
    change α s = ‖α s‖ • (‖α s‖⁻¹ • α s)
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hα0),one_smul]
  have hreg : ∀ᶠ r in 𝓝 s, (u r).val 0 ≠ 0 ∧ z r ≠ 0 := by
    have hh := ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0).continuousAt.comp
      hdu.continuousAt).eventually_ne hhead
    have ht := hdz.continuousAt.eventually_ne htail
    exact hh.and ht
  have hγ : (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) =ᶠ[𝓝 s]
      (fun r => frameExponential g o e (α r)) := by
    filter_upwards [hreg] with r hr
    rw [complexSphereProjection_affine (u r) hr.1]
    exact actualComplexProjectiveMap_affine hRic hminus hdim W hstar hw hz e he hstd _
  have halign : ∀ᶠ r in 𝓝 s, ∃ a : ℂ, complexNormalLift (α r) = a • (u r).val := by
    filter_upwards [hreg] with r hr
    have hp : complexNormalPoint (α r) = complexSphereProjection (u r) :=
      (complexNormalPoint_affineLog hr.2).trans
        (complexAffinePoint_vector (u r).val hr.1 (unitSphere_ne_zero (u r)))
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
    exact ⟨a,ha.symm⟩
  have hdlift := complexNormalLift_hasDerivAt hdα.hasDerivAt (norm_pos_iff.mpr hα0) q hrad
  have hinv := complexHorizontalPart_curve_invariant (fun r => (u r).property)
    (fun r => complexNormalLift_norm (α r)) halign hdu hdlift
  have hs := frameExponential_complex_curve_speed hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) W hstar hw hz e he hstd hdα
    (norm_pos_iff.mpr hα0) q hrad
  rw [hdlift.deriv,← complexHorizontalPart_norm_sq _ _ (complexNormalLift_norm (α s)),
    Real.sqrt_sq (norm_nonneg _)] at hs
  rw [hinv] at hs
  exact hs.trans (metric_curve_speed_congr hγ).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth curves admit projective lifts with the exact horizontal speed in the open normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_local_curve_lift (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {γ : ℝ → M} {s : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ s)
    (v : FourSpace) (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (hpoint : frameExponential g o e v = γ s) :
    ∃ (u : ℝ → UnitSphere CP2Vector) (w : CP2Vector),
      (u s).val = complexNormalLift v ∧
      HasDerivAt (fun t => (u t).val) w s ∧
      (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ ∧
      Real.sqrt 2 * ‖complexHorizontalPart (u s).val w‖ =
        metricTangentNorm g (γ s) (mfderiv 𝓘(ℝ, ℝ) I4 γ s 1) := by
  have hnorm := halfFlat_dimension_one_norm hRic hminus hdim
  obtain ⟨C,hCv,hC⟩ := frameExponential_complex_localChart hRic hminus hnorm W hstar hw hz e he v hR
  have hCt : C v = γ s := (hC hCv).trans hpoint
  have hy : γ s ∈ C.target := hCt ▸ C.map_source hCv
  let α : ℝ → FourSpace := fun t => C.symm (γ t)
  have hαs : α s = v := by
    change C.symm (γ s) = v
    rw [← hCt]
    exact C.left_inv hCv
  have hα : ContDiffAt ℝ 1 α s := by
    have hi := frameExponential_complex_inverse_contMDiffAt hRic hminus hnorm
      W hstar hw hz e he v hv hR C hCv hC
    rw [hpoint] at hi
    exact (hi.comp s hγ).contDiffAt
  have hn : ∀ᶠ t in 𝓝 s, γ t ∈ C.target :=
    hγ.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hy)
  have hEq : (fun t => frameExponential g o e (α t)) =ᶠ[𝓝 s] γ := by
    filter_upwards [hn] with t ht
    exact (hC (C.map_target ht)).symm.trans (C.right_inv ht)
  let u : ℝ → UnitSphere CP2Vector := fun t => ⟨complexNormalLift (α t),complexNormalLift_norm _⟩
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : α s = ‖v‖ • q.val := by
    rw [hαs]
    change v = ‖v‖ • (‖v‖⁻¹ • v)
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  let w := complexPolarLiftDifferential ‖v‖ q (deriv α s)
  have hd : HasDerivAt (fun t => (u t).val) w s :=
    complexNormalLift_hasDerivAt (hα.differentiableAt one_ne_zero).hasDerivAt
      (norm_pos_iff.mpr hv) q hrad
  have hnear0 : ∀ᶠ t in 𝓝 s, α t ≠ 0 :=
    hα.continuousAt.eventually_ne (by rwa [hαs])
  have hnearR : ∀ᶠ t in 𝓝 s, ‖α t‖ < complexJacobiRadius :=
    hα.continuousAt.norm.eventually_lt continuousAt_const (by rwa [hαs])
  have hlift : (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ := by
    filter_upwards [hEq,hnear0,hnearR] with t ht ht0 htR
    exact (actualComplexProjectiveMap_normal hRic hminus hdim W hstar hw hz e he hstd
      (α t) ht0 htR.le).trans ht
  have hspeed := frameExponential_complex_curve_speed hRic hminus hnorm W hstar hw hz e he hstd
    (hα.differentiableAt one_ne_zero) (norm_pos_iff.mpr hv) q hrad
  have hder : deriv (fun t => complexNormalLift (α t)) s = w := hd.deriv
  rw [hder,← complexHorizontalPart_norm_sq _ _ (complexNormalLift_norm (α s)),
    Real.sqrt_sq (norm_nonneg _)] at hspeed
  exact ⟨u,w,by change complexNormalLift (α s) = _; rw [hαs],hd,hlift,
    hspeed.trans (metric_curve_speed_congr hEq)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projective angular differential is bounded by horizontal speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_overlap_derivative_bound (p : UnitSphere CP2Vector)
    {u : ℝ → UnitSphere CP2Vector} {t : ℝ} {w : CP2Vector}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hc0 : 0 < ‖inner ℂ p.val (u t).val‖) :
    DifferentiableAt ℝ (fun s => ‖inner ℂ p.val (u s).val‖) t ∧
      |deriv (fun s => ‖inner ℂ p.val (u s).val‖) t| ≤
        Real.sqrt (1-‖inner ℂ p.val (u t).val‖^2) *
          ‖complexHorizontalPart (u t).val w‖ := by
  let f : ℝ → ℂ := fun s => inner ℂ p.val (u s).val
  let c : ℝ := ‖f t‖
  have hf : HasDerivAt f (inner ℂ p.val w) t := by
    simpa only [inner_zero_left,add_zero] using (hasDerivAt_const t p.val).inner ℂ hu
  have hn : DifferentiableAt ℝ (fun s => ‖f s‖) t :=
    hf.differentiableAt.norm ℂ (norm_pos_iff.mp hc0)
  have hs := (hn.hasDerivAt.pow 2).unique hf.norm_sq
  have hs' : c * deriv (fun s => ‖f s‖) t = inner ℝ (f t) (inner ℂ p.val w) := by
    dsimp only [c]
    norm_num only [Nat.cast_ofNat,pow_one] at hs
    linarith
  have hproj : ‖complexHorizontalPart (u t).val p.val‖ = Real.sqrt (1-c^2) := by
    have hsq := complexHorizontalPart_norm_sq (u t).val p.val (u t).property
    rw [p.property,norm_inner_symm] at hsq
    change ‖complexHorizontalPart (u t).val p.val‖^2 = 1^2-c^2 at hsq
    norm_num only [one_pow] at hsq
    rw [← hsq]
    exact (Real.sqrt_sq (norm_nonneg (complexHorizontalPart (u t).val p.val))).symm
  have hb : |inner ℝ (f t) (inner ℂ p.val w)| ≤
      c * (Real.sqrt (1-c^2) * ‖complexHorizontalPart (u t).val w‖) := by
    change |inner ℝ (inner ℂ p.val (u t).val) (inner ℂ p.val w)| ≤ _
    rw [complexHorizontalPairing p.val (u t).val w (complex_unit_curve_tangent hu)]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [hproj] using complex_horizontal_inner_bound p.val (u t).val w (u t).property)
      (norm_nonneg _))
  rw [← hs',abs_mul,abs_of_pos hc0] at hb
  exact ⟨hn,le_of_mul_le_mul_left hb hc0⟩

theorem complex_angle_derivative_bound (p : UnitSphere CP2Vector)
    {u : ℝ → UnitSphere CP2Vector} {t : ℝ} {w : CP2Vector}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hc0 : 0 < ‖inner ℂ p.val (u t).val‖)
    (hc1 : ‖inner ℂ p.val (u t).val‖ < 1) :
    DifferentiableAt ℝ (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t ∧
      |deriv (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t| ≤
        ‖complexHorizontalPart (u t).val w‖ := by
  let f : ℝ → ℝ := fun s => ‖inner ℂ p.val (u s).val‖
  obtain ⟨hf,hb⟩ := complex_overlap_derivative_bound p hu hc0
  have hroot : 0 < Real.sqrt (1-f t^2) := Real.sqrt_pos.mpr (by dsimp [f]; nlinarith)
  have hd := (Real.hasDerivAt_arccos (by dsimp [f]; linarith) hc1.ne).comp t hf.hasDerivAt
  refine ⟨hd.differentiableAt,?_⟩
  change |deriv (Real.arccos ∘ f) t| ≤ _
  rw [hd.deriv]
  simp only [one_div]
  change |-(Real.sqrt (1-f t^2))⁻¹ * deriv f t| ≤ _
  rw [abs_mul,abs_neg,abs_inv,abs_of_pos hroot]
  have hb' : |deriv f t| ≤ Real.sqrt (1-f t^2) * ‖complexHorizontalPart (u t).val w‖ := hb
  calc
    _ ≤ (Real.sqrt (1-f t^2))⁻¹ *
        (Real.sqrt (1-f t^2) * ‖complexHorizontalPart (u t).val w‖) :=
      mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hroot.le)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hroot.ne',one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform projective distance estimate in homogeneous unit coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem fubiniStudyDistance_unit_le_chord (p q : UnitSphere CP2Vector) :
    fubiniStudyDistance (complexSphereProjection p) (complexSphereProjection q) ≤
      (Real.pi/2) * ‖p.val-q.val‖ := by
  let c := ‖inner ℂ p.val q.val‖
  let d := Real.arccos c
  have hc0 : 0 ≤ c := norm_nonneg _
  have hc1 : c ≤ 1 := by
    simpa only [p.property,q.property,one_mul] using norm_inner_le_norm p.val q.val
  have hd0 : 0 ≤ d := Real.arccos_nonneg c
  have hdpi : d ≤ Real.pi := Real.arccos_le_pi c
  have hcos : Real.cos d = c := Real.cos_arccos (by linarith) hc1
  have ht := Real.cos_le_one_sub_mul_cos_sq (x := d) (by rwa [abs_of_nonneg hd0])
  rw [hcos] at ht
  have hpi2 : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left ht hpi2.le
  have hcancel : Real.pi^2 * (1-2/Real.pi^2*d^2) = Real.pi^2-2*d^2 := by
    field_simp
  rw [hcancel] at hmul
  have hinner : inner ℝ p.val q.val ≤ c := by
    simpa only [← real_inner_eq_re_inner ℂ] using! Complex.re_le_norm (inner ℂ p.val q.val)
  have hnorm : ‖p.val-q.val‖^2 = 2-2*inner ℝ p.val q.val := by
    rw [norm_sub_sq_real,p.property,q.property]
    ring
  have hchord : 2-2*c ≤ ‖p.val-q.val‖^2 := by linarith
  have hbound := mul_le_mul_of_nonneg_left hchord hpi2.le
  have hfinal : d ≤ (Real.pi/2)*‖p.val-q.val‖ := by
    have hn : 0 ≤ (Real.pi/2)*‖p.val-q.val‖ := mul_nonneg (by positivity) (norm_nonneg _)
    nlinarith
  have heq : fubiniStudyDistance (complexSphereProjection p) (complexSphereProjection q) = d := by
    rw [fubiniStudyDistance_eq_arccos]
    exact congrArg Real.arccos (cp2Overlap_of_unit_representatives _ _ p.val q.val
      (unitSphere_ne_zero p) (unitSphere_ne_zero q) p.property q.property rfl rfl)
  rwa [heq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual distance along a projective great circle, including affine exceptions. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_greatCircle_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℂ p q = 0)
    (hhead : p 0 ≠ 0 ∨ q 0 ≠ 0) (d : ℝ) (hd : d ∈ Icc 0 (Real.pi/2)) :
    metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (complexGreatCircleUnit p q hp hq hpq 0)))
      (actualComplexProjectiveMap g o e (complexSphereProjection (complexGreatCircleUnit p q hp hq hpq d))) ≤
        Real.sqrt 2 * d := by
  let u := complexGreatCircleUnit p q hp hq hpq
  let γ : ℝ → M := fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))
  obtain ⟨E,hE⟩ := complexGreatCircle_regular_off_finite p q hp hq hpq hhead
  have hcont : Continuous γ :=
    (actualComplexProjectiveMap_unit_continuous hRic hminus hdim W hstar hw hz e he hstd).comp
      (complexGreatCircleUnit_continuous p q hp hq hpq)
  have hreg (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ E) :
      (u t).val 0 ≠ 0 ∧ complexVectorAffine (u t).val ≠ 0 :=
    hE t ⟨ht.1,ht.2.trans_le hd.2⟩ hexc
  have hbound := metricDistance_le_of_speed_bound_off_finite g E hd.1
    (Real.sqrt_nonneg 2) hcont
    (fun t ht hexc => actualComplexProjectiveMap_lift_contMDiffAt hRic hminus hdim
      W hstar hw hz e he hstd (complexGreatCircle_contDiff p q).contDiffAt
      (hreg t ht hexc).1 (hreg t ht hexc).2)
    (fun t ht hexc => ?_)
  · simpa only [sub_zero] using hbound
  · have hspeed := actualComplexProjectiveMap_lift_speed hRic hminus hdim W hstar hw hz e he hstd
      (complexGreatCircle_hasDerivAt p q t) (hreg t ht hexc).1 (hreg t ht hexc).2
    have hn : ‖complexHorizontalPart (u t).val (complexGreatCircleVelocity p q t)‖ = 1 :=
      complexGreatCircle_horizontal_speed p q hp hq hpq t
    rw [hn,mul_one] at hspeed
    exact hspeed.symm.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! A section of the actual projective map and its unique local values before the cut radius. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def actualComplexProjectiveSection (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (h : Function.Surjective (actualComplexProjectiveMap g o e)) :
    M → ComplexProjective2 := Function.surjInv h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actualComplexProjectiveSection_rightInverse
    (e : FrameBundle g) (h : Function.Surjective (actualComplexProjectiveMap g o e)) :
    Function.RightInverse (actualComplexProjectiveSection g o e h)
      (actualComplexProjectiveMap g o e) := Function.rightInverse_surjInv h

theorem actualComplexProjective_section_germ (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    {γ : ℝ → M} {u : ℝ → UnitSphere CP2Vector} {s : ℝ}
    (hγ : ContinuousAt γ s)
    (hmap : (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ)
    (hR : metricDistance g e.base (γ s) < complexJacobiRadius) :
    (fun t => S (γ t)) =ᶠ[𝓝 s] (fun t => complexSphereProjection (u t)) := by
  have hr : ∀ᶠ t in 𝓝 s, metricDistance g e.base (γ t) < complexJacobiRadius :=
    ((metricDistance_continuous g).continuousAt.comp (continuousAt_const.prodMk hγ)).eventually_lt
      continuousAt_const hR
  filter_upwards [hmap,hr] with t ht htr
  exact actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
    (S (γ t)) (complexSphereProjection (u t)) ((hS (γ t)).trans ht.symm)
    (by rwa [hS (γ t)])

end
end PositiveEinsteinFour.Geometry
end


section

/-! Projective angular length controlled by the horizontal velocity of a unit lift. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_angle_curve_sub_le (p : UnitSphere CP2Vector)
    (u : ℝ → UnitSphere CP2Vector) (a b C : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : CP2Vector,
      HasDerivAt (fun s => (u s).val) w t ∧ ‖complexHorizontalPart (u t).val w‖ ≤ C)
    (hreg : ∀ t ∈ Ioo a b, t ∉ E →
      0 < ‖inner ℂ p.val (u t).val‖ ∧ ‖inner ℂ p.val (u t).val‖ < 1) :
    Real.arccos ‖inner ℂ p.val (u b).val‖ - Real.arccos ‖inner ℂ p.val (u a).val‖ ≤
      C*(b-a) := by
  have hcont : ContinuousOn (fun t => Real.arccos ‖inner ℂ p.val (u t).val‖) (Icc a b) :=
    Real.continuous_arccos.comp_continuousOn
      (continuousOn_const.inner (continuous_subtype_val.comp_continuousOn hu)).norm
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) (he : t ∉ E) :
      DifferentiableAt ℝ (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t ∧
      deriv (fun s => Real.arccos ‖inner ℂ p.val (u s).val‖) t ≤ C := by
    obtain ⟨w,hw,hC⟩ := hd t ht he
    obtain ⟨hD,hb⟩ := complex_angle_derivative_bound p hw (hreg t ht he).1 (hreg t ht he).2
    exact ⟨hD,(le_abs_self _).trans (hb.trans hC)⟩
  exact image_sub_le_mul_sub_of_deriv_le_off_finite E hab hcont
    (fun t ht he => (hbound t ht he).1) (fun t ht he => (hbound t ht he).2)

theorem fubiniStudyDistance_lift_curve_sub_le (P : ComplexProjective2)
    (u : ℝ → UnitSphere CP2Vector) (a b C : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : CP2Vector,
      HasDerivAt (fun s => (u s).val) w t ∧ ‖complexHorizontalPart (u t).val w‖ ≤ C)
    (hreg : ∀ t ∈ Ioo a b, t ∉ E →
      0 < ‖inner ℂ (cp2UnitRep P) (u t).val‖ ∧ ‖inner ℂ (cp2UnitRep P) (u t).val‖ < 1) :
    fubiniStudyDistance P (complexSphereProjection (u b)) -
      fubiniStudyDistance P (complexSphereProjection (u a)) ≤ C*(b-a) := by
  have heq (t : ℝ) : fubiniStudyDistance P (complexSphereProjection (u t)) =
      Real.arccos ‖inner ℂ (cp2UnitRep P) (u t).val‖ := by
    rw [fubiniStudyDistance_eq_arccos]
    exact congrArg Real.arccos (cp2Overlap_of_unit_representatives
      P (complexSphereProjection (u t)) (cp2UnitRep P) (u t).val
      (cp2UnitRep_ne_zero P) (unitSphere_ne_zero _) (cp2UnitRep_norm P) (u t).property
      (cp2UnitRep_mk P) rfl)
  rw [heq,heq]
  exact complex_angle_curve_sub_le ⟨cp2UnitRep P,cp2UnitRep_norm P⟩ u a b C hab E hu hd hreg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform Lipschitz control for normalizing homogeneous vectors bounded away from zero. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexNormalize (x : CP2Vector) (hx : x ≠ 0) : UnitSphere CP2Vector :=
  ⟨‖x‖⁻¹ • x,by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem complexNormalize_projection (x : CP2Vector) (hx : x ≠ 0) :
    complexSphereProjection (complexNormalize x hx) = Projectivization.mk ℂ x hx := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨(‖x‖⁻¹ : ℝ),rfl⟩

theorem complex_normalization_distance_le (x y : CP2Vector) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2*‖x-y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy
  have hsplit : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x-y) + (‖x‖⁻¹-‖y‖⁻¹) • y := by module
  have hcoef : |‖x‖⁻¹-‖y‖⁻¹| * ‖y‖ = ‖x‖⁻¹ * |‖y‖-‖x‖| := by
    have heq : ‖x‖⁻¹-‖y‖⁻¹ = (‖y‖-‖x‖)/(‖x‖*‖y‖) := by field_simp
    rw [heq,abs_div,abs_of_pos (mul_pos hx0 hy0)]
    field_simp
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖ + ‖(‖x‖⁻¹-‖y‖⁻¹) • y‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * |‖y‖-‖x‖| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx0),hcoef]
    _ ≤ ‖x‖⁻¹ * ‖x-y‖ + ‖x‖⁻¹ * ‖x-y‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = ‖x‖⁻¹ * (2*‖x-y‖) := by ring
    _ ≤ 2*‖x-y‖ := mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global distance upper bound when the initial point is in the standard affine chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_le_of_affine (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) (hhead : cp2UnitRep P 0 ≠ 0) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) ≤
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  by_cases hpq : P = Q
  · subst Q
    rw [(metricDistance_eq_zero_iff g _ _).mpr rfl,fubiniStudyDistance_eq_arccos,
      cp2Overlap_self,Real.arccos_one,mul_zero]
  have hc1 : cp2Overlap P Q < 1 := lt_of_le_of_ne (cp2Overlap_le_one P Q)
    (fun h => hpq ((cp2Overlap_eq_one_iff P Q).mp h))
  obtain ⟨v,hv,hvn,hvQ,hcv⟩ := cp2_aligned_unit_representative P Q
  obtain ⟨q,hqn,horth,hend⟩ := complex_aligned_circle (cp2UnitRep P) v (cp2UnitRep_norm P)
    hvn (cp2Overlap P Q) (cp2Overlap_nonneg P Q) hc1 hcv
  let d := Real.arccos (cp2Overlap P Q)
  let u := complexGreatCircleUnit (cp2UnitRep P) q (cp2UnitRep_norm P) hqn horth
  have hP : complexSphereProjection (u 0) = P := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) q 0) _ = P
    simpa only [complexGreatCircle,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
      using cp2UnitRep_mk P
  have hQ : complexSphereProjection (u d) = Q := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) q d) _ = Q
    simpa only [d,hend] using hvQ
  have h := actualComplexProjectiveMap_greatCircle_distance_le hRic hminus hdim W hstar hw hz e he hstd
    (cp2UnitRep P) q (cp2UnitRep_norm P) hqn horth (Or.inl hhead) d
    ⟨Real.arccos_nonneg _,Real.arccos_le_pi_div_two.mpr (cp2Overlap_nonneg P Q)⟩
  change metricDistance g (actualComplexProjectiveMap g o e (complexSphereProjection (u 0)))
    (actualComplexProjectiveMap g o e (complexSphereProjection (u d))) ≤ Real.sqrt 2*d at h
  rw [hP,hQ] at h
  simpa only [d,fubiniStudyDistance_eq_arccos] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local angular distance estimates for a section of the actual projective map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_inverse_angle_derivative (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (P : ComplexProjective2) {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ s)
    (v : FourSpace) (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (hpoint : frameExponential g o e v = γ s)
    (hc0 : 0 < cp2Overlap P (S (γ s))) (hc1 : cp2Overlap P (S (γ s)) < 1) :
    DifferentiableAt ℝ (fun t => fubiniStudyDistance P (S (γ t))) s ∧
      |deriv (fun t => fubiniStudyDistance P (S (γ t))) s| ≤
        (Real.sqrt 2)⁻¹ * metricTangentNorm g (γ s) (mfderiv 𝓘(ℝ, ℝ) I4 γ s 1) := by
  obtain ⟨u,w,_,hu,hmap,hspeed⟩ := actualComplexProjectiveMap_local_curve_lift
    hRic hminus hdim W hstar hw hz e he hstd hγ v hv hR hpoint
  have hrad : metricDistance g e.base (γ s) < complexJacobiRadius := by
    rw [← hpoint,frameExponential_complex_minimizing hRic hminus hdim e he v hR.le]
    exact hR
  have heq := actualComplexProjective_section_germ hRic hminus hdim W hstar hw hz e he hstd
    S hS hγ.continuousAt hmap hrad
  have heqs : S (γ s) = complexSphereProjection (u s) := heq.self_of_nhds
  have hval (t : ℝ) : cp2Overlap P (complexSphereProjection (u t)) =
      ‖inner ℂ (cp2UnitRep P) (u t).val‖ :=
    cp2Overlap_of_unit_representatives P (complexSphereProjection (u t))
      (cp2UnitRep P) (u t).val (cp2UnitRep_ne_zero P) (unitSphere_ne_zero _)
      (cp2UnitRep_norm P) (u t).property (cp2UnitRep_mk P) rfl
  have h0 : 0 < ‖inner ℂ (cp2UnitRep P) (u s).val‖ := by
    rw [← hval,← heqs]
    exact hc0
  have h1 : ‖inner ℂ (cp2UnitRep P) (u s).val‖ < 1 := by
    rw [← hval,← heqs]
    exact hc1
  have hdist : (fun t => fubiniStudyDistance P (S (γ t))) =ᶠ[𝓝 s]
      (fun t => Real.arccos ‖inner ℂ (cp2UnitRep P) (u t).val‖) := by
    filter_upwards [heq] with t ht
    rw [ht,fubiniStudyDistance_eq_arccos,hval]
  obtain ⟨hd,hb⟩ := complex_angle_derivative_bound ⟨cp2UnitRep P,cp2UnitRep_norm P⟩ hu h0 h1
  have hd' := hd.hasDerivAt.congr_of_eventuallyEq hdist
  refine ⟨hd'.differentiableAt,?_⟩
  rw [hd'.deriv]
  apply hb.trans
  rw [← hspeed,← mul_assoc,inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A projective section is continuous wherever the actual fiber is a singleton. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

theorem complexProjective_compactSpace : CompactSpace ComplexProjective2 := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr complexPolarProjection_surjective]
  exact isCompact_range complexPolarProjection_continuous

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_section_continuousAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (x : M) (hR : metricDistance g e.base x < complexJacobiRadius) :
    ContinuousAt S x := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  have hF := actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd
  have huniq (p : ComplexProjective2) (hp : actualComplexProjectiveMap g o e p = x) : p = S x :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      p (S x) (hp.trans (hS x).symm) (by rwa [hp])
  change Tendsto S (𝓝 x) (𝓝 (S x))
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V,hVU,hV,hsV⟩ := mem_nhds_iff.mp hU
  have hclosed : IsClosed (actualComplexProjectiveMap g o e '' Vᶜ) :=
    hF.isClosedMap _ hV.isClosed_compl
  have hx : x ∈ (actualComplexProjectiveMap g o e '' Vᶜ)ᶜ := by
    rintro ⟨p,hp,hpx⟩
    exact hp ((huniq p hpx) ▸ hsV)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  apply hVU
  by_contra hsy
  exact hy ⟨S y,hsy,hS y⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Two bounded complex coordinate charts cover the projective cut hyperplane. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

def complexCutLift (i : Fin 2) (z : ℂ) : CP2Vector :=
  if i = 0 then WithLp.toLp 2 ![0,1,z] else WithLp.toLp 2 ![0,z,1]

theorem complexCutLift_norm_ge_one (i : Fin 2) (z : ℂ) : 1 ≤ ‖complexCutLift i z‖ := by
  fin_cases i
  · simpa [complexCutLift] using PiLp.norm_apply_le (complexCutLift 0 z) 1
  · simpa [complexCutLift] using PiLp.norm_apply_le (complexCutLift 1 z) 2

theorem complexCutLift_ne_zero (i : Fin 2) (z : ℂ) : complexCutLift i z ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one (complexCutLift_norm_ge_one i z)))

def complexCutPoint (i : Fin 2) (z : ℂ) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexCutLift i z) (complexCutLift_ne_zero i z)

theorem complexCutLift_sub_norm (i : Fin 2) (z w : ℂ) :
    ‖complexCutLift i z-complexCutLift i w‖ = ‖z-w‖ := by
  have heq : complexCutLift i z-complexCutLift i w =
      EuclideanSpace.single (if i = 0 then 2 else 1) (z-w) := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [complexCutLift]
  rw [heq]
  simp

theorem complexCutPoint_distance_le (i : Fin 2) (z w : ℂ) :
    fubiniStudyDistance (complexCutPoint i z) (complexCutPoint i w) ≤ Real.pi * ‖z-w‖ := by
  let p := complexNormalize (complexCutLift i z) (complexCutLift_ne_zero i z)
  let q := complexNormalize (complexCutLift i w) (complexCutLift_ne_zero i w)
  have hp : complexSphereProjection p = complexCutPoint i z := complexNormalize_projection _ _
  have hq : complexSphereProjection q = complexCutPoint i w := complexNormalize_projection _ _
  rw [← hp,← hq]
  have hb := fubiniStudyDistance_unit_le_chord p q
  have hn : ‖p.val-q.val‖ ≤ 2*‖z-w‖ := by
    exact (complex_normalization_distance_le _ _ (complexCutLift_norm_ge_one i z)
      (complexCutLift_norm_ge_one i w)).trans_eq (by rw [complexCutLift_sub_norm])
  exact hb.trans ((mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ Real.pi/2)).trans_eq (by ring))

theorem complexCutPoint_covers (P : ComplexProjective2) (hP : cp2UnitRep P 0 = 0) :
    ∃ (i : Fin 2) (z : ℂ), ‖z‖ ≤ 1 ∧ complexCutPoint i z = P := by
  let p := cp2UnitRep P
  have hp0 : p 0 = 0 := hP
  have hnon : p 1 ≠ 0 ∨ p 2 ≠ 0 := by
    by_contra h
    push Not at h
    have hz : p = 0 := by ext i; fin_cases i <;> simp [hp0,h.1,h.2]
    exact cp2UnitRep_ne_zero P hz
  by_cases hnorm : ‖p 2‖ ≤ ‖p 1‖
  · have hp1 : p 1 ≠ 0 := by
      intro hz
      have hz2 : p 2 = 0 := norm_eq_zero.mp (le_antisymm
        (by simpa only [hz,norm_zero] using hnorm) (norm_nonneg _))
      exact hnon.elim (fun h => h hz) (fun h => h hz2)
    refine ⟨0,p 2 / p 1,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hp1)).mpr hnorm
    · rw [← cp2UnitRep_mk P]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(p 1)⁻¹,?_⟩
      change (p 1)⁻¹ • p = complexCutLift 0 (p 2 / p 1)
      ext i
      fin_cases i <;> simp [complexCutLift,hp0,hp1,div_eq_mul_inv,mul_comm]
  · have hp2 : p 2 ≠ 0 := by
      intro hz
      have hh := lt_of_not_ge hnorm
      rw [hz,norm_zero] at hh
      exact (not_lt_of_ge (norm_nonneg _)) hh
    refine ⟨1,p 1 / p 2,?_,?_⟩
    · rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hp2)).mpr (le_of_not_ge hnorm)
    · rw [← cp2UnitRep_mk P]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(p 2)⁻¹,?_⟩
      change (p 2)⁻¹ • p = complexCutLift 1 (p 1 / p 2)
      ext i
      fin_cases i <;> simp [complexCutLift,hp0,hp2,div_eq_mul_inv,mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit Fubini--Study distance induces the existing compact projective topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

theorem fubiniStudyDistance_self (P : ComplexProjective2) : fubiniStudyDistance P P = 0 := by
  rw [fubiniStudyDistance_eq_arccos,cp2Overlap_self,Real.arccos_one]

theorem fubiniStudyDistance_comm (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q = fubiniStudyDistance Q P := by
  simp only [fubiniStudyDistance_eq_arccos,cp2Overlap_comm P Q]

theorem fubiniStudyDistance_eq_zero_iff (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q = 0 ↔ P = Q := by
  rw [fubiniStudyDistance_eq_arccos,Real.arccos_eq_zero]
  exact ⟨fun h => (cp2Overlap_eq_one_iff P Q).mp (le_antisymm (cp2Overlap_le_one P Q) h),
    fun h => by subst Q; rw [cp2Overlap_self]⟩

theorem complexProjective_open_iff (V : Set ComplexProjective2) :
    IsOpen V ↔ ∀ x ∈ V, ∃ ε > 0, ∀ y, fubiniStudyDistance x y < ε → y ∈ V := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  constructor
  · intro hV x hx
    by_cases hempty : Vᶜ = ∅
    · refine ⟨1,zero_lt_one,fun y _ => ?_⟩
      by_contra hy
      have hh : y ∈ (∅ : Set ComplexProjective2) := hempty ▸ hy
      exact hh
    obtain ⟨y,hy,hmin⟩ := hV.isClosed_compl.isCompact.exists_isMinOn
      (Set.nonempty_iff_ne_empty.mpr hempty) (fubiniStudyDistance_left_continuous x).continuousOn
    have hpos : 0 < fubiniStudyDistance x y := by
      apply lt_of_le_of_ne
      · rw [fubiniStudyDistance_eq_arccos]; exact Real.arccos_nonneg _
      · intro h
        exact hy ((fubiniStudyDistance_eq_zero_iff x y).mp h.symm ▸ hx)
    refine ⟨fubiniStudyDistance x y,hpos,fun z hz => ?_⟩
    by_contra hzV
    exact (not_lt_of_ge (hmin hzV)) hz
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε,hε,hsub⟩ := h x hx
    have hn : {y | fubiniStudyDistance x y < ε} ∈ 𝓝 x :=
      (isOpen_lt (fubiniStudyDistance_left_continuous x) continuous_const).mem_nhds
        (by simpa only [mem_ofPred_eq,fubiniStudyDistance_self] using hε)
    exact mem_of_superset hn hsub

@[instance_reducible] def complexProjectiveMetric : MetricSpace ComplexProjective2 :=
  MetricSpace.ofDistTopology fubiniStudyDistance fubiniStudyDistance_self
    fubiniStudyDistance_comm fubiniStudyDistance_triangle complexProjective_open_iff
    (fun P Q h => (fubiniStudyDistance_eq_zero_iff P Q).mp h)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projective map decreases the scaled Fubini--Study distance everywhere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) ≤
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  by_cases hhead : cp2UnitRep P 0 ≠ 0
  · exact actualComplexProjectiveMap_distance_le_of_affine hRic hminus hdim W hstar hw hz e he hstd P Q hhead
  have hp0 : cp2UnitRep P 0 = 0 := not_ne_iff.mp hhead
  let n : CP2Vector := EuclideanSpace.single 0 1
  have hn : ‖n‖ = 1 := by simp [n]
  have hpn : inner ℂ (cp2UnitRep P) n = 0 := by
    simp [n,EuclideanSpace.inner_single_right,hp0]
  let u : ℝ → UnitSphere CP2Vector :=
    complexGreatCircleUnit (cp2UnitRep P) n (cp2UnitRep_norm P) hn hpn
  have hu : Continuous u := complexGreatCircleUnit_continuous _ _ _ _ _
  have hP : complexSphereProjection (u 0) = P := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) n 0) _ = P
    simpa only [complexGreatCircle,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
      using cp2UnitRep_mk P
  have hmap := actualComplexProjectiveMap_unit_continuous hRic hminus hdim W hstar hw hz e he hstd
  have hleft : Continuous (fun t : ℝ => metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (u t)))
      (actualComplexProjectiveMap g o e Q)) :=
    (metricDistance_continuous g).comp ((hmap.comp hu).prodMk continuous_const)
  have hright : Continuous (fun t : ℝ => Real.sqrt 2 *
      fubiniStudyDistance (complexSphereProjection (u t)) Q) :=
    continuous_const.mul ((fubiniStudyDistance_sphere_continuous Q).comp hu)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (u t)))
      (actualComplexProjectiveMap g o e Q) ≤ Real.sqrt 2 *
      fubiniStudyDistance (complexSphereProjection (u t)) Q := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi))] with t ht htpi
    have hus : (u t).val 0 ≠ 0 := by
      change (Real.cos t : ℂ) * cp2UnitRep P 0 + (Real.sin t : ℂ) * n 0 ≠ 0
      rw [hp0,mul_zero,zero_add]
      have hn0 : n 0 = 1 := by simp [n]
      rw [hn0,mul_one,ne_eq,Complex.ofReal_eq_zero]
      exact (Real.sin_pos_of_pos_of_lt_pi ht htpi).ne'
    exact actualComplexProjectiveMap_distance_le_of_affine hRic hminus hdim W hstar hw hz e he hstd
      _ Q (cp2UnitRep_coordinate_ne_zero_of_unit (u t) 0 hus)
  have h := le_of_tendsto_of_tendsto
    ((hleft.tendsto 0).mono_left nhdsWithin_le_nhds)
    ((hright.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  simpa only [hP] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse projective length comparison along actual curves in the open normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_inverse_curve_sub_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (P : ComplexProjective2) (γ : ℝ → M) (a b C : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hR : ∀ t ∈ Icc a b, metricDistance g e.base (γ t) < complexJacobiRadius)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, t ∉ E →
      metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C)
    (hx : ∀ t ∈ Ioo a b, t ∉ E → γ t ≠ e.base)
    (hreg : ∀ t ∈ Ioo a b, t ∉ E → 0 < cp2Overlap P (S (γ t)) ∧ cp2Overlap P (S (γ t)) < 1) :
    fubiniStudyDistance P (S (γ b)) - fubiniStudyDistance P (S (γ a)) ≤
      ((Real.sqrt 2)⁻¹*C)*(b-a) := by
  have hcont : ContinuousOn (fun t => fubiniStudyDistance P (S (γ t))) (Icc a b) := by
    intro t ht
    apply (fubiniStudyDistance_left_continuous P).continuousAt.comp_continuousWithinAt
    exact (actualComplexProjective_section_continuousAt hRic hminus hdim W hstar hw hz e he hstd
      S hS (γ t) (hR t ht)).comp_continuousWithinAt (hγ t ht)
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) (hexc : t ∉ E) :
      DifferentiableAt ℝ (fun s => fubiniStudyDistance P (S (γ s))) t ∧
      deriv (fun s => fubiniStudyDistance P (S (γ s))) t ≤ (Real.sqrt 2)⁻¹*C := by
    obtain ⟨v,hv,hvR,hvpoint⟩ := exists_complex_interior_coordinates hRic hminus hdim e he
      (γ t) (hR t ⟨ht.1.le,ht.2.le⟩) (hx t ht hexc)
    obtain ⟨hD,hb⟩ := actualComplexProjective_inverse_angle_derivative hRic hminus hdim
      W hstar hw hz e he hstd S hS P (hd t ht hexc) v hv hvR hvpoint
      (hreg t ht hexc).1 (hreg t ht hexc).2
    exact ⟨hD,(le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left
      (hs t ht hexc) (inv_nonneg.mpr (Real.sqrt_nonneg 2))))⟩
  exact image_sub_le_mul_sub_of_deriv_le_off_finite E hab hcont
    (fun t ht hexc => (hbound t ht hexc).1) (fun t ht hexc => (hbound t ht hexc).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The open polar ball is dense in the actual projective metric space. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveMetric

def complexProjectiveInterior : Set ComplexProjective2 :=
  {P | ∃ t ∈ Ico (0 : ℝ) complexJacobiRadius, ∃ q : Directions, complexProjectivePolar t q = P}

theorem complexProjectiveInterior_dense : Dense complexProjectiveInterior := by
  intro P
  obtain ⟨t,ht,q,rfl⟩ := complexProjectivePolar_surjective P
  by_cases ht0 : t = 0
  · subst t
    exact subset_closure ⟨0,⟨le_rfl,complexJacobiRadius_pos⟩,q,rfl⟩
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hlim : Tendsto (fun s : ℝ => complexProjectivePolar s q)
      (𝓝[<] t) (𝓝 (complexProjectivePolar t q)) :=
    (complexProjectivePolar_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_gt_nhds htpos)] with s hst hs0
  exact ⟨s,⟨hs0.le,hst.trans_le ht.2⟩,q,rfl⟩

theorem exists_complexInterior_sequence (P : ComplexProjective2) :
    ∃ u : ℕ → ComplexProjective2, (∀ n, u n ∈ complexProjectiveInterior) ∧
      Tendsto u atTop (𝓝 P) :=
  mem_closure_iff_seq_limit.mp (complexProjectiveInterior_dense P)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut locus is covered by two Lipschitz images of closed complex disks. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem cp2Overlap_north (P : ComplexProjective2) :
    cp2Overlap complexProjectiveNorth P = ‖cp2UnitRep P 0‖ := by
  have h := cp2Overlap_of_unit_representatives complexProjectiveNorth P
    (complexPolarLift 0 firstDirection) (cp2UnitRep P)
    (complexPolarLift_ne_zero 0 firstDirection) (cp2UnitRep_ne_zero P)
    (complexPolarLift_norm 0 firstDirection) (cp2UnitRep_norm P) rfl (cp2UnitRep_mk P)
  rw [h]
  simp [complexPolarLift,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three]

theorem cp2UnitRep_cut_head (i : Fin 2) (z : ℂ) : cp2UnitRep (complexCutPoint i z) 0 = 0 := by
  have h : Projectivization.mk ℂ (cp2UnitRep (complexCutPoint i z))
      (cp2UnitRep_ne_zero _) = Projectivization.mk ℂ (complexCutLift i z) (complexCutLift_ne_zero i z) :=
    cp2UnitRep_mk _
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hh := congrArg (fun p : CP2Vector => p 0) ha
  have hzero : complexCutLift i z 0 = 0 := by fin_cases i <;> simp [complexCutLift]
  change a * complexCutLift i z 0 = cp2UnitRep (complexCutPoint i z) 0 at hh
  simpa only [hzero,mul_zero] using hh.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_cut_iff (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (P : ComplexProjective2) :
    metricDistance g e.base (actualComplexProjectiveMap g o e P) = complexJacobiRadius ↔
      cp2UnitRep P 0 = 0 := by
  rw [actualComplexProjectiveMap_distance_from_center hRic hminus hdim W hstar hw hz e he hstd,
    fubiniStudyDistance_eq_arccos,cp2Overlap_north]
  have hs : Real.sqrt 2 * (Real.pi/2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    apply (eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)).mpr
    calc
      Real.sqrt 2 * (Real.pi/2) * Real.sqrt 2 = (Real.pi/2) * (Real.sqrt 2)^2 := by ring
      _ = Real.pi := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [← hs]
  constructor
  · intro h
    exact norm_eq_zero.mp (Real.arccos_eq_pi_div_two.mp
      (mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h))
  · intro h
    rw [h,norm_zero,Real.arccos_zero]

theorem actual_complex_cut_disk_cover (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (x : M) :
    metricDistance g e.base x = complexJacobiRadius ↔
      ∃ (i : Fin 2) (z : ℂ), ‖z‖ ≤ 1 ∧ actualComplexProjectiveMap g o e (complexCutPoint i z) = x := by
  constructor
  · intro hx
    obtain ⟨P,rfl⟩ := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd x
    obtain ⟨i,z,hznorm,hP⟩ := complexCutPoint_covers P
      ((actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd P).mp hx)
    exact ⟨i,z,hznorm,congrArg (actualComplexProjectiveMap g o e) hP⟩
  · rintro ⟨i,z,_,rfl⟩
    exact (actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd _).mpr
      (cp2UnitRep_cut_head i z)

theorem actual_complex_cut_disk_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (i : Fin 2) (z w : ℂ) :
    metricDistance g (actualComplexProjectiveMap g o e (complexCutPoint i z))
      (actualComplexProjectiveMap g o e (complexCutPoint i w)) ≤
      (Real.sqrt 2 * Real.pi)*‖z-w‖ := by
  exact (actualComplexProjectiveMap_distance_le hRic hminus hdim W hstar hw hz e he hstd _ _).trans
    ((mul_le_mul_of_nonneg_left (complexCutPoint_distance_le i z w) (Real.sqrt_nonneg 2)).trans_eq (by ring))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cones over locally Lipschitz complex parametrizations have dimension at most three. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

def complexParametrizedCone (a : FourSpace) (f : ℂ → FourSpace) (U : Set ℂ) : Set FourSpace :=
  (fun p : ℂ × ℝ => a + p.2 • (f p.1 - a)) '' (U ×ˢ univ)

theorem complexParametrizedCone_dimH_le (a : FourSpace) (f : ℂ → FourSpace) (U : Set ℂ)
    (hf : ∀ z ∈ U, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K f V) :
    dimH (complexParametrizedCone a f U) ≤ 3 := by
  have houter : LocallyLipschitz (fun p : FourSpace × ℝ => a + p.2 • (p.1 - a)) :=
    (contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const)) :
      ContDiff ℝ 1 (fun p : FourSpace × ℝ => a + p.2 • (p.1 - a))).locallyLipschitz
  have hlocal : ∀ p ∈ U ×ˢ (univ : Set ℝ), ∃ K : ℝ≥0, ∃ V ∈ 𝓝[U ×ˢ univ] p,
      LipschitzOnWith K (fun p : ℂ × ℝ => a + p.2 • (f p.1 - a)) V := by
    intro p hp
    obtain ⟨K,V,hV,hfV⟩ := hf p.1 hp.1
    let T : Set (ℂ × ℝ) := Prod.fst ⁻¹' V
    have hT : T ∈ 𝓝 p := continuous_fst.continuousAt hV
    have hpair : LipschitzOnWith (max K 1) (fun q : ℂ × ℝ => (f q.1,q.2)) T := by
      have hh : LipschitzOnWith K (fun q : ℂ × ℝ => f q.1) T := by
        simpa only [mul_one,Function.comp_def] using hfV.comp
          (LipschitzWith.prod_fst.lipschitzOnWith : LipschitzOnWith 1 Prod.fst T)
          (fun _ hq => hq)
      exact hh.prodMk LipschitzWith.prod_snd.lipschitzOnWith
    obtain ⟨L,W,hW,houterW⟩ := houter (f p.1,p.2)
    have hpre : (fun q : ℂ × ℝ => (f q.1,q.2)) ⁻¹' W ∈ 𝓝 p :=
      (hpair.continuousOn.continuousAt hT) hW
    refine ⟨L * max K 1,T ∩ (fun q : ℂ × ℝ => (f q.1,q.2)) ⁻¹' W,
      mem_nhdsWithin_of_mem_nhds (inter_mem hT hpre), ?_⟩
    intro u hu v hv
    have hd := (houterW hu.2 hv.2).trans (mul_le_mul_right (hpair hu.1 hv.1) (L : ℝ≥0∞))
    simpa only [ENNReal.coe_mul,mul_assoc] using hd
  calc
    _ ≤ dimH (U ×ˢ (univ : Set ℝ)) := dimH_image_le_of_locally_lipschitzOn hlocal
    _ ≤ dimH (univ : Set (ℂ × ℝ)) := dimH_mono (subset_univ _)
    _ = 3 := by rw [Real.dimH_univ_eq_finrank]; norm_num [Module.finrank_prod]

theorem complexParametrizedCone_hausdorff_four_zero (a : FourSpace) (f : ℂ → FourSpace)
    (U : Set ℂ) (hf : ∀ z ∈ U, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K f V) :
    (MeasureTheory.Measure.hausdorffMeasure 4 : MeasureTheory.Measure FourSpace)
      (complexParametrizedCone a f U) = 0 := by
  apply hausdorffMeasure_of_dimH_lt (d := (4 : ℝ≥0))
  exact (complexParametrizedCone_dimH_le a f U hf).trans_lt (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse distance along an interior curve, including zero and maximal angular values. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_inverse_interior_curve_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (γ : ℝ → M) (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C) (E : Finset ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hR : ∀ t ∈ Icc a b, metricDistance g e.base (γ t) < complexJacobiRadius)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, t ∉ E →
      metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C)
    (hx : ∀ t ∈ Ioo a b, t ∉ E → γ t ≠ e.base) :
    fubiniStudyDistance (S (γ a)) (S (γ b)) ≤ ((Real.sqrt 2)⁻¹*C)*(b-a) := by
  let P := S (γ a)
  let f : ℝ → ℝ := fun t => fubiniStudyDistance P (S (γ t))
  have hcont : ContinuousOn f (Icc a b) := by
    intro t ht
    exact (fubiniStudyDistance_left_continuous P).continuousAt.comp_continuousWithinAt
      ((actualComplexProjective_section_continuousAt hRic hminus hdim W hstar hw hz e he hstd
        S hS (γ t) (hR t ht)).comp_continuousWithinAt (hγ t ht))
  have hfa : f a = 0 := by simp [f,P,fubiniStudyDistance_eq_arccos]
  have hpos (t : ℝ) (_ : t ∈ Icc a b) : 0 ≤ f t := Real.arccos_nonneg _
  have hbound : f b ≤ Real.pi/2 := by
    change fubiniStudyDistance P (S (γ b)) ≤ _
    rw [fubiniStudyDistance_eq_arccos]
    exact Real.arccos_le_pi_div_two.mpr (cp2Overlap_nonneg _ _)
  have hD (t : ℝ) (ht : t ∈ Ioo a b) (hexc : t ∉ E) (h0 : 0 < f t) (h1 : f t < Real.pi/2) :
      DifferentiableAt ℝ f t ∧ deriv f t ≤ (Real.sqrt 2)⁻¹*C := by
    have hc0 : 0 < cp2Overlap P (S (γ t)) := by
      apply Real.arccos_lt_pi_div_two.mp
      simpa only [f,fubiniStudyDistance_eq_arccos] using h1
    have hc1 : cp2Overlap P (S (γ t)) < 1 := by
      apply Real.arccos_pos.mp
      simpa only [f,fubiniStudyDistance_eq_arccos] using h0
    obtain ⟨v,hv,hvR,hvx⟩ := exists_complex_interior_coordinates hRic hminus hdim e he
      (γ t) (hR t ⟨ht.1.le,ht.2.le⟩) (hx t ht hexc)
    obtain ⟨hD,hb⟩ := actualComplexProjective_inverse_angle_derivative hRic hminus hdim
      W hstar hw hz e he hstd S hS P (hd t ht hexc) v hv hvR hvx hc0 hc1
    exact ⟨hD,(le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left (hs t ht hexc)
      (inv_nonneg.mpr (Real.sqrt_nonneg 2))))⟩
  exact bounded_angle_le_of_deriv_le f a b (Real.pi/2) ((Real.sqrt 2)⁻¹*C) E hab
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)) hC) hcont hfa hpos hbound
    (fun t ht he h0 h1 => (hD t ht he h0 h1).1)
    (fun t ht he h0 h1 => (hD t ht he h0 h1).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual complex cut locus has zero three-dimensional Hausdorff measure. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set MeasureTheory Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def metricHausdorffThree (g : SmoothMetric M) : Measure M := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact Measure.hausdorffMeasure 3

theorem actual_complex_cut_hausdorff_three_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) :
    metricHausdorffThree g {x | metricDistance g e.base x = complexJacobiRadius} = 0 := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let F : Fin 2 → ℂ → M := fun i z => actualComplexProjectiveMap g o e (complexCutPoint i z)
  let K : ℝ≥0 := ⟨Real.sqrt 2 * Real.pi,mul_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le⟩
  have hLip (i : Fin 2) : LipschitzWith K (F i) := by
    intro z w
    change metricEDistance g (F i z) (F i w) ≤ (K : ℝ≥0∞)*edist z w
    rw [← ofReal_metricDistance g,edist_dist,dist_eq_norm,← ENNReal.ofReal_coe_nnreal]
    calc
      _ ≤ ENNReal.ofReal ((K : ℝ)*‖z-w‖) := ENNReal.ofReal_le_ofReal
        (actual_complex_cut_disk_distance_le hRic hminus hdim W hstar hw hz e he hstd i z w)
      _ = _ := ENNReal.ofReal_mul K.property
  have hC : (Measure.hausdorffMeasure 3 : Measure ℂ) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (by norm_num)
  have hzero (i : Fin 2) : (Measure.hausdorffMeasure 3 : Measure M) (range (F i)) = 0 := by
    have h := (hLip i).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 3) univ
    simp only [image_univ,hC,Measure.coe_zero,Pi.zero_apply,mul_zero] at h
    exact le_antisymm h zero_le
  have hcover : {x | metricDistance g e.base x = complexJacobiRadius} ⊆ ⋃ i, range (F i) := by
    intro x hx
    obtain ⟨i,z,_,heq⟩ := (actual_complex_cut_disk_cover hRic hminus hdim W hstar hw hz e he hstd x).mp hx
    exact mem_iUnion.mpr ⟨i,⟨z,heq⟩⟩
  exact measure_mono_null hcover (measure_iUnion_null hzero)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrarily short polygonal detours around two complex-parametrized sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

theorem exists_not_mem_of_dimH_le_three (s : Set FourSpace) (hs : dimH s ≤ 3)
    (x : FourSpace) (V : Set FourSpace) (hV : V ∈ 𝓝 x) : ∃ y ∈ V, y ∉ s := by
  by_contra! h
  have hdim : (4 : ℝ≥0∞) ≤ 3 := by
    calc
      _ = dimH V := by rw [Real.dimH_of_mem_nhds hV]; norm_num [FourSpace]
      _ ≤ dimH s := dimH_mono h
      _ ≤ 3 := hs
  norm_num at hdim

theorem segment_avoids_of_not_mem_complexCone (a b : FourSpace)
    (f : ℂ → FourSpace) (U : Set ℂ) (ha : a ∉ f '' U)
    (hb : b ∉ complexParametrizedCone a f U) :
    Disjoint (segment ℝ a b) (f '' U) := by
  rw [Set.disjoint_left]
  intro p hp hpf
  obtain ⟨z,hz,rfl⟩ := hpf
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t,ht,heq⟩ := hp
  by_cases ht0 : t = 0
  · have hfa : f z = a := by simpa only [ht0,AffineMap.lineMap_apply_zero] using heq.symm
    exact ha ⟨z,hz,hfa⟩
  · apply hb
    refine ⟨(z,t⁻¹),⟨hz,mem_univ _⟩,?_⟩
    have hsub : f z - a = t • (b-a) := by
      rw [← heq,AffineMap.lineMap_apply]
      simp only [vsub_eq_sub,vadd_eq_add]
      abel
    change a + t⁻¹ • (f z-a) = b
    rw [hsub,smul_smul,inv_mul_cancel₀ ht0,one_smul]
    abel

theorem exists_complexParametrized_detour (f : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hf : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (f i) V)
    (a b : FourSpace) (ha : ∀ i, a ∉ f i '' U i) (hb : ∀ i, b ∉ f i '' U i)
    (V : Set FourSpace) (hV : V ∈ 𝓝 b) :
    ∃ z ∈ V, ∀ i, Disjoint (segment ℝ a z) (f i '' U i) ∧
      Disjoint (segment ℝ z b) (f i '' U i) := by
  let B := (⋃ i, complexParametrizedCone a (f i) (U i)) ∪
    (⋃ i, complexParametrizedCone b (f i) (U i))
  have hB : dimH B ≤ 3 := by
    rw [dimH_union]
    apply max_le
    · rw [dimH_iUnion]
      exact iSup_le (fun i => complexParametrizedCone_dimH_le a (f i) (U i) (hf i))
    · rw [dimH_iUnion]
      exact iSup_le (fun i => complexParametrizedCone_dimH_le b (f i) (U i) (hf i))
  obtain ⟨z,hz,hzB⟩ := exists_not_mem_of_dimH_le_three B hB b V hV
  refine ⟨z,hz,fun i => ⟨?_,?_⟩⟩
  · apply segment_avoids_of_not_mem_complexCone a z (f i) (U i) (ha i)
    exact fun h => hzB (Or.inl (mem_iUnion.mpr ⟨i,h⟩))
  · rw [segment_symm]
    apply segment_avoids_of_not_mem_complexCone b z (f i) (U i) (hb i)
    exact fun h => hzB (Or.inr (mem_iUnion.mpr ⟨i,h⟩))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact inverse length control for actual minimizing geodesics that remain before the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_frameGeodesic_radial_distance (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) (t : ℝ) (ht : t ∈ Icc 0 complexJacobiRadius) :
    metricDistance g f.base (frameGeodesic g 0 f t) = t := by
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    simp [coordinateVector]
  have hm := frameExponential_complex_minimizing hRic hminus hdim f hf
    (t • coordinateVector 0) (by rw [hn]; exact ht.2)
  rwa [frameExponential_first_ray_all g o f hf t,hn] at hm

theorem complex_frameGeodesic_injOn (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) :
    InjOn (frameGeodesic g 0 f) (Icc 0 complexJacobiRadius) := by
  intro s hs t ht heq
  have h := congrArg (metricDistance g f.base) heq
  rwa [complex_frameGeodesic_radial_distance hRic hminus hdim f hf s hs,
    complex_frameGeodesic_radial_distance hRic hminus hdim f hf t ht] at h

theorem actualComplexProjective_inverse_interior_geodesic_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (f : FrameBundle g) (hf : f ∈ o.positive) (d : ℝ) (hd : d ∈ Icc 0 complexJacobiRadius)
    (hR : ∀ t ∈ Icc 0 d, metricDistance g e.base (frameGeodesic g 0 f t) < complexJacobiRadius) :
    fubiniStudyDistance (S (frameGeodesic g 0 f 0)) (S (frameGeodesic g 0 f d)) ≤ (Real.sqrt 2)⁻¹*d := by
  classical
  let γ := frameGeodesic g 0 f
  let B : Set ℝ := Ioo 0 d ∩ γ ⁻¹' {e.base}
  have hsub : B ⊆ Icc 0 complexJacobiRadius := fun _ ht =>
    ⟨ht.1.1.le,ht.1.2.le.trans hd.2⟩
  have hi : InjOn γ B := (complex_frameGeodesic_injOn hRic hminus hdim f hf).mono hsub
  have hmap : MapsTo γ B {e.base} := fun _ ht => ht.2
  have hB : B.Finite := (finite_singleton e.base).of_injOn hmap hi
  have hbad (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) : γ t ≠ e.base := by
    intro hx
    exact hexc (hB.mem_toFinset.mpr ⟨ht,hx⟩)
  have h := actualComplexProjective_inverse_interior_curve_le hRic hminus hdim W hstar hw hz e he hstd
    S hS γ 0 d 1 hd.1 zero_le_one hB.toFinset
    (frameGeodesic_contMDiff g 0 f).continuous.continuousOn hR
    (fun _ _ _ => (frameGeodesic_contMDiff g 0 f).contMDiffAt)
    (fun t _ _ => (round_frameGeodesic_real_speed f t).le) hbad
  simpa only [mul_one,sub_zero] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut-locus parametrizations and their cones in any fixed linear chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def complexCutChartMap (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g)
    (c : M) (A : FourSpace →L[ℝ] FourSpace) (i : Fin 2) (z : ℂ) : FourSpace :=
  A (chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z)))

def complexCutChartDomain (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g)
    (c : M) (i : Fin 2) : Set ℂ :=
  (fun z => actualComplexProjectiveMap g o e (complexCutPoint i z)) ⁻¹'
    (chartAt FourSpace c).source

theorem complexCutChartMap_locallyLipschitz (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (c : M) (A : FourSpace →L[ℝ] FourSpace) (i : Fin 2) :
    ∀ z ∈ complexCutChartDomain g o e c i, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z,
      LipschitzOnWith K (complexCutChartMap g o e c A i) V := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let F : ℂ → M := fun z => actualComplexProjectiveMap g o e (complexCutPoint i z)
  let K : ℝ≥0 := ⟨Real.sqrt 2 * Real.pi,mul_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le⟩
  have hLip : LipschitzWith K F := by
    intro z w
    change metricEDistance g (F z) (F w) ≤ (K : ℝ≥0∞)*edist z w
    rw [← ofReal_metricDistance g,edist_dist,dist_eq_norm,← ENNReal.ofReal_coe_nnreal]
    calc
      _ ≤ ENNReal.ofReal ((K : ℝ)*‖z-w‖) := ENNReal.ofReal_le_ofReal
        (actual_complex_cut_disk_distance_le hRic hminus hdim W hstar hw hz e he hstd i z w)
      _ = _ := ENNReal.ofReal_mul K.property
  exact metric_chart_lipschitz_image g c A F hLip.continuous K (fun z w => hLip z w)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local metric increment bounds control the length of a straight segment. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology
noncomputable section

theorem dist_le_of_segment_local_bound {Y : Type*} [PseudoMetricSpace Y]
    (f : FourSpace → Y) (a b : FourSpace) (K : ℝ)
    (hf : ContinuousOn f (segment ℝ a b))
    (hlocal : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝[segment ℝ a b] x,
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * dist a b := by
  let η : ℝ → FourSpace := AffineMap.lineMap a b
  have hη : Continuous η := (ContinuousAffineMap.lineMap a b).continuous
  have hmaps : MapsTo η (Icc 0 1) (segment ℝ a b) := fun t ht => lineMap_mem_segment ℝ a b ht
  have hcomp : ContinuousOn (f ∘ η) (Icc 0 1) := hf.comp hη.continuousOn hmaps
  let q : ℝ → ℝ := fun t => dist (f a) (f (η t))
  have hq : ContinuousOn q (Icc 0 1) := continuous_dist.comp_continuousOn (continuousOn_const.prodMk hcomp)
  have hinc (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ∀ᶠ s in 𝓝[>] t, q s-q t ≤ (K*dist a b)*(s-t) := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hηlim : Tendsto η (𝓝[>] t) (𝓝[segment ℝ a b] (η t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hη.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds ht.2)] with s hs hsb
      exact hmaps ⟨ht.1.trans hs.le,hsb.le⟩
    filter_upwards [hηlim (hlocal (η t) (hmaps ht')),self_mem_nhdsWithin] with s hs hts
    have htri : q s-q t ≤ dist (f (η t)) (f (η s)) := by
      dsimp [q]
      linarith [dist_triangle (f a) (f (η t)) (f (η s))]
    calc
      _ ≤ K * dist (η t) (η s) := htri.trans hs
      _ = (K*dist a b)*(s-t) := by
        change K * dist (AffineMap.lineMap a b t) (AffineMap.lineMap a b s) = _
        rw [dist_lineMap_lineMap,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hts.le)]
        ring
  have h := sub_le_of_local_increment q 0 1 (K*dist a b) (by norm_num) hq hinc
  simpa only [q,η,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,dist_self,
    sub_zero,mul_one] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact local distance preservation throughout the actual open normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_section_local_distance (hRic : RicciThree g)
    (hminus : ∀ z, minusWeyl g z (o.frame z) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ z, twoFormHodge (W.val z) = W.val z)
    (hw : ∀ z, ‖W.val z‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (x y : M) (hmargin : metricDistance g e.base x + metricDistance g x y < complexJacobiRadius) :
    Real.sqrt 2 * fubiniStudyDistance (S x) (S y) = metricDistance g x y := by
  have hupper : metricDistance g x y ≤ Real.sqrt 2 * fubiniStudyDistance (S x) (S y) := by
    simpa only [hS x,hS y] using actualComplexProjectiveMap_distance_le
      hRic hminus hdim W hstar hw hz e he hstd (S x) (S y)
  apply le_antisymm ?_ hupper
  by_cases hxy : y = x
  · subst y
    rw [fubiniStudyDistance_eq_arccos,cp2Overlap_self,Real.arccos_one,mul_zero]
    exact metricDistance_nonneg g x x
  let f : FrameBundle g := ⟨x,o.frame x⟩
  have hf : f ∈ o.positive := o.frame_positive x
  have hxyR : metricDistance g f.base y < complexJacobiRadius := by
    change metricDistance g x y < _
    linarith [metricDistance_nonneg g e.base x]
  obtain ⟨v,hv,hvR,hvy⟩ := exists_complex_interior_coordinates hRic hminus hdim f hf y hxyR hxy
  have hvdist : ‖v‖ = metricDistance g x y := by
    have h := frameExponential_complex_minimizing hRic hminus hdim f hf v hvR.le
    rw [hvy] at h
    exact h.symm
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hf' : f' ∈ o.positive := frameRotate_oriented_positive o f hf _
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  have hstart : frameGeodesic g 0 f' 0 = x := by
    simp only [frameGeodesic,parallelFrameFlowMap_zero]
    rfl
  have hend : frameGeodesic g 0 f' ‖v‖ = y := by
    rw [← frameExponential_direction_ray g o f hf q ‖v‖,hrad,hvy]
  have hstay (t : ℝ) (ht : t ∈ Icc 0 ‖v‖) :
      metricDistance g e.base (frameGeodesic g 0 f' t) < complexJacobiRadius := by
    have hdist := complex_frameGeodesic_radial_distance hRic hminus hdim f' hf' t
      ⟨ht.1,ht.2.trans hvR.le⟩
    change metricDistance g x (frameGeodesic g 0 f' t) = t at hdist
    have hh := metricDistance_triangle g e.base x (frameGeodesic g 0 f' t)
    rw [hdist] at hh
    rw [← hvdist] at hmargin
    linarith [ht.2]
  have hbound := actualComplexProjective_inverse_interior_geodesic_le hRic hminus hdim
    W hstar hw hz e he hstd S hS f' hf' ‖v‖ ⟨norm_nonneg _,hvR.le⟩ hstay
  rw [hstart,hend,hvdist] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg 2)
  rwa [← mul_assoc,mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul] at h

end
end PositiveEinsteinFour.Geometry
end

end OAI
