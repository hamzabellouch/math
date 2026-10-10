import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.WeaklySingularWeighted
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.JetVolterraFixedPoint

namespace OAI

/-! Linear Volterra equations with finitely many continuous time-dependent coefficients. -/

noncomputable section
namespace ForcedComputation.WeaklySingular

open Real MeasureTheory Set Filter
open scoped Topology Interval BigOperators

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise action of a continuous coefficient on a continuous path. -/
def coefficientOperator {T : ℝ} (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    Path E T →L[ℝ] Path E T :=
  LinearMap.mkContinuous
    { toFun := fun u => (pathEquiv E T).symm
        ⟨fun t => A t (u t), A.continuous.clm_apply (pathEquiv E T u).continuous⟩
      map_add' := by
        intro u v
        apply (pathEquiv E T).injective
        ext t
        exact (A t).map_add (u t) (v t)
      map_smul' := by
        intro c u
        apply (pathEquiv E T).injective
        ext t
        exact (A t).map_smul c (u t) }
    ‖A‖ (by
      intro u
      rw [← (pathEquiv E T).norm_map]
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact ((A t).le_opNorm (u t)).trans <|
        mul_le_mul (A.norm_coe_le_norm t)
          ((pathEquiv E T u).norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg A))

@[simp] theorem coefficientOperator_apply {T : ℝ}
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u : Path E T) (t : Icc (0 : ℝ) T) :
    coefficientOperator E A u t = A t (u t) := rfl

theorem norm_coefficientOperator_le {T : ℝ} (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖coefficientOperator E A‖ ≤ ‖A‖ := by
  apply (coefficientOperator E A).opNorm_le_bound (norm_nonneg A)
  intro u
  rw [← (pathEquiv E T).norm_map]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans <|
    mul_le_mul (A.norm_coe_le_norm t) ((pathEquiv E T u).norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg A)

/-- Multiplication by an exponential scalar weight on the time interval. -/
def weightOperator (T rate : ℝ) : Path E T →L[ℝ] Path E T :=
  coefficientOperator E
    ⟨fun t => Real.exp (rate * (t : ℝ)) • ContinuousLinearMap.id ℝ E,
      ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
        continuous_const)⟩

@[simp] theorem weightOperator_apply (T rate : ℝ) (u : Path E T) (t : Icc (0 : ℝ) T) :
    weightOperator E T rate u t = Real.exp (rate * (t : ℝ)) • u t := rfl

theorem weightOperator_inverse (T rate : ℝ) (u : Path E T) :
    weightOperator E T (-rate) (weightOperator E T rate u) = u := by
  apply (pathEquiv E T).injective
  ext t
  change Real.exp (-rate * (t : ℝ)) • (Real.exp (rate * (t : ℝ)) • u t) = u t
  rw [smul_smul, ← Real.exp_add]
  simp only [neg_mul, neg_add_cancel, Real.exp_zero, one_smul]

theorem weightOperator_injective (T rate : ℝ) : Function.Injective (weightOperator E T rate) := by
  intro u v huv
  have h := congrArg (weightOperator E T (-rate)) huv
  simpa only [weightOperator_inverse] using h

variable {ι : Type*} [Fintype ι]

/-- A finite sum of genuine Volterra integrals with continuous coefficient paths. -/
def familyOperator {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (rate : ℝ) (hrate : 0 ≤ rate) :
    Path E T →L[ℝ] Path E T :=
  ∑ i, (integralOperator E hT (weightedKernel E rate (K i))
    (weightedKernel_continuous E rate (K i) (hK i)) (C i) (hC i)
    (weightedKernel_bound E hrate (hC i) (K i) (hbound i))).comp (coefficientOperator E (A i))

theorem familyOperator_apply {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (rate : ℝ) (hrate : 0 ≤ rate)
    (u : Path E T) (t : Icc (0 : ℝ) T) :
    familyOperator E hT K hK C hC hbound A rate hrate u t =
      ∑ i, ∫ s in 0..t.val, Real.exp (-rate * (t.val-s)) •
        K i (t.val-s) (A i (projIcc 0 T hT s) (extendPath E hT u s)) := by
  have hsum (v : ι → Path E T) : (∑ i, v i) t = ∑ i, v i t := by
    change (ContinuousMap.evalCLM ℝ t) ((pathEquiv E T) (∑ i, v i)) = _
    simp only [map_sum]
    rfl
  simp only [familyOperator, sum_apply, ContinuousLinearMap.comp_apply]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem familyOperator_zero_apply {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u : Path E T) (t : Icc (0 : ℝ) T) :
    familyOperator E hT K hK C hC hbound A 0 le_rfl u t =
      ∑ i, ∫ s in 0..t.val,
        K i (t.val-s) (A i (projIcc 0 T hT s) (extendPath E hT u s)) := by
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using
    familyOperator_apply E hT K hK C hC hbound A 0 le_rfl u t

theorem norm_familyOperator_le {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (rate : ℝ) (hrate : 0 ≤ rate) :
    ‖familyOperator E hT K hK C hC hbound A rate hrate‖ ≤
      (∑ i, C i * ‖A i‖) * ∫ r in 0..T, weightedProfile rate r := by
  have hm : 0 ≤ ∫ r in 0..T, weightedProfile rate r :=
    intervalIntegral.integral_nonneg hT (fun r _ => weightedProfile_nonneg rate r)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, (C i * ∫ r in 0..T, weightedProfile rate r) * ‖A i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact ((ContinuousLinearMap.opNorm_comp_le _ _)).trans <|
        mul_le_mul (norm_weightedIntegralOperator_le E hT hrate (K i) (hK i) (hC i) (hbound i))
          (norm_coefficientOperator_le E (A i)) (norm_nonneg _) (mul_nonneg (hC i) hm)
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

theorem exists_familyOperator_contraction {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ∃ rate : ℝ, ∃ hrate : 0 ≤ rate,
      ‖familyOperator E hT K hK C hC hbound A rate hrate‖ < 1 := by
  have ht : Tendsto (fun rate : ℝ => (∑ i, C i * ‖A i‖) *
      ∫ r in 0..T, weightedProfile rate r) atTop (𝓝 0) := by
    simpa only [mul_zero] using (weightedProfile_integral_tendsto hT).const_mul (∑ i, C i * ‖A i‖)
  have he := (tendsto_order.1 ht).2 1 zero_lt_one
  obtain ⟨rate, hrate, hsmall⟩ := (eventually_ge_atTop (0 : ℝ)).and he |>.exists
  exact ⟨rate, hrate, (norm_familyOperator_le E hT K hK C hC hbound A rate hrate).trans_lt hsmall⟩

theorem weight_familyOperator {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (rate : ℝ) (hrate : 0 ≤ rate)
    (u : Path E T) :
    weightOperator E T (-rate) (familyOperator E hT K hK C hC hbound A 0 le_rfl u) =
      familyOperator E hT K hK C hC hbound A rate hrate (weightOperator E T (-rate) u) := by
  apply (pathEquiv E T).injective
  ext t
  simp only [weightOperator_apply, familyOperator_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.property.2⟩
  have hp : (projIcc 0 T hT s : ℝ) = s := by rw [projIcc_of_mem hT hsT]
  have hexp : Real.exp (-rate * t.val) =
      Real.exp (-rate * (t.val-s)) * Real.exp (-rate * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [zero_mul, neg_zero, Real.exp_zero, one_smul, extendPath, weightOperator_apply,
    hp, map_smul, ← smul_smul, hexp]

variable [CompleteSpace E]

/-- A finite family of weakly singular kernels has a unique continuous solution on any finite slab. -/
theorem exists_unique_family_equation {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (a : Path E T) :
    ∃! u : Path E T, u = a + familyOperator E hT K hK C hC hbound A 0 le_rfl u := by
  obtain ⟨rate, hrate, hcontract⟩ := exists_familyOperator_contraction E hT K hK C hC hbound A
  let L := familyOperator E hT K hK C hC hbound A rate hrate
  let b := weightOperator E T (-rate) a
  let w := JetVolterra.solution (Path E T) b L hcontract
  have hw : w = b + L w := JetVolterra.solution_eq (Path E T) b L hcontract
  let u := weightOperator E T rate w
  have hu : weightOperator E T (-rate) u = w := weightOperator_inverse E T rate w
  refine ⟨u, ?_, ?_⟩
  · apply weightOperator_injective E T (-rate)
    rw [map_add, weight_familyOperator E hT K hK C hC hbound A rate hrate, hu]
    exact hw
  · intro v hv
    have hv' : weightOperator E T (-rate) v = b + L (weightOperator E T (-rate) v) := by
      calc
        _ = weightOperator E T (-rate) (a + familyOperator E hT K hK C hC hbound A 0 le_rfl v) :=
          congrArg (weightOperator E T (-rate)) hv
        _ = _ := by rw [map_add, weight_familyOperator E hT K hK C hC hbound A rate hrate]
    have he := JetVolterra.solution_unique (Path E T) b L hcontract _ hv'
    apply weightOperator_injective E T (-rate)
    exact he.trans hu.symm

/-- Pointwise form of the unique equation, with the actual finite sum of time integrals. -/
theorem exists_unique_integral_equation {T : ℝ} (hT : 0 ≤ T)
    (K : ι → ℝ → E →L[ℝ] E) (hK : ∀ i, ContinuousOn (K i) (Ioi 0))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i r, 0 ≤ r → ‖K i r‖ ≤ C i * inverseSqrt r)
    (A : ι → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (a : Path E T) :
    ∃! u : Path E T, ∀ t : Icc (0 : ℝ) T, u t = a t +
      ∑ i, ∫ s in 0..t.val,
        K i (t.val-s) (A i (projIcc 0 T hT s) (extendPath E hT u s)) := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_family_equation E hT K hK C hC hbound A a
  refine ⟨u, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun v : Path E T => v t) hu
    change u t = a t + familyOperator E hT K hK C hC hbound A 0 le_rfl u t at ht
    simpa only [familyOperator_zero_apply] using ht
  · intro v hv
    apply huniq v
    apply (pathEquiv E T).injective
    ext t
    change v t = a t + familyOperator E hT K hK C hC hbound A 0 le_rfl v t
    simpa only [familyOperator_zero_apply] using hv t

end ForcedComputation.WeaklySingular

end

end OAI
