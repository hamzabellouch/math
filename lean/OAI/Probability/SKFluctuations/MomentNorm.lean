import Mathlib
import OAI.Probability.SKFluctuations.CompContDiff

namespace OAI

/-! Moment Norm. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]

 def momentNorm (μ : Measure E) (A : E → ℝ) (p : ℝ) : ℝ :=
  (eLpNorm A (ENNReal.ofReal p) μ).toReal

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasure μ] in
 theorem momentNorm_nonneg (A : E → ℝ) (p : ℝ) : 0 ≤ momentNorm μ A p := ENNReal.toReal_nonneg

 theorem momentNorm_eq {A : E → ℝ} (hA : BddSmooth 0 A) {p : ℝ} (hp : 0 < p) :
    momentNorm μ A p = (∫ x, |A x|^p ∂μ)^(1/p) := by
  unfold momentNorm
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top (hA.memLp _)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, one_div]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _)]

 theorem momentNorm_rpow {A : E → ℝ} (hA : BddSmooth 0 A) {p : ℝ} (hp : 0 < p) :
    (momentNorm μ A p)^p = ∫ x, |A x|^p ∂μ := by
  rw [momentNorm_eq hA hp, ← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

 theorem momentNorm_mono [IsProbabilityMeasure μ] {A : E → ℝ} (hA : BddSmooth 0 A)
    {p q : ℝ} (hpq : p ≤ q) : momentNorm μ A p ≤ momentNorm μ A q := by
  exact ENNReal.toReal_mono (hA.memLp (ENNReal.ofReal q)).ne
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq))

 omit [MeasurableSpace E] [BorelSpace E] in
 theorem BddSmooth.abs_rpow_zero {A : E → ℝ} (hA : BddSmooth 0 A) {p : ℝ} (hp : 0 ≤ p) :
    BddSmooth 0 (fun x => |A x|^p) := by
  obtain ⟨B,hB,hAb⟩ := hA.bound
  refine ⟨(Real.continuous_rpow_const hp).comp hA.continuous.abs,
    B^p, Real.rpow_nonneg hB _, fun x => ?_⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hAb x) hp

 theorem momentNorm_holder [IsProbabilityMeasure μ] {A J : E → ℝ}
    (hA : BddSmooth 0 A) (hJ : BddSmooth 0 J) (hJ0 : ∀ x, 0 ≤ J x)
    {p : ℝ} (hp : 2 < p) :
    (∫ x, |A x|^(p-2)*J x ∂μ) ≤ (momentNorm μ A p)^(p-2)*momentNorm μ J (p/2) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hc : (p/(p-2)).HolderConjugate (p/2) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hpm]; linarith
    · field_simp
      ring
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hc
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (A x)) (p-2))
    (ae_of_all _ hJ0) ((hA.abs_rpow_zero hpm.le).memLp _) (hJ.memLp _)
  have hprod : (p-2)*(p/(p-2)) = p := by field_simp
  have he (x : E) : (|A x|^(p-2))^(p/(p-2)) = |A x|^p := by
    rw [← Real.rpow_mul (abs_nonneg _), hprod]
  simp_rw [he] at h
  rw [momentNorm_eq hA hp0, momentNorm_eq hJ (by linarith)]
  rw [← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg (A x)) _)]
  have hq : (1/p)*(p-2) = 1/(p/(p-2)) := by field_simp
  rw [hq]
  simpa only [abs_of_nonneg (hJ0 _)] using h

 theorem norm_power_step {x y j p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hj : 0 ≤ j)
    (hp : 2 < p) (hyx : y ≤ x)
    (h : x^p ≤ y^p + (p^2/4)*x^(p-2)*j) :
    x^2 ≤ y^2 + (p^2/4)*j := by
  by_cases hx0 : x = 0
  · subst x
    norm_num only [zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hbase : y^p ≤ y^2*x^(p-2) := by
    have he : y^p = y^2*y^(p-2) := by
      rw [← Real.rpow_two, ← Real.rpow_add' hy (by linarith : (2 : ℝ)+(p-2) ≠ 0)]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy hyx (by linarith)) (sq_nonneg y)
  have he : x^p = x^2*x^(p-2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hxpos]
    congr 1
    ring
  rw [he] at h
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hxpos (p-2))).mp
  nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

 theorem momentNorm_two_sq {A : E → ℝ} (hA : BddSmooth 0 A) :
    (momentNorm μ A 2)^2 = ∫ x, (A x)^2 ∂μ := by
  have hh := momentNorm_rpow (μ := μ) hA (by norm_num : (0 : ℝ) < 2)
  simpa only [Real.rpow_two, sq_abs] using hh

 theorem momentNorm_half_pow {A : E → ℝ} (hA : BddSmooth 0 A) {p : ℝ} (hp : 0 < p) :
    (momentNorm μ A (p/2))^p = (∫ x, |A x|^(p/2) ∂μ)^2 := by
  calc
    _ = ((momentNorm μ A (p/2))^(p/2))^2 := by
      rw [← Real.rpow_two, ← Real.rpow_mul (momentNorm_nonneg _ _)]
      congr 1
      ring
    _ = _ := by rw [momentNorm_rpow hA (by linarith)]

 theorem momentNorm_nonneg_one {J : E → ℝ} (hJ : BddSmooth 0 J) (hJ0 : ∀ x, 0 ≤ J x) :
    momentNorm μ J 1 = ∫ x, J x ∂μ := by
  rw [momentNorm_eq hJ (by norm_num)]
  simp only [Real.rpow_one, one_div_one, abs_of_nonneg (hJ0 _)]

 theorem momentNorm_recurrence {A J : E → ℝ}
    (hA : BddSmooth 0 A) (hJ : BddSmooth 0 J) (hJ0 : ∀ x, 0 ≤ J x)
    {p : ℝ} (hp : 2 < p)
    (h : (∫ x, |A x|^p ∂μ) ≤ (∫ x, |A x|^(p/2) ∂μ)^2 +
      (p^2/4)*(∫ x, |A x|^(p-2)*J x ∂μ)) :
    (momentNorm μ A p)^2 ≤ (momentNorm μ A (p/2))^2 +
      (p^2/4)*momentNorm μ J (p/2) := by
  apply norm_power_step (momentNorm_nonneg _ _) (momentNorm_nonneg _ _)
    (momentNorm_nonneg _ _) hp (momentNorm_mono hA (by linarith))
  rw [momentNorm_rpow hA (by linarith), momentNorm_half_pow hA (by linarith)]
  calc
    _ ≤ (∫ x, |A x|^(p/2) ∂μ)^2 + (p^2/4)*(∫ x, |A x|^(p-2)*J x ∂μ) := h
    _ ≤ (∫ x, |A x|^(p/2) ∂μ)^2 + (p^2/4)*((momentNorm μ A p)^(p-2)*momentNorm μ J (p/2)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (momentNorm_holder (μ := μ) hA hJ hJ0 hp) (show 0 ≤ p^2/4 by positivity))
    _ = _ := by ring

 theorem real_moment_constant {A J : E → ℝ}
    (hA : BddSmooth 0 A) (hJ : BddSmooth 0 J)
    (hbase : (momentNorm μ A 2)^2 ≤ momentNorm μ J 1)
    (hstep : ∀ p : ℝ, 2 < p → (momentNorm μ A p)^2 ≤
      (momentNorm μ A (p/2))^2 + (p^2/4)*momentNorm μ J (p/2))
    {p : ℝ} (hp : 2 ≤ p) :
    (momentNorm μ A p)^2 ≤ (1+p^2/3)*momentNorm μ J (p/2) := by
  have bound : ∀ N : ℕ, ∀ p : ℝ, 2 ≤ p → p ≤ (N : ℝ) →
      (momentNorm μ A p)^2 ≤ (1+p^2/3)*momentNorm μ J (p/2) := by
    intro N
    induction N with
    | zero => intro p hp hpN; norm_num at hpN; linarith
    | succ N ih =>
      intro p hp hpN
      have hmonoJ : momentNorm μ J 1 ≤ momentNorm μ J (p/2) :=
        momentNorm_mono hJ (by linarith)
      have hJnn := momentNorm_nonneg (μ := μ) J (p/2)
      by_cases hp2 : p = 2
      · subst p
        have hB : (momentNorm μ A 2)^2 ≤ momentNorm μ J (2/2) := hbase.trans hmonoJ
        nlinarith
      have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
      have hh := hstep p hpgt
      by_cases hp4 : p ≤ 4
      · have hsmall := momentNorm_mono (μ := μ) hA (show p/2 ≤ 2 by linarith)
        have hc : (momentNorm μ A (p/2))^2 ≤ (momentNorm μ A 2)^2 :=
          sq_le_sq₀ (momentNorm_nonneg _ _) (momentNorm_nonneg _ _) |>.mpr hsmall
        have hcoeff : 0 ≤ p^2*momentNorm μ J (p/2) := mul_nonneg (sq_nonneg p) hJnn
        nlinarith
      · have hp4' : 4 < p := lt_of_not_ge hp4
        have hpN' : p ≤ (N : ℝ)+1 := by simpa only [Nat.cast_add, Nat.cast_one] using hpN
        have hhalf := ih (p/2) (by linarith) (by linarith)
        have hm := momentNorm_mono (μ := μ) hJ (show (p/2)/2 ≤ p/2 by linarith)
        have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+(p/2)^2/3 by positivity)
        nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt p
  exact bound N p hp hN.le

 theorem bl_real_moment_bound {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hJ0 : ∀ x, 0 ≤ J x) (hmean : ∫ x, A x ∂μ = 0)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x)
    {p : ℝ} (hp : 2 ≤ p) :
    (momentNorm μ A p)^2 ≤ (1+p^2/3)*momentNorm μ J (p/2) := by
  apply real_moment_constant hA.down.down hJ.down.down ?_ ?_ hp
  · have hv := variance_le_BddSmooth_block hμ hU hUc DU hA hJ hstrong hblock
    rw [variance_eq_sub (hA.memLp 2), hmean] at hv
    rw [momentNorm_two_sq hA.down.down, momentNorm_nonneg_one hJ.down.down hJ0]
    simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hv
  · intro q hq
    exact momentNorm_recurrence hA.down.down hJ.down.down hJ0 hq
      (power_moment_le hμ hU hUc DU hA hJ hJ0 hstrong hblock hq)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa

 theorem bl_centered_moment_bound {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hJ0 : ∀ x, 0 ≤ J x)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x)
    {p : ℝ} (hp : 2 ≤ p) :
    (momentNorm μ (fun x => A x - ∫ y, A y ∂μ) p)^2 ≤
      (1+p^2/3)*momentNorm μ J (p/2) := by
  have hAs : BddSmooth 2 (fun x => A x - ∫ y, A y ∂μ) := hA.sub (BddSmooth.const 2 _)
  apply bl_real_moment_bound hμ hU hUc DU hAs hJ hJ0 ?_ hstrong ?_ hp
  · rw [integral_sub hA.integrable (integrable_const _), integral_const]
    simp
  · intro x v s
    have he : lineDeriv ℝ (fun x => A x - ∫ y, A y ∂μ) x v = lineDeriv ℝ A x v := by
      apply HasLineDerivAt.lineDeriv
      simpa only [zero_smul, add_zero, HasLineDerivAt] using
        (hA.down.hasDerivAt_line x v 0).sub_const (∫ y, A y ∂μ)
    rw [he]
    exact hblock x v s

variable {ι S κ τ : Type*} [Fintype ι] [Fintype S] [Nonempty S] [Fintype κ] [Fintype τ] {n : ℕ}

 theorem PinFrame.energy_nonneg (P : PinFrame ι S κ n) (σ : S) (x : Fin n → ℝ) :
    0 ≤ P.energy σ x := by
  rw [PinFrame.energy, driverEnergy_eq P.weight_pos P.feature P.steps P.ordered]
  exact gaussianHierarchyHessian_nonneg P.weight_pos P.feature P.steps P.ordered _ _

 theorem pinnedEnergy_nonneg (P : τ → PinFrame ι S κ n) {α : τ → ℝ} (hα : ∀ j, 0 ≤ α j)
    (k : τ → ℝ) (σ : S) (x : Fin n → ℝ) : 0 ≤ pinnedEnergy P α k σ x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hα j) (sq_nonneg _))
    ((P j).energy_nonneg σ x)

omit [Fintype κ] in
 theorem pinnedPotential_continuous (P : τ → PinFrame ι S κ n) (α : τ → ℝ)
    (ell : (Fin n → ℝ) →L[ℝ] ℝ) : Continuous (pinnedPotential P α ell) := by
  unfold pinnedPotential
  apply Continuous.add
  · exact (show Continuous (driverQuadratic (n := n)) from by unfold driverQuadratic; fun_prop).sub ell.continuous
  · apply continuous_finsetSum
    intro j _
    obtain ⟨C,hC⟩ := (P j).potential_lipschitz
    exact hC.continuous.const_mul (α j)

 

 theorem pinned_centered_moment_le (P : τ → PinFrame ι S κ n) {α : τ → ℝ} (hα : ∀ j, 0 ≤ α j)
    (k : τ → ℝ) (σ : S) (ell : (Fin n → ℝ) →L[ℝ] ℝ) {p : ℝ} (hp : 2 ≤ p) :
    let μ := potentialLaw (pinnedPotential P α ell)
    (momentNorm μ (fun x => pinnedObservable P α k σ x - ∫ y, pinnedObservable P α k σ y ∂μ) p)^2 ≤
      (1+p^2/3)*momentNorm μ (pinnedEnergy P α k σ) (p/2) := by
  dsimp only
  have hU := pinnedPotential_gaussianDominated P α ell
  have : IsProbabilityMeasure (potentialLaw (pinnedPotential P α ell)) := potentialLaw_isProbability hU
  apply bl_centered_moment_bound (μ := potentialLaw (pinnedPotential P α ell))
    (U := normalizedPotential (pinnedPotential P α ell)) rfl
    (gaussianDominated_normalizedPotential hU) ((pinnedPotential_continuous P α ell).add continuous_const)
    ((pinnedPotential_derivatives P α ell).const_add _)
    (pinnedObservable_smooth P α k σ 2) (pinnedEnergy_smooth P α k σ 2)
    (pinnedEnergy_nonneg P hα k σ) (pinnedPotential_strong P hα ell)
    (pinnedPotential_block P hα k σ ell) hp

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

 

 def plantedTransitionDensity (ν : Measure E) (m : ℝ) (F : E → ℝ) (x z : E) : ℝ :=
    Real.exp (m*(F (x+z)-shiftedContinuation ν m F x))

 theorem plantedTransitionDensity_eq {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x z : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    plantedTransitionDensity ν m F x z = Real.exp (m*F (x+z)) /
      (∫ y, Real.exp (m*F (x+y)) ∂ν) := by
  rw [plantedTransitionDensity, mul_sub, Real.exp_sub, shiftedContinuation,
    mul_div_cancel₀ _ hm, Real.exp_log (partition_pos m hi)]

 theorem plantedTransitionDensity_integrable {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    Integrable (plantedTransitionDensity ν m F x) ν := by
  have he : plantedTransitionDensity ν m F x =
      fun z => Real.exp (m*F (x+z)) / (∫ y, Real.exp (m*F (x+y)) ∂ν) := by
    funext z
    exact plantedTransitionDensity_eq hm x z hi
  rw [he]
  exact hi.div_const _

 theorem integral_plantedTransitionDensity {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    (∫ z, plantedTransitionDensity ν m F x z ∂ν) = 1 := by
  simp_rw [plantedTransitionDensity_eq hm _ _ hi]
  rw [integral_div, div_self (partition_pos m hi).ne']

 theorem lintegral_plantedTransitionDensity {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    (∫⁻ z, ENNReal.ofReal (plantedTransitionDensity ν m F x z) ∂ν) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (plantedTransitionDensity_integrable hm x hi)
    (Eventually.of_forall fun _ => Real.exp_nonneg _), integral_plantedTransitionDensity hm x hi]
  exact ENNReal.ofReal_one

 theorem plantedTransitionLaw_eq {m : ℝ} (hm : m ≠ 0) {F : E → ℝ} (x : E)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    ν.withDensity (fun z => ENNReal.ofReal (plantedTransitionDensity ν m F x z)) =
      tiltedLaw ν m (fun z => F (x+z)) := by
  simp only [plantedTransitionDensity_eq hm _ _ hi, tiltedLaw]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 

def standardDrivers (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure (standardDrivers ι) := by unfold standardDrivers; infer_instance

def scaleDriver (q : ι → ℝ≥0) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => Real.sqrt (q i : ℝ) • ContinuousLinearMap.proj i

omit [Fintype ι] in
@[simp] theorem scaleDriver_apply (q : ι → ℝ≥0) (z : ι → ℝ) (i : ι) :
    scaleDriver q z i = Real.sqrt (q i : ℝ) * z i := by simp [scaleDriver]

 theorem scaleDriver_gaussian (q : ι → ℝ≥0) :
    MeasurePreserving (scaleDriver q) (standardDrivers ι)
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
  apply measurePreserving_pi (fun _ => gaussianReal 0 1) (fun i => gaussianReal 0 (q i))
  intro i
  change MeasurePreserving (fun z : ℝ => Real.sqrt (q i : ℝ) * z) _ _
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  change Real.sqrt (q i : ℝ)^2 * 1 = (q i : ℝ)
  rw [mul_one, Real.sq_sqrt (q i).coe_nonneg]

variable {S : Type*} [Fintype S] [Nonempty S]

 theorem gaussianHierarchy_lipschitz {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) : ∃ C, LipschitzWith C (gaussianHierarchy w φ steps) := by
  obtain ⟨T,hF,_,_⟩ := gaussianHierarchy_source hw φ 0 steps ha
  rw [← hF]
  exact (T.regular 0).1

 theorem gaussianHierarchy_continuous {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) : Continuous (gaussianHierarchy w φ steps) := by
  obtain ⟨C,hC⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  exact hC.continuous

 theorem gaussianHierarchy_exp_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (q : ι → ℝ≥0) (m : ℝ) (x : ι → ℝ) :
    Integrable (fun z => Real.exp (m*gaussianHierarchy w φ steps (x+z)))
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
  obtain ⟨C,hC⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  exact (exponentialIncrement_gaussian q).integrable_shift hC m x

 theorem lintegral_scaled_transition {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a m : ℝ} (ha : OrderedSteps a steps) (hm : m ≠ 0) (q : ι → ℝ≥0) (x : ι → ℝ) :
    (∫⁻ z, ENNReal.ofReal (plantedTransitionDensity (Measure.pi fun i => gaussianReal 0 (q i))
      m (gaussianHierarchy w φ steps) x (scaleDriver q z)) ∂standardDrivers ι) = 1 := by
  have hmeas : Measurable (fun z => ENNReal.ofReal (plantedTransitionDensity
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ steps) x z)) := by
    apply Measurable.ennreal_ofReal
    exact (Real.continuous_exp.comp (((gaussianHierarchy_continuous hw φ steps ha).comp
      (continuous_const.add continuous_id)).sub continuous_const |>.const_mul m)).measurable
  exact ((scaleDriver_gaussian q).lintegral_comp hmeas).trans
    (lintegral_plantedTransitionDensity hm x
      (gaussianHierarchy_exp_integrable hw φ steps ha q m x))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped ENNReal

 theorem lintegral_fin_cons {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Fin (n+1) → Measure E) [∀ i, SigmaFinite (μ i)] {f : (Fin (n+1) → E) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ p, f p ∂Measure.pi μ) =
      ∫⁻ z, ∫⁻ p, f (Fin.cons z p) ∂Measure.pi (fun i => μ i.succ) ∂μ 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0
  have hp := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [← hp.lintegral_comp_emb e.symm.measurableEmbedding f]
  rw [lintegral_prod _ (show AEMeasurable (fun a => f (e.symm a)) _ from
    (hf.comp e.symm.measurable).aemeasurable)]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {E D : Type*} [AddCommMonoid E] [MeasurableSpace E]
  [MeasurableAdd₂ E] [MeasurableSpace D]

 

def forwardWeight : (n : ℕ) → (Fin n → D → E) →
    (Fin n → E → D → ℝ≥0∞) → E → (Fin n → D) → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | n+1, inc, T, x, p => T 0 x (p 0) *
      forwardWeight n (fun i => inc i.succ) (fun i => T i.succ)
        (x + inc 0 (p 0)) (Fin.tail p)

def forwardEnd : (n : ℕ) → (Fin n → D → E) → E → (Fin n → D) → E
  | 0, _, x, _ => x
  | n+1, inc, x, p => forwardEnd n (fun i => inc i.succ)
      (x + inc 0 (p 0)) (Fin.tail p)

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSpace D] in
 theorem forwardEnd_eq_sum (n : ℕ) (inc : Fin n → D → E) (x : E) (p : Fin n → D) :
    forwardEnd n inc x p = x + ∑ i, inc i (p i) := by
  induction n generalizing x with
  | zero => simp [forwardEnd]
  | succ n ih =>
    simp only [forwardEnd, ih, Fin.sum_univ_succ, Fin.tail, add_assoc]

 theorem measurable_forwardEnd (n : ℕ) {inc : Fin n → D → E}
    (hinc : ∀ i, Measurable (inc i)) :
    Measurable (fun xp : E × (Fin n → D) => forwardEnd n inc xp.1 xp.2) := by
  simp only [forwardEnd_eq_sum]
  exact measurable_fst.add (Finset.measurable_sum _ (fun i _ =>
    (hinc i).comp ((measurable_pi_apply i).comp measurable_snd)))

 theorem measurable_forwardWeight (n : ℕ) {inc : Fin n → D → E}
    {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i))
    (hT : ∀ i, Measurable (Function.uncurry (T i))) :
    Measurable (fun xp : E × (Fin n → D) => forwardWeight n inc T xp.1 xp.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have ht : Measurable (fun xp : E × (Fin (n+1) → D) => T 0 xp.1 (xp.2 0)) :=
      (hT 0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hs : Measurable (fun xp : E × (Fin (n+1) → D) =>
        (xp.1 + inc 0 (xp.2 0), Fin.tail xp.2)) :=
      (measurable_fst.add ((hinc 0).comp ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd))
    exact ht.mul ((ih (fun i => hinc i.succ) (fun i => hT i.succ)).comp hs)

 theorem lintegral_forwardWeight (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E}
    {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i))
    (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1) (x : E) :
    (∫⁻ p, forwardWeight n inc T x p ∂Measure.pi μ) = 1 := by
  induction n generalizing x with
  | zero => simp [forwardWeight]
  | succ n ih =>
    have hm : Measurable (forwardWeight (n+1) inc T x) :=
      (measurable_forwardWeight _ hinc hT).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_fin_cons μ hm]
    simp only [forwardWeight, Fin.cons_zero, Fin.tail_cons]
    have hi (z : D) :
        (∫⁻ p, T 0 x z * forwardWeight n (fun i => inc i.succ) (fun i => T i.succ)
          (x+inc 0 z) p ∂Measure.pi (fun i => μ i.succ)) = T 0 x z := by
      have hm : Measurable (forwardWeight n (fun i => inc i.succ) (fun i => T i.succ)
          (x+inc 0 z)) := (measurable_forwardWeight _ (fun i => hinc i.succ)
          (fun i => hT i.succ)).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hm, ih (fun i => μ i.succ) (fun i => hinc i.succ)
        (fun i => hT i.succ) (fun i => h1 i.succ), mul_one]
    simp_rw [hi]
    exact h1 0 x

 

 theorem sum_lintegral_forward_terminal {S : Type*} [Fintype S]
    (n : ℕ) (μ : Fin n → Measure D) [∀ i, IsProbabilityMeasure (μ i)]
    {inc : Fin n → D → E} {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i))
    (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1)
    (W : E → S → ℝ≥0∞) (hW : ∀ s, Measurable (fun x => W x s))
    (hsum : ∀ x, ∑ s, W x s = 1) (x : E) :
    (∑ s, ∫⁻ p, forwardWeight n inc T x p * W (forwardEnd n inc x p) s
      ∂Measure.pi μ) = 1 := by
  have hp : Measurable (forwardWeight n inc T x) := (measurable_forwardWeight _ hinc hT).comp
    (measurable_const.prodMk measurable_id)
  have he : Measurable (forwardEnd n inc x) := (measurable_forwardEnd _ hinc).comp
    (measurable_const.prodMk measurable_id)
  rw [← lintegral_finsetSum Finset.univ (fun s _ => show Measurable
    (fun p => forwardWeight n inc T x p * W (forwardEnd n inc x p) s) from
      hp.mul ((hW s).comp he))]
  simp_rw [← Finset.mul_sum, hsum, mul_one]
  exact lintegral_forwardWeight n μ hinc hT h1 x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def hierarchyIncrements : (steps : List (GaussianStep ι)) →
    Fin steps.length → (ι → ℝ) → (ι → ℝ)
  | [] => fun i => Fin.elim0 i
  | (_,q)::tail => Fin.cons (scaleDriver q) (hierarchyIncrements tail)

 

def hierarchyTransitions (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (steps : List (GaussianStep ι)) → Fin steps.length → (ι → ℝ) → (ι → ℝ) → ℝ≥0∞
  | [] => fun i => Fin.elim0 i
  | (m,q)::tail => Fin.cons
      (fun x z => ENNReal.ofReal (Real.exp (m * (gaussianHierarchy w φ tail (x+scaleDriver q z) -
        gaussianHierarchy w φ ((m,q)::tail) x)))) (hierarchyTransitions w φ tail)

 theorem hierarchyIncrements_measurable (steps : List (GaussianStep ι)) :
    ∀ i, Measurable (hierarchyIncrements steps i) := by
  induction steps with
  | nil => intro i; exact Fin.elim0 i
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    exact Fin.cases (scaleDriver q).measurable ih

 theorem hierarchyTransitions_measurable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) :
    ∀ i, Measurable (Function.uncurry (hierarchyTransitions w φ steps i)) := by
  induction steps generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2)
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    apply Real.continuous_exp.comp
    apply Continuous.const_mul
    exact ((gaussianHierarchy_continuous hw φ tail ha.2.2.2).comp
      (continuous_fst.add ((scaleDriver q).continuous.comp continuous_snd))).sub
      ((gaussianHierarchy_continuous hw φ ((m,q)::tail) ha).comp continuous_fst)

 theorem hierarchyTransitions_normalized {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) : ∀ i x,
    (∫⁻ z, hierarchyTransitions w φ steps i x z ∂standardDrivers ι) = 1 := by
  induction steps generalizing a with
  | nil => intro i; exact Fin.elim0 i
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    refine Fin.cases ?_ (ih ha.2.2.2)
    intro x
    exact lintegral_scaled_transition hw φ tail ha.2.2.2 ha.2.2.1.ne' q x

def hierarchyPathLog (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (steps : List (GaussianStep ι)) → (ι → ℝ) → (Fin steps.length → (ι → ℝ)) → ℝ
  | [], _, _ => 0
  | (m,q)::tail, x, p => m * (gaussianHierarchy w φ tail (x+scaleDriver q (p 0)) -
      gaussianHierarchy w φ ((m,q)::tail) x) +
      hierarchyPathLog w φ tail (x+scaleDriver q (p 0)) (Fin.tail p)

 

def hierarchyPathCost (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (steps : List (GaussianStep ι)) → ℝ → (ι → ℝ) → (Fin steps.length → (ι → ℝ)) → ℝ
  | [], a, x, _ => (1-a)*spinLogPartition w φ x
  | (m,q)::tail, a, x, p => (m-a)*gaussianHierarchy w φ ((m,q)::tail) x +
      hierarchyPathCost w φ tail m (x+scaleDriver q (p 0)) (Fin.tail p)

omit [Nonempty S] in
 theorem hierarchyPathWeight_eq (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (x : ι → ℝ) (p : Fin steps.length → (ι → ℝ)) :
    forwardWeight steps.length (hierarchyIncrements steps) (hierarchyTransitions w φ steps) x p =
      ENNReal.ofReal (Real.exp (hierarchyPathLog w φ steps x p)) := by
  induction steps generalizing x with
  | nil => simp [forwardWeight, hierarchyPathLog]
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    simp only [List.length_cons, forwardWeight, hierarchyIncrements, hierarchyTransitions,
      Fin.cons_zero, Fin.cons_succ, hierarchyPathLog, ih, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]

omit [Nonempty S] in
 theorem hierarchyPathLog_telescope (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (a : ℝ) (x : ι → ℝ)
    (p : Fin steps.length → (ι → ℝ)) :
    hierarchyPathLog w φ steps x p -
      spinLogPartition w φ (forwardEnd steps.length (hierarchyIncrements steps) x p) =
    -a*gaussianHierarchy w φ steps x - hierarchyPathCost w φ steps a x p := by
  induction steps generalizing a x with
  | nil => simp only [hierarchyPathLog, List.length_nil, forwardEnd,
      gaussianHierarchy, hierarchyPathCost]; ring
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    simp only [hierarchyPathLog, List.length_cons, forwardEnd, hierarchyIncrements,
      Fin.cons_zero, Fin.cons_succ, hierarchyPathCost]
    have h := ih m (x+scaleDriver q (p 0)) (Fin.tail p)
    linarith

 

def hierarchyJointDensity (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (x : ι → ℝ) (p : Fin steps.length → (ι → ℝ)) (σ : S) : ℝ :=
  Real.exp (hierarchyPathLog w φ steps x p) *
    spinWeight w φ (forwardEnd steps.length (hierarchyIncrements steps) x p) σ

 theorem hierarchyJointDensity_eq {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (a : ℝ) (x : ι → ℝ)
    (p : Fin steps.length → (ι → ℝ)) (σ : S) :
    hierarchyJointDensity w φ steps x p σ = w σ * Real.exp
      (φ σ (forwardEnd steps.length (hierarchyIncrements steps) x p) -
        a*gaussianHierarchy w φ steps x - hierarchyPathCost w φ steps a x p) := by
  let y := forwardEnd steps.length (hierarchyIncrements steps) x p
  have htel := hierarchyPathLog_telescope w φ steps a x p
  change hierarchyPathLog w φ steps x p - spinLogPartition w φ y = _ at htel
  have he : φ σ y - a*gaussianHierarchy w φ steps x - hierarchyPathCost w φ steps a x p =
      φ σ y + (hierarchyPathLog w φ steps x p - spinLogPartition w φ y) := by linarith
  change Real.exp (hierarchyPathLog w φ steps x p) * spinWeight w φ y σ =
    w σ * Real.exp (φ σ y - a*gaussianHierarchy w φ steps x - hierarchyPathCost w φ steps a x p)
  rw [he, Real.exp_add, Real.exp_sub, spinWeight, spinLogPartition,
    Real.exp_log (spinPartition_pos hw φ y)]
  ring

 theorem hierarchyJointDensity_pos {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ)
    (p : Fin steps.length → (ι → ℝ)) (σ : S) : 0 < hierarchyJointDensity w φ steps x p σ := by
  rw [hierarchyJointDensity_eq hw φ steps 0 x p σ]
  exact mul_pos (hw _) (Real.exp_pos _)

 theorem hierarchyJointDensity_normalized {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (∑ σ, ∫⁻ p, ENNReal.ofReal (hierarchyJointDensity w φ steps x p σ)
      ∂Measure.pi (fun _ : Fin steps.length => standardDrivers ι)) = 1 := by
  have he (p : Fin steps.length → (ι → ℝ)) (σ : S) :
      ENNReal.ofReal (hierarchyJointDensity w φ steps x p σ) =
        forwardWeight steps.length (hierarchyIncrements steps) (hierarchyTransitions w φ steps) x p *
          ENNReal.ofReal (spinWeight w φ (forwardEnd steps.length (hierarchyIncrements steps) x p) σ) := by
    rw [hierarchyJointDensity, ENNReal.ofReal_mul (Real.exp_nonneg _), hierarchyPathWeight_eq]
  simp_rw [he]
  apply sum_lintegral_forward_terminal _ _ (hierarchyIncrements_measurable steps)
    (hierarchyTransitions_measurable hw φ steps ha) (hierarchyTransitions_normalized hw φ steps ha)
    (fun x σ => ENNReal.ofReal (spinWeight w φ x σ))
  · intro σ
    exact (continuous_spinWeight hw φ σ).measurable.ennreal_ofReal
  · intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => spinWeight_nonneg hw φ x σ), sum_spinWeight hw φ]
    exact ENNReal.ofReal_one

end SKFluctuations.Hierarchy

end

end OAI
