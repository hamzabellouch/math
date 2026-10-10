import Mathlib
import OAI.Probability.SKFluctuations.Terminal

namespace OAI

/-! Line Derivatives Sign Equiv Volume. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def BddSmooth.lineDerivatives {f : E → ℝ} (hf : BddSmooth 2 f) :
    LineDerivatives f where
  first x v := lineDeriv ℝ f x v
  second x v := lineDeriv ℝ (fun y => lineDeriv ℝ f y v) x v
  deriv_first := hf.down.hasDerivAt_line
  deriv_second x v t := (hf.lineDeriv_smooth v).hasDerivAt_line x v t

theorem variance_le_BddSmooth_block {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x) :
    variance A μ ≤ ∫ x, J x ∂μ := by
  obtain ⟨M₁, hM₁, hAb⟩ := hA.bound
  obtain ⟨M₂, hM₂, hJb⟩ := hJ.bound
  obtain ⟨B₁, hB₁, hA₂⟩ := hA.uniform_second_bound
  obtain ⟨B₂, hB₂, hJ₁⟩ := hJ.down.uniform_first_bound
  obtain ⟨B₃, hB₃, hJ₂⟩ := hJ.uniform_second_bound
  apply variance_le_of_block_hessian (M := M₁+M₂) (B := B₁+B₂+B₃) hμ
    (by positivity) (by positivity) hU hUc hA.continuous hJ.continuous
    DU hA.lineDerivatives hJ.lineDerivatives
    (fun x => (hAb x).trans (by linarith)) (fun x => (hJb x).trans (by linarith))
    hstrong hblock
  · intro x v
    exact (hA₂ x v).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  · intro x v
    exact (hJ₁ x v).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro x v
    exact (hJ₂ x v).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

 

structure PinFrame (ι S κ : Type*) [Fintype ι] [Fintype S] [Nonempty S] (n : ℕ) where
  weight : S → ℝ
  weight_pos : ∀ s, 0 < weight s
  feature : S → (ι → ℝ) →L[ℝ] ℝ
  steps : List (GaussianStep ι)
  mass : ℝ
  ordered : OrderedSteps mass steps
  driver : (Fin n → ℝ) →L[ℝ] (ι → ℝ)
  source : κ → ι → ℝ

variable {ι S κ : Type*} [Fintype ι] [Fintype S] [Nonempty S] [Fintype κ] {n : ℕ}
namespace PinFrame
variable (P : PinFrame ι S κ n)

def potential (x : Fin n → ℝ) : ℝ := gaussianHierarchy P.weight P.feature P.steps (P.driver x)
def observable (σ : S) : (Fin n → ℝ) → ℝ :=
  driverObservable P.weight P.feature P.steps P.driver P.source σ
def energy (σ : S) : (Fin n → ℝ) → ℝ :=
  driverEnergy P.weight P.feature P.steps P.driver P.source σ

def gradient (x v : Fin n → ℝ) : ℝ :=
  gaussianHierarchyMean P.weight P.feature (fun s => P.feature s (P.driver v)) P.steps (P.driver x)
def hessian (x v u : Fin n → ℝ) : ℝ :=
  gaussianHierarchyHessian P.weight P.feature P.steps (P.driver x) (P.driver v) (P.driver u)
def cross (σ : S) (x v : Fin n → ℝ) : ℝ :=
  gaussianHierarchyHessian P.weight P.feature P.steps (P.driver x)
    (driverSource P.weight P.feature P.steps P.driver P.source σ x) (P.driver v)

omit [Fintype κ] in
theorem potential_lipschitz : ∃ C : ℝ≥0, LipschitzWith C P.potential := by
  obtain ⟨C, hC⟩ := (gaussianHierarchy_regular P.weight_pos P.feature P.steps P.ordered 0).1
  exact ⟨C * ‖P.driver‖₊, hC.comp P.driver.lipschitzWith⟩

omit [Fintype κ] in
noncomputable def derivatives : LineDerivatives P.potential where
  first := P.gradient
  second x v := P.hessian x v v
  deriv_first x v t := by
    simpa only [gradient, potential, map_add, map_smul] using
      gaussianHierarchy_hasDerivAt P.weight_pos P.feature P.steps P.ordered (P.driver x) (P.driver v) t
  deriv_second x v t := by
    simpa only [gradient, hessian, gaussianHierarchyHessian, map_add, map_smul] using
      gaussianHierarchyMean_hasDerivAt P.weight_pos P.feature
        (fun s => P.feature s (P.driver v)) P.steps P.ordered (P.driver x) (P.driver v) t

omit [Fintype κ] in
theorem hessian_nonneg (x v : Fin n → ℝ) : 0 ≤ P.hessian x v v :=
  gaussianHierarchyHessian_nonneg P.weight_pos P.feature P.steps P.ordered _ _

theorem observable_smooth (σ : S) (k : ℕ) : BddSmooth k (P.observable σ) :=
  driverObservable_smooth P.weight_pos P.feature P.steps P.ordered P.driver P.source σ k

theorem energy_smooth (σ : S) (k : ℕ) : BddSmooth k (P.energy σ) :=
  driverEnergy_smooth P.weight_pos P.feature P.steps P.ordered P.driver P.source σ k

theorem cross_eq_lineDeriv (σ : S) (x v : Fin n → ℝ) :
    P.cross σ x v = lineDeriv ℝ (P.observable σ) x v := by
  symm
  apply HasLineDerivAt.lineDeriv
  simpa only [HasLineDerivAt, zero_smul, add_zero, observable, cross] using
    driverObservable_hasDerivAt P.weight_pos P.feature P.steps P.ordered P.driver P.source σ x v 0

theorem block_nonneg (σ : S) (x v : Fin n → ℝ) (c : ℝ) :
    0 ≤ P.hessian x v v - 2*c*P.cross σ x v + c^2*P.energy σ x := by
  rw [energy, driverEnergy_eq P.weight_pos P.feature P.steps P.ordered]
  unfold hessian cross
  rw [gaussianHierarchyHessian_symm P.weight P.feature P.steps (P.driver x)
    (driverSource P.weight P.feature P.steps P.driver P.source σ x) (P.driver v)]
  exact gaussianHierarchyHessian_block_nonneg P.weight_pos P.feature P.steps P.ordered _ _ _ c

end PinFrame
end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
open SKFluctuations.PreKopa SKFluctuations.PinnedVariance

theorem pi_norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖^2 ≤ ∑ i, (x i)^2 := by
  have hs : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm : ‖x‖ ≤ Real.sqrt (∑ i, (x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt hs, norm_nonneg x, Real.sqrt_nonneg (∑ i, (x i)^2)]

def driverQuadratic {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, (x i)^2) / 2

noncomputable def driverQuadratic_derivatives {n : ℕ} :
    LineDerivatives (driverQuadratic (n := n)) where
  first x v := ∑ i, x i * v i
  second _ v := ∑ i, (v i)^2
  deriv_first x v t := by
    have h := (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (((hasDerivAt_id t).mul_const (v i)).const_add (x i)).pow 2).div_const 2
    simp only [Finset.sum_fn] at h
    apply h.congr_deriv
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]
    ring
  deriv_second x v t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (((hasDerivAt_id t).mul_const (v i)).const_add (x i)).mul_const (v i)
    simp only [Finset.sum_fn] at h
    apply h.congr_deriv
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem gaussianDominated_quadratic_lipschitz {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    {C : ℝ≥0} (hG : LipschitzWith C G) :
    GaussianDominated (fun x => Real.exp (-(driverQuadratic x + G x))) := by
  refine ⟨Real.continuous_exp.comp (Continuous.neg ?_), Real.exp ((C:ℝ)^2 - G 0), 1/4,
      Real.exp_pos _, by norm_num, ?_⟩
  · exact (show Continuous (driverQuadratic (n := n)) from by unfold driverQuadratic; fun_prop).add hG.continuous
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [gaussianEnvelope, ← Real.exp_sum, ← Finset.mul_sum]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hg : |G x - G 0| ≤ (C:ℝ)*‖x‖ := by
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hG.dist_le_mul x 0
  have hq := pi_norm_sq_le_sum_sq x
  have hh := (abs_le.mp hg).1
  unfold driverQuadratic
  nlinarith [sq_nonneg ((C:ℝ) - ‖x‖/2)]

 

theorem positive_integral_exp_neg {n : ℕ} {U : (Fin n → ℝ) → ℝ}
    (hU : GaussianDominated (fun x => Real.exp (-U x))) :
    0 < ∫ x, Real.exp (-U x) := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => Real.exp_nonneg _) hU.integrable).mpr
  simp only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true, ofPred_true]
  exact Measure.measure_univ_pos.mpr (NeZero.ne volume)

def normalizedPotential {n : ℕ} (U : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  U x + Real.log (∫ z, Real.exp (-U z))

noncomputable def potentialLaw {n : ℕ} (U : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-normalizedPotential U x)))

theorem exp_neg_normalizedPotential {n : ℕ} {U : (Fin n → ℝ) → ℝ}
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (x : Fin n → ℝ) :
    Real.exp (-normalizedPotential U x) = Real.exp (-U x) / (∫ z, Real.exp (-U z)) := by
  rw [normalizedPotential, neg_add, Real.exp_add,
    Real.exp_neg (Real.log (∫ z, Real.exp (-U z))), Real.exp_log (positive_integral_exp_neg hU)]
  rfl

theorem gaussianDominated_normalizedPotential {n : ℕ} {U : (Fin n → ℝ) → ℝ}
    (hU : GaussianDominated (fun x => Real.exp (-U x))) :
    GaussianDominated (fun x => Real.exp (-normalizedPotential U x)) := by
  obtain ⟨hc, C, c, hC, hcp, hb⟩ := hU
  have hZ := positive_integral_exp_neg ⟨hc, C, c, hC, hcp, hb⟩
  have he := exp_neg_normalizedPotential ⟨hc, C, c, hC, hcp, hb⟩
  refine ⟨?_, C / (∫ z, Real.exp (-U z)), c, div_pos hC hZ, hcp, ?_⟩
  · simp_rw [he]
    exact hc.div_const _
  intro x
  dsimp only
  simp only [he, norm_div, Real.norm_eq_abs, abs_of_pos hZ]
  calc
    _ ≤ C * gaussianEnvelope c x / (∫ z, Real.exp (-U z)) := div_le_div_of_nonneg_right (hb x) hZ.le
    _ = C / (∫ z, Real.exp (-U z)) * gaussianEnvelope c x := by ring

theorem potentialLaw_isProbability {n : ℕ} {U : (Fin n → ℝ) → ℝ}
    (hU : GaussianDominated (fun x => Real.exp (-U x))) : IsProbabilityMeasure (potentialLaw U) := by
  constructor
  rw [potentialLaw, withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianDominated_normalizedPotential hU).integrable
    (Eventually.of_forall fun _ => Real.exp_nonneg _)]
  simp_rw [exp_neg_normalizedPotential hU]
  rw [integral_div, div_self (positive_integral_exp_neg hU).ne', ENNReal.ofReal_one]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa
variable {ι S κ τ : Type*} [Fintype ι] [Fintype S] [Nonempty S] [Fintype κ] [Fintype τ] {n : ℕ}

 

def pinnedPotential (P : τ → PinFrame ι S κ n) (α : τ → ℝ)
    (ell : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) : ℝ :=
  driverQuadratic x - ell x + ∑ j, α j * (P j).potential x

def pinnedObservable (P : τ → PinFrame ι S κ n) (α k : τ → ℝ) (σ : S)
    (x : Fin n → ℝ) : ℝ := ∑ j, α j * k j * (P j).observable σ x

def pinnedEnergy (P : τ → PinFrame ι S κ n) (α k : τ → ℝ) (σ : S)
    (x : Fin n → ℝ) : ℝ := ∑ j, α j * (k j)^2 * (P j).energy σ x

omit [Fintype κ] in
noncomputable def pinnedPotential_derivatives (P : τ → PinFrame ι S κ n) (α : τ → ℝ)
    (ell : (Fin n → ℝ) →L[ℝ] ℝ) : LineDerivatives (pinnedPotential P α ell) where
  first x v := (∑ i, x i*v i) - ell v + ∑ j, α j * (P j).gradient x v
  second x v := (∑ i, (v i)^2) + ∑ j, α j * (P j).hessian x v v
  deriv_first x v t := by
    have hdell : HasDerivAt (fun s : ℝ => ell (x+s•v)) (ell v) t := by
      simpa only [map_add, map_smul, smul_eq_mul, one_mul, id_eq] using
        (((hasDerivAt_id t).mul_const (ell v)).const_add (ell x))
    have h := ((driverQuadratic_derivatives.deriv_first x v t).sub hdell).add
      (HasDerivAt.sum (u := Finset.univ) fun j _ =>
        ((P j).derivatives.deriv_first x v t).const_mul (α j))
    simp only [Finset.sum_fn] at h
    exact h
  deriv_second x v t := by
    have h := ((driverQuadratic_derivatives.deriv_second x v t).sub_const (ell v)).add
      (HasDerivAt.sum (u := Finset.univ) fun j _ =>
        ((P j).derivatives.deriv_second x v t).const_mul (α j))
    simp only [Finset.sum_fn] at h
    exact h

omit [Fintype κ] in
theorem pinnedPotential_gaussianDominated (P : τ → PinFrame ι S κ n) (α : τ → ℝ)
    (ell : (Fin n → ℝ) →L[ℝ] ℝ) :
    GaussianDominated (fun x => Real.exp (-pinnedPotential P α ell x)) := by
  choose C hC using fun j => (P j).potential_lipschitz
  have hsum : ∀ s : Finset τ, ∃ K : ℝ≥0,
      LipschitzWith K (fun x => ∑ j ∈ s, α j * (P j).potential x) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simpa only [Finset.sum_empty] using LipschitzWith.const (0 : ℝ)⟩
    | @insert j s hj ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨K', hK'⟩ : ∃ K', LipschitzWith K' (fun x => α j * (P j).potential x) := by
        refine ⟨‖α j‖₊ * C j, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
        simp only [dist_eq_norm, ← mul_sub, norm_mul, NNReal.coe_mul, coe_nnnorm]
        exact (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (hC j).dist_le_mul x y)
          (norm_nonneg _)).trans_eq (by ring)
      refine ⟨K'+K, ?_⟩
      simpa only [Finset.sum_insert hj] using hK'.add hK
  obtain ⟨K, hK⟩ := hsum Finset.univ
  have hG := ell.lipschitzWith.neg.add hK
  have h := gaussianDominated_quadratic_lipschitz hG
  convert h using 1
  funext x
  congr 1
  unfold pinnedPotential
  simp only [Pi.neg_apply]
  ring

theorem pinnedObservable_smooth (P : τ → PinFrame ι S κ n) (α k : τ → ℝ)
    (σ : S) (r : ℕ) : BddSmooth r (pinnedObservable P α k σ) :=
  BddSmooth.sum Finset.univ fun j _ => ((P j).observable_smooth σ r).const_mul (α j*k j)

theorem pinnedEnergy_smooth (P : τ → PinFrame ι S κ n) (α k : τ → ℝ)
    (σ : S) (r : ℕ) : BddSmooth r (pinnedEnergy P α k σ) :=
  BddSmooth.sum Finset.univ fun j _ => ((P j).energy_smooth σ r).const_mul (α j*(k j)^2)

theorem pinnedObservable_lineDeriv (P : τ → PinFrame ι S κ n) (α k : τ → ℝ)
    (σ : S) (x v : Fin n → ℝ) :
    lineDeriv ℝ (pinnedObservable P α k σ) x v = ∑ j, α j*k j*(P j).cross σ x v := by
  have h := HasDerivAt.sum (u := Finset.univ) fun j _ =>
    (((P j).observable_smooth σ 1).hasDerivAt_line x v 0).const_mul (α j*k j)
  simp only [Finset.sum_fn, zero_smul, add_zero] at h
  simpa only [HasLineDerivAt, pinnedObservable, ← PinFrame.cross_eq_lineDeriv] using
    (show HasLineDerivAt ℝ (pinnedObservable P α k σ)
      (∑ j, α j*k j*lineDeriv ℝ ((P j).observable σ) x v) x v from h).lineDeriv

omit [Fintype κ] in
theorem pinnedPotential_strong (P : τ → PinFrame ι S κ n) {α : τ → ℝ} (hα : ∀ j, 0 ≤ α j)
    (ell : (Fin n → ℝ) →L[ℝ] ℝ) (x v : Fin n → ℝ) :
    ‖v‖^2 ≤ (pinnedPotential_derivatives P α ell).second x v := by
  exact (pi_norm_sq_le_sum_sq v).trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => mul_nonneg (hα j) ((P j).hessian_nonneg x v)))

theorem pinnedPotential_block (P : τ → PinFrame ι S κ n) {α : τ → ℝ} (hα : ∀ j, 0 ≤ α j)
    (k : τ → ℝ) (σ : S) (ell : (Fin n → ℝ) →L[ℝ] ℝ) (x v : Fin n → ℝ) (s : ℝ) :
    0 ≤ (pinnedPotential_derivatives P α ell).second x v -
      2*s*lineDeriv ℝ (pinnedObservable P α k σ) x v + s^2*pinnedEnergy P α k σ x := by
  rw [pinnedObservable_lineDeriv]
  have h : 0 ≤ (∑ i, (v i)^2) + ∑ j, α j *
      ((P j).hessian x v v - 2*(s*k j)*(P j).cross σ x v + (s*k j)^2*(P j).energy σ x) :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hα j) ((P j).block_nonneg σ x v (s*k j)))
  convert h using 1
  change (∑ i, (v i)^2) + (∑ j, α j*(P j).hessian x v v) -
    2*s*(∑ j, α j*k j*(P j).cross σ x v) +
    s^2*(∑ j, α j*(k j)^2*(P j).energy σ x) = _
  simp only [Finset.mul_sum]
  have he : ∀ j, α j * (P j).hessian x v v - 2*s*(α j*k j*(P j).cross σ x v) +
      s^2*(α j*(k j)^2*(P j).energy σ x) = α j *
        ((P j).hessian x v v - 2*(s*k j)*(P j).cross σ x v + (s*k j)^2*(P j).energy σ x) := by
    intro j
    ring
  rw [show (∑ i, (v i)^2) + (∑ j, α j*(P j).hessian x v v) -
      (∑ j, 2*s*(α j*k j*(P j).cross σ x v)) +
      (∑ j, s^2*(α j*(k j)^2*(P j).energy σ x)) =
      (∑ i, (v i)^2) + ∑ j, (α j*(P j).hessian x v v -
        2*s*(α j*k j*(P j).cross σ x v) + s^2*(α j*(k j)^2*(P j).energy σ x)) by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring]
  simp_rw [he]

 

theorem pinned_variance_le (P : τ → PinFrame ι S κ n) {α : τ → ℝ} (hα : ∀ j, 0 ≤ α j)
    (k : τ → ℝ) (σ : S) (ell : (Fin n → ℝ) →L[ℝ] ℝ) :
    variance (pinnedObservable P α k σ) (potentialLaw (pinnedPotential P α ell)) ≤
      ∫ x, pinnedEnergy P α k σ x ∂potentialLaw (pinnedPotential P α ell) := by
  have hU := pinnedPotential_gaussianDominated P α ell
  have : IsProbabilityMeasure (potentialLaw (pinnedPotential P α ell)) := potentialLaw_isProbability hU
  apply variance_le_BddSmooth_block (μ := potentialLaw (pinnedPotential P α ell)) (U := normalizedPotential (pinnedPotential P α ell)) rfl
    (gaussianDominated_normalizedPotential hU) ?_
    ((pinnedPotential_derivatives P α ell).const_add _)
    (pinnedObservable_smooth P α k σ 2) (pinnedEnergy_smooth P α k σ 2)
    (pinnedPotential_strong P hα ell) (pinnedPotential_block P hα k σ ell)
  unfold normalizedPotential pinnedPotential
  apply Continuous.add _ continuous_const
  apply Continuous.add
  · exact (show Continuous (driverQuadratic (n := n)) from by unfold driverQuadratic; fun_prop).sub ell.continuous
  · apply continuous_finsetSum
    intro j _
    obtain ⟨C, hC⟩ := (P j).potential_lipschitz
    exact hC.continuous.const_mul (α j)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

 

def zeroContinuation (ν : Measure E) (F : E → ℝ) (x : E) : ℝ :=
  ∫ z, F (x + z) ∂ν

omit [NormedSpace ℝ E] [IsProbabilityMeasure ν] in
theorem ExponentialIncrement.integrable_norm (hν : ExponentialIncrement ν) :
    Integrable (fun z : E => ‖z‖) ν := by
  apply (hν 1).mono' continuous_norm.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_mul] using
    (Real.add_one_le_exp ‖z‖).trans' (by linarith : ‖z‖ ≤ ‖z‖ + 1)

omit [NormedSpace ℝ E] in
theorem ExponentialIncrement.integrable_lipschitz (hν : ExponentialIncrement ν)
    {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (x : E) :
    Integrable (fun z => F (x + z)) ν := by
  apply ((integrable_const |F x|).add (hν.integrable_norm.const_mul (C:ℝ))).mono'
    (hF.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  filter_upwards [] with z
  change |F (x+z)| ≤ |F x| + C * ‖z‖
  have h := hF.dist_le_mul (x+z) x
  simp only [dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left] at h
  have hh := abs_add_le (F (x+z)-F x) (F x)
  rw [sub_add_cancel] at hh
  linarith

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem shiftedMean_zero (F A : E → ℝ) (x : E) :
    shiftedMean ν 0 F A x = zeroContinuation ν A x := by
  simp [shiftedMean, tiltedMean, zeroContinuation]

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem zeroContinuation_lipschitz {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hi : ∀ x, Integrable (fun z => F (x+z)) ν) :
    LipschitzWith C (zeroContinuation ν F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, zeroContinuation, zeroContinuation, ← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ z, |F (x+z)-F (y+z)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _ : E, (C:ℝ)*dist x y ∂ν := integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
      (Eventually.of_forall fun z => by simpa only [Real.dist_eq, dist_add_right] using hF.dist_le_mul (x+z) (y+z))
    _ = _ := by simp

theorem hasDerivAt_zeroContinuation {F F₁ : E → ℝ} {B : ℝ} {v : E}
    (hF : Continuous F) (hF₁ : Continuous F₁)
    (hd : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s•v)) (F₁ (x+t•v)) t)
    (hb : ∀ x, |F₁ x| ≤ B) (hi : ∀ x, Integrable (fun z => F (x+z)) ν)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => zeroContinuation ν F (x+s•v))
      (zeroContinuation ν F₁ (x+t•v)) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := fun (s : ℝ) (z : E) => F (x+s•v+z))
    (F' := fun (s : ℝ) (z : E) => F₁ (x+s•v+z))
    (s := Set.univ) (bound := fun _ : E => B) (by simp)
    (Eventually.of_forall fun s : ℝ =>
      (show Continuous (fun z : E => F (x+s•v+z)) from hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (hi (x+t•v))
    ((show Continuous (fun z : E => F₁ (x+t•v+z)) from hF₁.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z s _ => by simpa only [Real.norm_eq_abs] using hb (x+s•v+z))
    (integrable_const _)
    (Eventually.of_forall fun z s _ => by
      simpa only [add_assoc, add_comm z] using hd (x+z) s)).2

theorem BddSmooth.zeroContinuation {r : ℕ} {A : E → ℝ} (hA : BddSmooth r A) :
    BddSmooth r (zeroContinuation ν A) := by
  have hF : PotentialRegularity r (fun _ : E => (0 : ℝ)) := by
    refine ⟨⟨0, LipschitzWith.const 0⟩, ?_⟩
    intro v
    exact ⟨fun _ => 0, BddSmooth.const r 0, fun _ t => hasDerivAt_const t 0⟩
  have hi (x : E) : Integrable (fun z : E => Real.exp ((0:ℝ) * (0:ℝ))) ν := by simp
  have h := hA.shiftedMean hF (m := 0) hi
  have heq : Hierarchy.shiftedMean ν 0 (fun _ : E => (0 : ℝ)) A = Hierarchy.zeroContinuation ν A :=
    funext fun x => shiftedMean_zero _ _ x
  rw [heq] at h
  exact h

theorem PotentialRegularity.zeroContinuation {r : ℕ} {F : E → ℝ}
    (hF : PotentialRegularity r F) (hν : ExponentialIncrement ν) :
    PotentialRegularity r (zeroContinuation ν F) := by
  obtain ⟨C, hC⟩ := hF.1
  refine ⟨⟨C, zeroContinuation_lipschitz hC (hν.integrable_lipschitz hC)⟩, ?_⟩
  intro v
  obtain ⟨F₁, hF₁, hd⟩ := hF.2 v
  obtain ⟨B, _, hb⟩ := hF₁.bound
  refine ⟨Hierarchy.zeroContinuation ν F₁, hF₁.zeroContinuation, ?_⟩
  exact hasDerivAt_zeroContinuation hC.continuous hF₁.continuous hd hb
    (hν.integrable_lipschitz hC)

theorem BddSmooth.integrable_zero_shift {r : ℕ} {A : E → ℝ}
    (hA : BddSmooth r A) (x : E) : Integrable (fun z => A (x+z)) ν := by
  obtain ⟨B, _, hb⟩ := hA.bound
  exact (integrable_const B).mono'
    (hA.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun z => hb _)

 

noncomputable def SourceContinuation.root {v : E} {a : ℝ}
    (T : SourceContinuation v a) (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : ExponentialIncrement ν) : SourceContinuation v 0 where
  potential := zeroContinuation ν T.potential
  mean := zeroContinuation ν T.mean
  secondMoment := zeroContinuation ν T.secondMoment
  hessian := zeroContinuation ν T.hessian
  regular r := (T.regular r).zeroContinuation hν
  mean_smooth r := (T.mean_smooth r).zeroContinuation
  second_smooth r := (T.second_smooth r).zeroContinuation
  hessian_smooth r := (T.hessian_smooth r).zeroContinuation
  first := by
    obtain ⟨C, hC⟩ := (T.regular 0).1
    obtain ⟨B, _, hb⟩ := (T.mean_smooth 0).bound
    exact hasDerivAt_zeroContinuation hC.continuous (T.mean_smooth 0).continuous
      T.first hb (hν.integrable_lipschitz hC)
  second := by
    obtain ⟨B, _, hb⟩ := (T.hessian_smooth 0).bound
    exact hasDerivAt_zeroContinuation (T.mean_smooth 0).continuous (T.hessian_smooth 0).continuous
      T.second hb ((T.mean_smooth 0).integrable_zero_shift)
  mass_nonneg := le_rfl
  mass_le_one := by norm_num
  variance_nonneg x := by
    have hmono := shiftedMean_mono ((T.mean_smooth 0).mul (T.mean_smooth 0))
      (T.second_smooth 0) (fun y => by have := T.variance_nonneg y; nlinarith)
      (ν := ν) (F := fun _ => 0) (m := 0) (x := x) (by simp)
    have hj := shiftedMean_square_sub_nonneg (F := fun _ : E => (0:ℝ)) continuous_const
      (T.mean_smooth 0) (ν := ν) (m := 0) (x := x) (by simp)
    simp only [shiftedMean_zero, ← sq] at hmono hj
    linarith
  lower x := by
    simp only [zero_mul, zeroContinuation]
    exact integral_nonneg fun z => (mul_nonneg T.mass_nonneg (T.variance_nonneg (x+z))).trans (T.lower (x+z))
  upper x := by
    have hmono := shiftedMean_mono (T.hessian_smooth 0)
      ((T.second_smooth 0).sub ((T.mean_smooth 0).mul (T.mean_smooth 0)))
      (fun y => by simpa only [← sq] using T.upper y)
      (ν := ν) (F := fun _ => 0) (m := 0) (x := x) (by simp)
    have hj := shiftedMean_square_sub_nonneg (F := fun _ : E => (0:ℝ)) continuous_const
      (T.mean_smooth 0) (ν := ν) (m := 0) (x := x) (by simp)
    rw [shiftedMean_sub (T.second_smooth 0) ((T.mean_smooth 0).mul (T.mean_smooth 0)) (by simp)] at hmono
    simp only [shiftedMean_zero, ← sq] at hmono hj
    linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

 

theorem shiftedContinuation_equiv (T : E ≃L[ℝ] E) {ν : Measure E}
    (hT : MeasurePreserving T ν ν) (m : ℝ) {F : E → ℝ}
    (hF : ∀ x, F (T x) = F x) (x : E) :
    shiftedContinuation ν m F (T x) = shiftedContinuation ν m F x := by
  unfold shiftedContinuation
  have h := hT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => Real.exp (m * F (T x + z)))
  have he : (fun z => Real.exp (m * F (T x + T z))) =
      (fun z => Real.exp (m * F (x+z))) := by
    funext z
    rw [← map_add, hF]
  change (∫ z, Real.exp (m * F (T x + T z)) ∂ν) = _ at h
  rw [he] at h
  rw [h]

theorem shiftedMean_equiv (T : E ≃L[ℝ] E) {ν : Measure E}
    (hT : MeasurePreserving T ν ν) (m : ℝ) {F A B : E → ℝ}
    (hF : ∀ x, F (T x) = F x) (hA : ∀ x, A (T x) = B x) (x : E) :
    shiftedMean ν m F A (T x) = shiftedMean ν m F B x := by
  unfold shiftedMean tiltedMean
  have h₁ := hT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => A (T x+z)*Real.exp (m*F (T x+z)))
  have h₂ := hT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => Real.exp (m*F (T x+z)))
  change (∫ z, A (T x+T z)*Real.exp (m*F (T x+T z)) ∂ν) = _ at h₁
  change (∫ z, Real.exp (m*F (T x+T z)) ∂ν) = _ at h₂
  simp_rw [← map_add T, hF, hA] at h₁ h₂
  rw [← h₁, ← h₂]

variable {S : Type*} [Fintype S]

omit [MeasurableSpace E] [BorelSpace E] in
theorem spinPartition_equiv (T : E ≃L[ℝ] E) (π : S ≃ S)
    {w : S → ℝ} {φ : S → E →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x) (x : E) :
    spinPartition w φ (T x) = spinPartition w φ x := by
  unfold spinPartition
  rw [← Equiv.sum_comp π (fun s => w s * Real.exp (φ s (T x)))]
  simp_rw [hw, hφ]

omit [MeasurableSpace E] [BorelSpace E] in
theorem spinWeight_equiv (T : E ≃L[ℝ] E) (π : S ≃ S)
    {w : S → ℝ} {φ : S → E →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x) (x : E) (s : S) :
    spinWeight w φ (T x) (π s) = spinWeight w φ x s := by
  simp only [spinWeight, hw, hφ, spinPartition_equiv T π hw hφ]

variable {ι : Type*} [Fintype ι]

theorem gaussianHierarchy_equiv (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    (steps : List (GaussianStep ι))
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i)) (Measure.pi fun i => gaussianReal 0 (p.2 i))) :
    ∀ x, gaussianHierarchy w φ steps (T x) = gaussianHierarchy w φ steps x := by
  induction steps with
  | nil =>
    intro x
    simp only [gaussianHierarchy, spinLogPartition, spinPartition_equiv T π hw hφ]
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    have ht := ih (fun p hp => hT p (List.mem_cons_of_mem _ hp))
    intro x
    exact shiftedContinuation_equiv T (hT _ (List.mem_cons_self)) m ht x

theorem gaussianHierarchyMean_equiv (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    (steps : List (GaussianStep ι))
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i)) (Measure.pi fun i => gaussianReal 0 (p.2 i)))
    (A : S → ℝ) (x : ι → ℝ) :
    gaussianHierarchyMean w φ A steps (T x) =
      gaussianHierarchyMean w φ (fun s => A (π s)) steps x := by
  induction steps generalizing x with
  | nil =>
    simp only [gaussianHierarchyMean]
    rw [← Equiv.sum_comp π (fun s => spinWeight w φ (T x) s * A s)]
    simp_rw [spinWeight_equiv T π hw hφ]
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    have ht : ∀ p ∈ tail, MeasurePreserving T
        (Measure.pi fun i => gaussianReal 0 (p.2 i)) (Measure.pi fun i => gaussianReal 0 (p.2 i)) :=
      fun p hp => hT p (List.mem_cons_of_mem _ hp)
    exact shiftedMean_equiv T (hT _ (List.mem_cons_self)) m
      (gaussianHierarchy_equiv T π hw hφ tail ht) (fun y => ih ht y) x

variable [Nonempty S]

theorem gaussianHierarchyHessian_equiv (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} (hwpos : ∀ s, 0 < w s) {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i)) (Measure.pi fun i => gaussianReal 0 (p.2 i)))
    (x v u : ι → ℝ) :
    gaussianHierarchyHessian w φ steps (T x) (T v) (T u) =
      gaussianHierarchyHessian w φ steps x v u := by
  have hm (y : ι → ℝ) :
      gaussianHierarchyMean w φ (fun s => φ s (T v)) steps (T y) =
        gaussianHierarchyMean w φ (fun s => φ s v) steps y := by
    simpa only [hφ] using
      gaussianHierarchyMean_equiv T π hw hφ steps hT (fun s => φ s (T v)) y
  have hf : (fun t : ℝ => gaussianHierarchyMean w φ (fun s => φ s (T v)) steps
      (T x+t•T u)) = (fun t : ℝ => gaussianHierarchyMean w φ (fun s => φ s v) steps (x+t•u)) := by
    funext t
    simpa only [map_add, map_smul] using hm (x+t•u)
  have h₁ := gaussianHierarchyMean_hasDerivAt hwpos φ (fun s => φ s (T v)) steps ha (T x) (T u) 0
  have h₂ := gaussianHierarchyMean_hasDerivAt hwpos φ (fun s => φ s v) steps ha x u 0
  rw [hf] at h₁
  simpa only [zero_smul, add_zero, gaussianHierarchyHessian] using h₁.unique h₂

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 
def signEquiv (c : ι → ℝ) (hc : ∀ i, c i*c i = 1) : (ι → ℝ) ≃L[ℝ] (ι → ℝ) where
  toFun x i := c i*x i
  invFun x i := c i*x i
  left_inv x := by ext i; dsimp; rw [← mul_assoc, hc, one_mul]
  right_inv x := by ext i; dsimp; rw [← mul_assoc, hc, one_mul]
  map_add' x y := by ext i; dsimp; ring
  map_smul' r x := by ext i; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [Fintype ι] in
@[simp] theorem signEquiv_apply (c : ι → ℝ) (hc : ∀ i, c i*c i = 1) (x : ι → ℝ) (i : ι) :
    signEquiv c hc x i = c i*x i := rfl

theorem signEquiv_gaussian (c : ι → ℝ) (hc : ∀ i, c i*c i = 1) (q : ι → ℝ≥0) :
    MeasurePreserving (signEquiv c hc) (Measure.pi fun i => gaussianReal 0 (q i))
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
  apply measurePreserving_pi (fun i => gaussianReal 0 (q i)) (fun i => gaussianReal 0 (q i))
  intro i
  change MeasurePreserving (fun x : ℝ => c i*x) _ _
  rcases mul_self_eq_one_iff.mp (hc i) with hi | hi
  · have he : (fun x : ℝ => c i*x) = id := by funext x; simp [hi]
    rw [he]
    exact MeasurePreserving.id _
  · have he : (fun x : ℝ => c i*x) = Neg.neg := by ext x; simp [hi]
    rw [he]
    refine ⟨measurable_neg, ?_⟩
    simp only [gaussianReal_map_neg, neg_zero]

theorem signEquiv_volume (c : ι → ℝ) (hc : ∀ i, c i*c i = 1) :
    MeasurePreserving (signEquiv c hc) volume volume := by
  apply volume_preserving_pi
  intro i
  change MeasurePreserving (fun x : ℝ => c i*x) _ _
  rcases mul_self_eq_one_iff.mp (hc i) with hi | hi
  · have he : (fun x : ℝ => c i*x) = id := by funext x; simp [hi]
    rw [he]
    exact MeasurePreserving.id _
  · simpa only [hi, neg_one_mul] using Measure.measurePreserving_neg (volume : Measure ℝ)

end SKFluctuations.Hierarchy

end

end OAI
