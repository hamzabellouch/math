import Mathlib.Analysis.Calculus.FDeriv.Prod
import OAI.AlgebraicGeometry.PlaneCurves.SectionDimensions
import OAI.AlgebraicGeometry.PlaneCurves.ThetaEvaluation

namespace OAI

/-!
# Projective cubic maps, separation, local coordinates, and differentials
-/

section

/-!
# The actual projective map defined by three multiplier sections
-/

noncomputable section

namespace Nagata.W07

open Nagata.W08 Nagata.W21

/-- Three actual evaluation coordinates associated to a basis of `D(3,γ)`. -/
def cubicEvaluationVector {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) (z : ℂ) : Fin 3 → ℂ :=
  fun i => (b i).val z

theorem cubic_basis_finrank {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) :
    Module.finrank ℂ (automorphicSections τ 3 γ) = 3 := by
  simpa using Module.finrank_eq_card_basis b

/-- No base point means the actual coordinate vector is nonzero. -/
theorem cubicEvaluationVector_ne_zero {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    cubicEvaluationVector b z ≠ 0 := by
  intro hv
  obtain ⟨f, hf⟩ := cubic_exists_section_eval_one τ γ z (cubic_basis_finrank b) hker
  have heval : sectionEval τ 3 γ z = 0 := by
    apply b.ext
    intro i
    exact congrFun hv i
  have hf0 : f.val z = 0 := congrArg (fun L : automorphicSections τ 3 γ →ₗ[ℂ] ℂ => L f) heval
  exact one_ne_zero (hf.symm.trans hf0)

/-- The actual projective map on the nonzero complex covering space. -/
def cubicCoverMap {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) : Projectivization ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (cubicEvaluationVector b (z : ℂ))
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))

/-- Independent values at two lifts force distinct actual projective images. -/
theorem cubicCoverMap_ne_of_kernel {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z w : ℂˣ)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ 3 γ z w)) = 1) :
    cubicCoverMap b hbase z ≠ cubicCoverMap b hbase w := by
  intro he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  have hev : sectionEval τ 3 γ z = a • sectionEval τ 3 γ w := by
    apply b.ext
    intro i
    exact (congrFun ha i).symm
  obtain ⟨f, hfz, hfw⟩ := cubic_exists_section_separating τ γ z w
    (cubic_basis_finrank b) hker
  have heq := congrArg (fun L : automorphicSections τ 3 γ →ₗ[ℂ] ℂ => L f) hev
  change f.val z = a * f.val w at heq
  rw [hfz, hfw, mul_zero] at heq
  exact one_ne_zero heq

/-- Common automorphy multipliers give invariance under the period generator. -/
theorem cubicCoverMap_period (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) : cubicCoverMap b hbase (τ * z) = cubicCoverMap b hbase z := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨γ * (z : ℂ) ^ (-3 : ℤ), ?_⟩
  funext i
  exact ((b i).property.2.2 (z : ℂ) z.ne_zero).symm

/-- Period invariance holds in both integer directions, without a choice of lift. -/
theorem cubicCoverMap_zpow (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (k : ℤ) :
    cubicCoverMap b hbase (τ ^ k * z) = cubicCoverMap b hbase z := by
  have he : (fun k : ℤ => cubicCoverMap b hbase (τ ^ k * z)) =
      (fun _ : ℤ => cubicCoverMap b hbase z) := by
    apply Nagata.W08.biInfinite_unique (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact cubicCoverMap_period τ b hbase (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k

/-- The map on the actual multiplicative torus quotient. -/
def cubicTorusMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    TorusPoint τ → Projectivization ℂ (Fin 3 → ℂ) :=
  Quotient.lift (cubicCoverMap b hbase) (by
    intro z w h
    obtain ⟨k, rfl⟩ := h
    exact (cubicCoverMap_zpow τ b hbase z k).symm)

@[simp] theorem cubicTorusMap_mk (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) : cubicTorusMap τ b hbase (torusPointMk τ z) = cubicCoverMap b hbase z := rfl

/-- The dimension-two divisor input proves injectivity of the genuine torus map. -/
theorem cubicTorusMap_injective (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (hsep : ∀ z w : ℂˣ, ¬ torusOrbitSetoid τ z w →
      Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ 3 γ z w)) = 1) :
    Function.Injective (cubicTorusMap τ b hbase) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro z w hmap
  apply Quotient.sound
  by_contra hrel
  exact (cubicCoverMap_ne_of_kernel b hbase z w (hsep z w hrel)) hmap

end Nagata.W07

end
end

section

/-!
# Separation by genuine degree-three multiplier sections
-/

noncomputable section

namespace Nagata.W07

open Nagata.W08 Nagata.W21

theorem cubic_eval_kernel_dimension {τ γ z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 2 δ) = 2) :
    Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2 := by
  rw [sectionEval_kernel_finrank hτ hτ0 hz hγ 3]
  exact h2 _ (div_ne_zero hγ (neg_ne_zero.mpr hz))

theorem cubic_firstJet_kernel_dimension {τ γ z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0)
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 1 δ) = 1) :
    Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ hz)) = 1 := by
  rw [sectionFirstJet_kernel_finrank hτ hτ0 hz hγ 3]
  exact h1 _ (div_ne_zero hγ (pow_ne_zero 2 (neg_ne_zero.mpr hz)))

theorem cubic_twoEval_kernel_dimension {τ γ z w : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hzw : ¬ ∃ k : ℤ, w = z * τ ^ k)
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 1 δ) = 1) :
    Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ 3 γ z w)) = 1 := by
  rw [sectionTwoEval_kernel_finrank hτ hτ0 hz hw hγ hzw 3]
  exact h1 _ (div_ne_zero (div_ne_zero hγ (neg_ne_zero.mpr hz)) (neg_ne_zero.mpr hw))

/-- No base points, using actual D3 and D2 section dimensions alone. -/
theorem cubic_no_base_points {τ γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 2 δ) = 2)
    {z : ℂ} (hz : z ≠ 0) :
    ∃ f : automorphicSections τ 3 γ, f.val z = 1 :=
  cubic_exists_section_eval_one τ γ z (cubic_basis_finrank b)
    (cubic_eval_kernel_dimension hτ hτ0 hγ hz h2)

/-- A ratio with actual derivative one, after discharging the double-point divisor kernel. -/
theorem cubic_ratio_deriv_one_from_dimensions {τ γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 1 δ) = 1)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 2 δ) = 2)
    {z : ℂ} (hz : z ≠ 0) :
    ∃ f g : automorphicSections τ 3 γ,
      f.val z = 0 ∧ g.val z = 1 ∧ deriv f.val z = 1 ∧
        deriv (fun w => f.val w / g.val w) z = 1 :=
  cubic_exists_ratio_deriv_one τ γ hz (cubic_basis_finrank b)
    (cubic_eval_kernel_dimension hτ hτ0 hγ hz h2)
    (cubic_firstJet_kernel_dimension hτ hτ0 hγ hz h1)

/-- The genuine projective map, with basepoint exclusion obtained from D2 dimensions. -/
def cubicMapFromDimensions (τ : ℂˣ) (hτ : ‖(τ : ℂ)‖ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections (τ : ℂ) 2 δ) = 2) :
    TorusPoint τ → Projectivization ℂ (Fin 3 → ℂ) :=
  cubicTorusMap τ b (fun _ hz => cubic_eval_kernel_dimension hτ τ.ne_zero hγ hz h2)

theorem cubicMapFromDimensions_injective (τ : ℂˣ) (hτ : ‖(τ : ℂ)‖ < 1)
    {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections (τ : ℂ) 1 δ) = 1)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections (τ : ℂ) 2 δ) = 2) :
    Function.Injective (cubicMapFromDimensions τ hτ hγ b h2) := by
  apply cubicTorusMap_injective
  intro z w hrel
  apply cubic_twoEval_kernel_dimension hτ τ.ne_zero hγ z.ne_zero w.ne_zero _ h1
  rintro ⟨k, hk⟩
  apply hrel
  refine ⟨k, Units.ext ?_⟩
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, mul_comm] using hk.symm

end Nagata.W07

end
end

section

noncomputable section
namespace Nagata.W07
open Nagata.W08

/-- For every nonzero basis denominator, some coordinate ratio has nonzero derivative. -/
theorem cubic_basis_ratio_deriv_ne_zero {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) (hz : z ≠ 0)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ hz)) = 1)
    (j : Fin 3) (hj : (b j).val z ≠ 0) :
    ∃ i : Fin 3, deriv (fun w => (b i).val w / (b j).val w) z ≠ 0 := by
  by_contra! h
  let L : automorphicSections τ 3 γ →ₗ[ℂ] ℂ :=
    (b j).val z • sectionDeriv τ 3 γ hz - deriv (b j).val z • sectionEval τ 3 γ z
  have hL : L = 0 := by
    apply b.ext
    intro i
    have hd := (((b i).property.2.1 z hz).hasDerivAt.fun_div
      ((b j).property.2.1 z hz).hasDerivAt hj).deriv
    rw [h i] at hd
    have hn := (div_eq_zero_iff).mp hd.symm
    have hn' : deriv (b i).val z * (b j).val z - (b i).val z * deriv (b j).val z = 0 :=
      hn.resolve_right (pow_ne_zero 2 hj)
    change (b j).val z * deriv (b i).val z - deriv (b j).val z * (b i).val z = 0
    simpa only [mul_comm] using hn'
  obtain ⟨f, hf⟩ := cubic_firstJet_surjective τ γ hz (cubic_basis_finrank b) hker (0, 1)
  have hf0 : f.val z = 0 := congrArg Prod.fst hf
  have hf1 : deriv f.val z = 1 := congrArg Prod.snd hf
  have he := congrArg (fun A : automorphicSections τ 3 γ →ₗ[ℂ] ℂ => A f) hL
  change (b j).val z * deriv f.val z - deriv (b j).val z * f.val z = 0 at he
  apply hj
  simpa [hf0, hf1] using he

/-- Coordinate ratios are genuine analytic functions wherever the denominator is nonzero. -/
theorem cubic_basis_ratio_analyticAt {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hz : z ≠ 0) (i j : Fin 3) (hj : (b j).val z ≠ 0) :
    AnalyticAt ℂ (fun w => (b i).val w / (b j).val w) z :=
  (automorphicSection_analyticAt (b i) hz).div
    (automorphicSection_analyticAt (b j) hz) hj

/-- Some actual affine coordinate chart has a nonzero coordinate derivative at every lift. -/
theorem cubic_affine_chart_nonzero_derivative {τ γ z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 1 δ) = 1)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 2 δ) = 2)
    (hz : z ≠ 0) :
    ∃ i j : Fin 3, (b j).val z ≠ 0 ∧
      AnalyticAt ℂ (fun w => (b i).val w / (b j).val w) z ∧
      deriv (fun w => (b i).val w / (b j).val w) z ≠ 0 := by
  have hv := cubicEvaluationVector_ne_zero b (cubic_eval_kernel_dimension hτ hτ0 hγ hz h2)
  have hex : ∃ j : Fin 3, (b j).val z ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j, hj⟩ := hex
  obtain ⟨i, hi⟩ := cubic_basis_ratio_deriv_ne_zero b hz
    (cubic_firstJet_kernel_dimension hτ hτ0 hγ hz h1) j hj
  exact ⟨i, j, hj, cubic_basis_ratio_analyticAt b hz i j hj, hi⟩

end Nagata.W07

end
end

section

noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry

theorem cubicCoverMap_chartCoordinates {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) :
    chartCoordinates j (cubicCoverMap b hbase z) =
      fun i : ChartVariables j => (b i.val).val z / (b j).val z := by
  exact chartCoordinates_mk j _ _

theorem cubicCoverMap_chart_nonzero {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) :
    (cubicCoverMap b hbase z).rep j ≠ 0 ↔ (b j).val z ≠ 0 :=
  mk_rep_coordinate_ne_zero_iff _ _ j

/-- The witness lies among the two genuine affine chart variables, not the denominator. -/
theorem cubic_chart_variable_deriv_ne_zero {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) (hz : z ≠ 0)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ hz)) = 1)
    (j : Fin 3) (hj : (b j).val z ≠ 0) :
    ∃ i : ChartVariables j, deriv (fun w => (b i.val).val w / (b j).val w) z ≠ 0 := by
  obtain ⟨i, hi⟩ := cubic_basis_ratio_deriv_ne_zero b hz hker j hj
  have hij : i ≠ j := by
    intro h
    subst i
    apply hi
    have hd := (((b j).property.2.1 z hz).hasDerivAt.fun_div
      ((b j).property.2.1 z hz).hasDerivAt hj).deriv
    simpa only [mul_comm, sub_self, zero_div] using hd
  exact ⟨⟨i, hij⟩, hi⟩

/-- The covering map in a genuine local exponential parameter. -/
def cubicExponentialMap {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (x : ℂ) : PlanePoint :=
  cubicCoverMap b hbase (z * Units.mk0 (Complex.exp x) (Complex.exp_ne_zero x))

theorem cubicExponentialMap_coordinate {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (i : ChartVariables j) (x : ℂ) :
    chartCoordinates j (cubicExponentialMap b hbase z x) i =
      (b i.val).val ((z : ℂ) * Complex.exp x) /
        (b j).val ((z : ℂ) * Complex.exp x) := by
  exact congrFun (cubicCoverMap_chartCoordinates b hbase _ j) i

/-- Actual projective affine coordinates have a nonzero derivative in the torus chart. -/
theorem cubicExponentialMap_coordinate_deriv_ne_zero {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (hj : (b j).val z ≠ 0)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ z.ne_zero)) = 1) :
    ∃ i : ChartVariables j,
      deriv (fun x => chartCoordinates j (cubicExponentialMap b hbase z x) i) 0 ≠ 0 := by
  obtain ⟨i, hi⟩ := cubic_chart_variable_deriv_ne_zero b z.ne_zero hker j hj
  refine ⟨i, ?_⟩
  have hr := (cubic_basis_ratio_analyticAt b z.ne_zero i.val j hj).differentiableAt.hasDerivAt
  have he : HasDerivAt (fun x : ℂ => (z : ℂ) * Complex.exp x) (z : ℂ) 0 := by
    simpa using (Complex.hasDerivAt_exp (0 : ℂ)).const_mul (z : ℂ)
  have hr' : HasDerivAt (fun w => (b i.val).val w / (b j).val w)
      (deriv (fun w => (b i.val).val w / (b j).val w) (z : ℂ))
      ((z : ℂ) * Complex.exp 0) := by simpa using hr
  have hd := hr'.comp 0 he
  simp only [Function.comp_def] at hd
  have hfun : (fun x => chartCoordinates j (cubicExponentialMap b hbase z x) i) =
      (fun x => (b i.val).val ((z : ℂ) * Complex.exp x) /
        (b j).val ((z : ℂ) * Complex.exp x)) :=
    funext (cubicExponentialMap_coordinate b hbase z j i)
  rw [hfun, hd.deriv]
  exact mul_ne_zero hi z.ne_zero

end Nagata.W07

end
end

section

/-! Injective derivative of the genuine projective affine-coordinate map. -/
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry

theorem pi_fderiv_injective_of_coordinate {ι : Type*} [Fintype ι]
    (F : ℂ → ι → ℂ) (x : ℂ)
    (hd : ∀ i, DifferentiableAt ℂ (fun t => F t i) x)
    (hn : ∃ i, deriv (fun t => F t i) x ≠ 0) :
    Function.Injective (fderiv ℂ F x) := by
  obtain ⟨i, hi⟩ := hn
  intro u v h
  rw [show F = (fun t i => F t i) from rfl, fderiv_pi hd] at h
  have hc := congrFun h i
  simp only [ContinuousLinearMap.pi_apply, fderiv_eq_deriv_mul] at hc
  exact mul_left_cancel₀ hi hc

theorem cubicExponentialMap_coordinate_differentiableAt {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (hj : (b j).val z ≠ 0) (i : ChartVariables j) :
    DifferentiableAt ℂ
      (fun x => chartCoordinates j (cubicExponentialMap b hbase z x) i) 0 := by
  have hr := (cubic_basis_ratio_analyticAt b z.ne_zero i.val j hj).differentiableAt
  have hr' : DifferentiableAt ℂ (fun w => (b i.val).val w / (b j).val w)
      ((z : ℂ) * Complex.exp 0) := by simpa using hr
  have he : DifferentiableAt ℂ (fun x : ℂ => (z : ℂ) * Complex.exp x) 0 :=
    (Complex.differentiableAt_exp).const_mul (z : ℂ)
  have hfun : (fun x => chartCoordinates j (cubicExponentialMap b hbase z x) i) =
      (fun x => (b i.val).val ((z : ℂ) * Complex.exp x) /
        (b j).val ((z : ℂ) * Complex.exp x)) :=
    funext (cubicExponentialMap_coordinate b hbase z j i)
  rw [hfun]
  exact hr'.comp 0 he

/-- This is the actual affine-coordinate tangent map, not an assumed immersion predicate. -/
theorem cubicExponentialMap_fderiv_injective {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (hj : (b j).val z ≠ 0)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ z.ne_zero)) = 1) :
    Function.Injective (fderiv ℂ
      (fun x => chartCoordinates j (cubicExponentialMap b hbase z x)) 0) :=
  pi_fderiv_injective_of_coordinate _ 0
    (cubicExponentialMap_coordinate_differentiableAt b hbase z j hj)
    (cubicExponentialMap_coordinate_deriv_ne_zero b hbase z j hj hker)

end Nagata.W07

end
end

section

/-! The tangent statement in the exact Fin 2 charts used by the genuine projective atlas. -/
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry

theorem cubicExponentialMap_chartTwo_differentiableAt {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (hj : (b j).val z ≠ 0) :
    DifferentiableAt ℂ
      (fun x => chartCoordinates₂ j (cubicExponentialMap b hbase z x)) 0 := by
  apply differentiableAt_pi.mpr
  intro i
  exact cubicExponentialMap_coordinate_differentiableAt b hbase z j hj (chartIndexEquiv j i)

theorem cubicExponentialMap_chartTwo_fderiv_injective {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (j : Fin 3) (hj : (b j).val z ≠ 0)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ z.ne_zero)) = 1) :
    Function.Injective (fderiv ℂ
      (fun x => chartCoordinates₂ j (cubicExponentialMap b hbase z x)) 0) := by
  apply pi_fderiv_injective_of_coordinate
  · intro i
    exact cubicExponentialMap_coordinate_differentiableAt b hbase z j hj (chartIndexEquiv j i)
  · obtain ⟨i, hi⟩ := cubicExponentialMap_coordinate_deriv_ne_zero b hbase z j hj hker
    refine ⟨(chartIndexEquiv j).symm i, ?_⟩
    simpa only [chartCoordinates₂, Equiv.apply_symm_apply] using hi

end Nagata.W07

end
end

section

/-!
# Actual cubic map: no dimension or basis assumptions
-/
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21 Nagata.ProjectiveGeometry

/-- The actual nonzero real period as a complex unit. -/
def cubicPeriod {τ : ℝ} (hτ : 0 < τ) : ℂˣ :=
  Units.mk0 (τ : ℂ) (by exact_mod_cast ne_of_gt hτ)

@[simp] theorem cubicPeriod_val {τ : ℝ} (hτ : 0 < τ) :
    ((cubicPeriod hτ : ℂˣ) : ℂ) = (τ : ℂ) := rfl

theorem realPeriod_norm_lt_one {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ‖(τ : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone

/-- Actual positive-degree dimensions, with Laurent injectivity discharged. -/
theorem actualPositiveSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) n γ) = n.toNat :=
  Nagata.Workers.W10.positiveSection_finrank hτ hτone
    (fun n γ => Nagata.W01.laurentCoefficientMap_injective _ n γ) hn hγ

/-- A chosen actual basis of D(3,γ), built from convergent theta sections. -/
def actualCubicBasis {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ) :=
  Nagata.Workers.W10.positiveSectionBasisFin hτ hτone
    (fun n γ => Nagata.W01.laurentCoefficientMap_injective _ n γ)
    (show (0 : ℤ) < 3 by decide) hγ

theorem actualCubic_eval_kernel_dimension {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (sectionEval (τ : ℂ) 3 γ z)) = 2 :=
  cubic_eval_kernel_dimension (realPeriod_norm_lt_one hτ hτone)
    (cubicPeriod hτ).ne_zero hγ hz
    (fun _ hd => actualPositiveSection_finrank hτ hτone (by decide) hd)

theorem actualCubic_firstJet_kernel_dimension {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (sectionFirstJet (τ : ℂ) 3 γ hz)) = 1 :=
  cubic_firstJet_kernel_dimension (realPeriod_norm_lt_one hτ hτone)
    (cubicPeriod hτ).ne_zero hγ hz
    (fun _ hd => actualPositiveSection_finrank hτ hτone (by decide) hd)

/-- The complete actual degree-three section space has no base points. -/
theorem actualCubic_no_base_points {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    ∃ f : automorphicSections (τ : ℂ) 3 γ, f.val z = 1 :=
  cubic_exists_section_eval_one _ _ _
    (actualPositiveSection_finrank hτ hτone (show (0 : ℤ) < 3 by decide) hγ)
    (actualCubic_eval_kernel_dimension hτ hτone hγ hz)

/-- The genuine projective map on the genuine multiplicative torus quotient. -/
def actualCubicMap {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : TorusPoint (cubicPeriod hτ) → PlanePoint :=
  cubicTorusMap (cubicPeriod hτ) (actualCubicBasis hτ hτone hγ)
    (fun _ hz => actualCubic_eval_kernel_dimension hτ hτone hγ hz)

theorem actualCubicMap_injective {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Function.Injective (actualCubicMap hτ hτone hγ) := by
  apply cubicTorusMap_injective
  intro z w hrel
  apply cubic_twoEval_kernel_dimension (realPeriod_norm_lt_one hτ hτone)
    (cubicPeriod hτ).ne_zero hγ z.ne_zero w.ne_zero
  · rintro ⟨k, hk⟩
    apply hrel
    refine ⟨k, Units.ext ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, cubicPeriod_val, mul_comm]
      using hk.symm
  · intro δ hδ
    exact actualPositiveSection_finrank hτ hτone (by decide) hδ

/-- Evaluate the actual cubic map in the genuine exponential parameter around a lift. -/
def actualCubicExponentialMap {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (z : ℂˣ) : ℂ → PlanePoint :=
  cubicExponentialMap (actualCubicBasis hτ hτone hγ)
    (fun _ hz => actualCubic_eval_kernel_dimension hτ hτone hγ hz) z

theorem actualCubicExponentialMap_eq {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (z : ℂˣ) (x : ℂ) :
    actualCubicExponentialMap hτ hτone hγ z x =
      actualCubicMap hτ hτone hγ
        (torusPointMk (cubicPeriod hτ)
          (z * Units.mk0 (Complex.exp x) (Complex.exp_ne_zero x))) := rfl

@[simp] theorem actualCubicExponentialMap_zero {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (z : ℂˣ) :
    actualCubicExponentialMap hτ hτone hγ z 0 =
      actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) z) := by
  rw [actualCubicExponentialMap_eq]
  congr 2
  apply Units.ext
  simp

/-- In every target chart containing the image, the actual two-coordinate map is differentiable. -/
theorem actualCubicMap_chart_differentiableAt {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (z : ℂˣ) (j : Fin 3)
    (hj : (actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) z)).rep j ≠ 0) :
    DifferentiableAt ℂ
      (fun x => chartCoordinates₂ j (actualCubicExponentialMap hτ hτone hγ z x)) 0 := by
  apply cubicExponentialMap_chartTwo_differentiableAt
  exact (cubicCoverMap_chart_nonzero (actualCubicBasis hτ hτone hγ)
      (fun _ hz => actualCubic_eval_kernel_dimension hτ hτone hγ hz) z j).mp hj

/-- The actual complex tangent map is injective in every projective chart containing the point. -/
theorem actualCubicMap_chart_fderiv_injective {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (z : ℂˣ) (j : Fin 3)
    (hj : (actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) z)).rep j ≠ 0) :
    Function.Injective (fderiv ℂ
      (fun x => chartCoordinates₂ j (actualCubicExponentialMap hτ hτone hγ z x)) 0) := by
  apply cubicExponentialMap_chartTwo_fderiv_injective
  · exact (cubicCoverMap_chart_nonzero (actualCubicBasis hτ hτone hγ)
      (fun _ hz => actualCubic_eval_kernel_dimension hτ hτone hγ hz) z j).mp hj
  · exact actualCubic_firstJet_kernel_dimension hτ hτone hγ z.ne_zero

end Nagata.W07

end
end

end OAI
