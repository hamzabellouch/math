import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Basis.Defs
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticTaylor
import OAI.AlgebraicGeometry.PlaneCurves.CoefficientSpaces
import OAI.AlgebraicGeometry.PlaneCurves.Collision
import OAI.AlgebraicGeometry.PlaneCurves.FrechetMultiplicity

namespace OAI

/-!
# Necessary sections, actual expressions, jets, and kernels
-/

section

namespace Nagata.W20
open scoped Topology BigOperators
open Nagata.CoefficientSpaces
noncomputable section

abbrev ActualSection (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (P : ℂ → ℂ) :=
  polynomialSections τ γL γP d (m : ℤ) P

/-- The actual fixed local covering-space expression in logarithmic coordinates. -/
def localScalar {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : ActualSection τ γL γP d m P) (z₀ x y : ℂ) : ℂ :=
  scalarExpression F.val (z₀ * Complex.exp x) (Complex.exp y)

/-- The finite coefficient formula for the b-th transverse derivative at y=0. -/
def actualTransverse {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : ActualSection τ γL γP d m P) (z₀ : ℂ) (b : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range ((d / 3).toNat + 1),
    F.val.coeff j (z₀ * Complex.exp x) * (j : ℂ) ^ b

/-- A bounded polynomial section has exactly the expected finite sum in the
covering frame, including all zero coefficients and the degree-zero block. -/
theorem scalarExpression_eq_sum_range {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z v : ℂ) :
    scalarExpression F.val z v =
      ∑ j ∈ Finset.range ((d / 3).toNat + 1), F.val.coeff j z * v ^ j := by
  unfold scalarExpression
  apply Polynomial.sum_eq_of_subset (p := F.val) (fun (j : ℕ) (f : ℂ → ℂ) => f z * v ^ j)
  · intro j
    simp
  · intro j hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hn
    exact (Polynomial.mem_support_iff.mp hj) (F.property.1 j (Nat.lt_of_not_ge hn))

/-- The logarithmic fiber coordinate yields exponential monomials exactly. -/
theorem localScalar_eq_sum_exp {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z₀ x y : ℂ) :
    localScalar F z₀ x y =
      ∑ j ∈ Finset.range ((d / 3).toNat + 1),
        F.val.coeff j (z₀ * Complex.exp x) * Complex.exp ((j : ℂ) * y) := by
  rw [localScalar, scalarExpression_eq_sum_range]
  simp only [Complex.exp_nat_mul]

/-- This proves that the finite coefficient formula is the actual repeated
y derivative of the genuine local scalar expression. -/
theorem actualTransverse_eq_derivative {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z₀ x : ℂ) (b : ℕ) :
    actualTransverse F z₀ b x = iteratedDeriv b (fun y => localScalar F z₀ x y) 0 := by
  have hfun : (fun y => localScalar F z₀ x y) =
      fun y => ∑ j ∈ Finset.range ((d / 3).toNat + 1),
        F.val.coeff j (z₀ * Complex.exp x) * Complex.exp ((j : ℂ) * y) :=
    funext (fun y => localScalar_eq_sum_exp F z₀ x y)
  rw [hfun]
  have hcd : ∀ j ∈ Finset.range ((d / 3).toNat + 1),
      ContDiffAt ℂ b (fun y => F.val.coeff j (z₀ * Complex.exp x) *
        Complex.exp ((j : ℂ) * y)) 0 := by
    intro j _
    fun_prop
  rw [iteratedDeriv_fun_sum hcd]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul,
    mul_zero, Complex.exp_zero, mul_one, actualTransverse]

/-- Each coefficient is holomorphic after the actual common logarithmic
coordinate change; z₀≠0 guarantees the chart remains in the punctured plane. -/
theorem logarithmicCoefficient_differentiable {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P)
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (j : ℕ) :
    Differentiable ℂ (fun x => F.val.coeff j (z₀ * Complex.exp x)) := by
  intro x
  apply (coefficientSpace_differentiableAt hP (F.property.2 j)
    (mul_ne_zero hz₀ (Complex.exp_ne_zero x))).comp x
  exact Complex.differentiableAt_exp.const_mul z₀

/-- The transverse expressions needed in collision are genuine entire
holomorphic functions, proved from the actual coefficient-space definition. -/
theorem actualTransverse_differentiable {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P)
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (b : ℕ) :
    Differentiable ℂ (actualTransverse F z₀ b) := by
  apply Differentiable.fun_sum
  intro j _
  exact (logarithmicCoefficient_differentiable F hP hz₀ j).mul_const ((j : ℂ) ^ b)

@[simp] theorem actualTransverse_add {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F G : ActualSection τ γL γP d m P) (z₀ x : ℂ) (b : ℕ) :
    actualTransverse (F + G) z₀ b x =
      actualTransverse F z₀ b x + actualTransverse G z₀ b x := by
  simp only [actualTransverse, Submodule.coe_add, Polynomial.coeff_add,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] theorem actualTransverse_smul {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (a z₀ x : ℂ) (b : ℕ) :
    actualTransverse (a • F) z₀ b x = a * actualTransverse F z₀ b x := by
  simp only [actualTransverse, Submodule.coe_smul, Polynomial.coeff_smul,
    Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A transverse expression is a linear function of the actual polynomial
section, before any choice of basis. -/
def actualTransverseLinear {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (z₀ : ℂ) (b : ℕ) : ActualSection τ γL γP d m P →ₗ[ℂ] (ℂ → ℂ) where
  toFun F := actualTransverse F z₀ b
  map_add' F G := funext (fun x => actualTransverse_add F G z₀ x b)
  map_smul' a F := funext (fun x => actualTransverse_smul F a z₀ x b)

end
end Nagata.W20

end

section

namespace Nagata.W20
open scoped Topology BigOperators
open Nagata.CoefficientSpaces
noncomputable section

/-- The actual manuscript jet map on the concrete polynomial section space.
Its linearity follows from proved holomorphicity and differentiation rules. -/
def actualJetMap {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (q : ℕ) :
    ActualSection τ γL γP d m P →ₗ[ℂ] (Nagata.Workers.W30.JetIndex q m → ℂ) where
  toFun F row := iteratedDeriv row.2.val (actualTransverse F z₀ row.1.val) 0
  map_add' F G := by
    funext row
    have hfun : actualTransverse (F + G) z₀ row.1.val =
        actualTransverse F z₀ row.1.val + actualTransverse G z₀ row.1.val :=
      funext (fun x => actualTransverse_add F G z₀ x row.1.val)
    rw [hfun, iteratedDeriv_add
      ((actualTransverse_differentiable F hP hz₀ row.1.val).analyticAt 0).contDiffAt
      ((actualTransverse_differentiable G hP hz₀ row.1.val).analyticAt 0).contDiffAt]
    rfl
  map_smul' a F := by
    funext row
    have hfun : actualTransverse (a • F) z₀ row.1.val =
        fun x => a * actualTransverse F z₀ row.1.val x :=
      funext (fun x => actualTransverse_smul F a z₀ x row.1.val)
    rw [hfun, iteratedDeriv_const_mul_field]
    rfl

/-- The constructed linear map is exactly the mixed partial derivative
operator in the fixed local frame, not merely a matrix given a matching name. -/
theorem actualJetMap_apply_eq_mixed_derivative {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {q : ℕ}
    (F : ActualSection τ γL γP d m P) (row : Nagata.Workers.W30.JetIndex q m) :
    actualJetMap hP hz₀ q F row =
      iteratedDeriv row.2.val (fun x =>
        iteratedDeriv row.1.val (fun y => localScalar F z₀ x y) 0) 0 := by
  change iteratedDeriv row.2.val (actualTransverse F z₀ row.1.val) 0 = _
  apply congrArg (fun f : ℂ → ℂ => iteratedDeriv row.2.val f 0)
  exact funext (fun x => actualTransverse_eq_derivative F z₀ x row.1.val)

end
end Nagata.W20

end

section

/-! The collision jet map on a genuine finite coefficient space. Matrix
entries are actual complex derivatives of fixed local basis expressions.
No injectivity, existence of geometric sections, or collision conclusion is
included in the definitions. Instantiation with the Wτ basis is separate. -/

namespace Nagata.W20

open Filter Metric
open scoped Topology BigOperators

noncomputable section

/-- The local scalar expression of the b-th transverse derivative, written
in a fixed finite family of actual holomorphic functions. -/
def transverseExpression {ι : Type*} [Fintype ι] {m : ℕ}
    (basis : ι → Fin m → ℂ → ℂ) (c : ι → ℂ) (b : Fin m) (z : ℂ) : ℂ :=
  ∑ i, c i * basis i b z

@[simp] theorem transverseExpression_smul {ι : Type*} [Fintype ι] {m : ℕ}
    (basis : ι → Fin m → ℂ → ℂ) (c : ι → ℂ) (a : ℂ) (b : Fin m) (z : ℂ) :
    transverseExpression basis (a • c) b z = a * transverseExpression basis c b z := by
  simp only [transverseExpression, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Finite linear combinations retain holomorphicity of the local basis. -/
theorem transverseExpression_differentiableOn {ι : Type*} [Fintype ι]
    {m : ℕ} {U : Set ℂ} (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ι → ℂ) (b : Fin m) :
    DifferentiableOn ℂ (transverseExpression basis c b) U := by
  apply DifferentiableOn.fun_sum
  intro i _
  exact (hbasis i b).const_mul (c i)

/-- The manuscript's actual finite row shape, with entries obtained by
complex differentiation of the local basis functions. -/
def coefficientJetMap {ι : Type*} [Fintype ι] (q m : ℕ)
    (basis : ι → Fin m → ℂ → ℂ) :
    (ι → ℂ) →ₗ[ℂ] (Nagata.Workers.W30.JetIndex q m → ℂ) where
  toFun c row := ∑ i, c i * iteratedDeriv row.2.val (basis i row.1) 0
  map_add' c d := by
    funext row
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

/-- The derivative-entry matrix agrees with differentiating the synthesized
local scalar expression. This is an actual bridge, not the definition of
geometric multiplicity. -/
theorem coefficientJetMap_apply_eq_derivative {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ι → ℂ) (row : Nagata.Workers.W30.JetIndex q m) :
    coefficientJetMap q m basis c row =
      iteratedDeriv row.2.val (transverseExpression basis c row.1) 0 := by
  classical
  change (∑ i, c i * iteratedDeriv row.2.val (basis i row.1) 0) = _
  symm
  unfold transverseExpression
  have hcd : ∀ i ∈ (Finset.univ : Finset ι),
      ContDiffAt ℂ row.2.val (fun z => c i * basis i row.1 z) 0 := by
    intro i _
    have ha : AnalyticAt ℂ (fun z => c i * basis i row.1 z) 0 :=
      analyticAt_const.mul ((hbasis i row.1).analyticAt (hU.mem_nhds h0))
    exact ha.contDiffAt
  rw [iteratedDeriv_fun_sum hcd]
  simp only [iteratedDeriv_const_mul_field]

/-- One normalized subsequence works for every transverse order b and every
jet row simultaneously. The conclusion is a genuine nonzero vector in the
kernel of the actual derivative matrix, with no factorization assumption. -/
theorem nonzero_collision_jet_kernel {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ℕ → ι → ℂ) (hcnorm : ∀ n, ‖c n‖ = 1)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i)) :
    ∃ c₀ : ι → ℂ, ‖c₀‖ = 1 ∧ c₀ ≠ 0 ∧ coefficientJetMap q m basis c₀ = 0 := by
  classical
  obtain ⟨c₀, hc₀norm, hc₀ne, φ, hφ, hcφ⟩ := unit_subsequence c hcnorm
  have hcoord : ∀ i, Tendsto (fun n => c (φ n) i) atTop (𝓝 (c₀ i)) := by
    intro i
    exact ((continuous_apply i).tendsto c₀).comp hcφ
  have hroot : ∀ i, Tendsto (fun n => ξ (φ n) i) atTop (𝓝 0) :=
    fun i => (hξlim i).comp hφ.tendsto_atTop
  refine ⟨c₀, hc₀norm, hc₀ne, ?_⟩
  funext row
  rw [coefficientJetMap_apply_eq_derivative hU h0 basis hbasis]
  have hhol : ∀ n, DifferentiableOn ℂ
      (transverseExpression basis (c (φ n)) row.1) U := by
    intro n
    apply DifferentiableOn.fun_sum
    intro i _
    exact (hbasis i row.1).const_mul (c (φ n) i)
  have hconv := locally_uniform_linear_combination hU (fun i => basis i row.1)
    (fun i => (hbasis i row.1).continuousOn) (fun n => c (φ n)) c₀ hcoord
  exact holomorphic_collision_jets hU h0 (fun n => ξ (φ n)) (m - row.1.val)
    (fun n => transverseExpression basis (c (φ n)) row.1)
    (transverseExpression basis c₀ row.1) hroot (fun n => hξinj (φ n))
    (fun n => hξmem (φ n)) hhol hconv (fun n => horder (φ n) row.1)
    row.2.val row.2.isLt

/-- Nonzero input coefficient vectors can be normalized without weakening
any analytic-order lower bound. Thus the normalization hypothesis in the
compactness lemma is discharged for actual nonzero vectors. -/
theorem nonzero_collision_jet_kernel_of_nonzero {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ℕ → ι → ℂ) (hc : ∀ n, c n ≠ 0)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i)) :
    ∃ c₀ : ι → ℂ, ‖c₀‖ = 1 ∧ c₀ ≠ 0 ∧ coefficientJetMap q m basis c₀ = 0 := by
  let normalized : ℕ → ι → ℂ := fun n => (‖c n‖⁻¹ : ℂ) • c n
  have hnorm : ∀ n, ‖normalized n‖ = 1 :=
    fun n => norm_smul_inv_norm (𝕜 := ℂ) (hc n)
  apply nonzero_collision_jet_kernel hU h0 basis hbasis normalized hnorm ξ
    hξlim hξinj hξmem
  intro n b i
  have ha := (transverseExpression_differentiableOn basis hbasis (c n) b).analyticAt
    (hU.mem_nhds (hξmem n i))
  have hfun : transverseExpression basis (normalized n) b =
      (fun _ => (‖c n‖⁻¹ : ℂ)) * transverseExpression basis (c n) b := by
    funext z
    exact transverseExpression_smul basis (c n) (‖c n‖⁻¹ : ℂ) b z
  rw [hfun, analyticOrderAt_mul analyticAt_const ha]
  exact (horder n b i).trans (le_add_of_nonneg_left zero_le)

end
end Nagata.W20

end

section

namespace Nagata.W20

open scoped Topology BigOperators
open Filter Module

noncomputable section

/-- Basis coordinates reconstruct the actual transverse expression. -/
theorem actualTransverse_basis_repr {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ActualSection τ γL γP d m P) (z₀ : ℂ) (b : Fin m) (x : ℂ) :
    transverseExpression (fun i b => actualTransverse (B i) z₀ b.val)
      (fun i => B.repr F i) b x = actualTransverse F z₀ b.val x := by
  have h := congrArg (fun G => actualTransverseLinear z₀ b.val G x) (B.sum_repr F)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    transverseExpression, actualTransverseLinear, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem actual_nonzero_collision_kernel {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (actualTransverse (F n) z₀ b.val) (ξ n i)) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  classical
  let c : ℕ → ι → ℂ := fun n i => B.repr (F n) i
  have hc : ∀ n, c n ≠ 0 := by
    intro n hn
    apply hF n
    apply B.repr.injective
    have hz : B.repr (F n) = 0 := Finsupp.ext (fun i => congrFun hn i)
    simpa only [map_zero] using hz
  let basis : ι → Fin m → ℂ → ℂ := fun i b => actualTransverse (B i) z₀ b.val
  have hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U :=
    fun i b => (actualTransverse_differentiable (B i) hP hz₀ b.val).differentiableOn
  have hord : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i) := by
    intro n b i
    have heq : transverseExpression basis (c n) b = actualTransverse (F n) z₀ b.val :=
      funext (fun x => actualTransverse_basis_repr B (F n) z₀ b x)
    rw [heq]
    exact horder n b i
  obtain ⟨c₀, _, hc₀, hker⟩ := nonzero_collision_jet_kernel_of_nonzero hU h0 basis
    hbasis c hc ξ hξlim hξinj hξmem hord
  let F₀ : ActualSection τ γL γP d m P := ∑ i, c₀ i • B i
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hc₀
    funext i
    have hi := congrArg (fun G => B.repr G i) hz
    simpa [F₀, map_sum, map_smul, Finsupp.single_apply] using hi
  refine ⟨F₀, hF₀, ?_⟩
  have hjet : actualJetMap hP hz₀ q F₀ = coefficientJetMap q m basis c₀ := by
    ext row
    change actualJetMap hP hz₀ q (∑ i, c₀ i • B i) row = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  exact hjet.trans hker

/-- Concrete local power-series multiplicity implies a nonzero element of the
actual Wτ jet kernel. The input is vanishing of genuine convergent Taylor
coefficients, not vanishing of the desired output jets. -/
theorem actual_kernel_from_local_powerSeries {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (S : ℕ → Fin q → FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : ∀ n i, HasFPowerSeriesAt (fun p : ℂ × ℂ => localScalar (F n) z₀ p.1 p.2)
      (S n i) (ξ n i, 0))
    (hzero : ∀ n i j, j < m → S n i j = 0) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  apply actual_nonzero_collision_kernel hP hz₀ B F hF hU h0 ξ hξlim hξinj hξmem
  intro n b i
  have heq : actualTransverse (F n) z₀ b.val =
      fun x => iteratedDeriv b.val (fun y => localScalar (F n) z₀ x y) 0 :=
    funext (fun x => actualTransverse_eq_derivative (F n) z₀ x b.val)
  rw [heq]
  exact Nagata.W19.transverse_iteratedDeriv_order_of_powerSeries
    (ξ n i) (hS n i) m b.val (hzero n i)

end
end Nagata.W20

end

section

/-! Fixed-parameter necessary-section endpoint. Universal existence for distinct
configurations in one actual open neighborhood supplies the moving centers and
nonzero sections internally. No sequence of sections or simultaneous choice over
parameters is assumed. A finite basis is an explicit hypothesis. -/

namespace Nagata.W20
open scoped Topology
open Filter Module

/-- Universal necessary-W existence with genuine local Taylor multiplicity
forces a nonzero vector in the actual section jet kernel, at one fixed τ. -/
theorem actual_kernel_of_every_configuration {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hEvery : ∀ p : Fin q → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
      ∃ F : ActualSection τ γL γP d m P, F ≠ 0 ∧
        ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
          (fun x : ℂ × ℂ => localScalar F z₀ x.1 x.2) (p i, 0) m) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  obtain ⟨ξ, hξinj, hξmem, hξlim⟩ := exists_collision_centers hU h0 q
  have he : ∀ n, ∃ F : ActualSection τ γL γP d m P, F ≠ 0 ∧
      ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => localScalar F z₀ x.1 x.2) (ξ n i, 0) m :=
    fun n => hEvery (ξ n) (hξinj n) (hξmem n)
  choose F hF hTaylor using he
  choose S hS hzero using hTaylor
  exact actual_kernel_from_local_powerSeries hP hz₀ B F hF hU h0 ξ
    hξlim hξinj hξmem S hS hzero

/-- In particular, an injective actual jet map excludes the universal
necessary-W property. This formulation needs no choice across degeneration
parameters: every parameter is fixed before applying the theorem. -/
theorem not_every_configuration_of_injective_actualJetMap {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hJ : Function.Injective (actualJetMap (τ := τ) (γL := γL) (γP := γP)
      (d := d) (m := m) hP hz₀ q)) :
    ¬ (∀ p : Fin q → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
      ∃ F : ActualSection τ γL γP d m P, F ≠ 0 ∧
        ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
          (fun x : ℂ × ℂ => localScalar F z₀ x.1 x.2) (p i, 0) m) := by
  intro hEvery
  obtain ⟨F, hF, hker⟩ := actual_kernel_of_every_configuration hP hz₀ B hU h0 hEvery
  exact hF (hJ (hker.trans (map_zero (actualJetMap hP hz₀ q)).symm))

end Nagata.W20

end

section

/-! Ordinary polynomial ideal multiplicity in genuine analytic coordinates
implies the actual section collision kernel. The local representation of the
section by that polynomial is an explicit germ equality, rather than a jet condition. -/

namespace Nagata.W20
open scoped Topology
open Filter Module

/-- Local analytic polynomial representatives turn ordinary maximal-ideal-power
multiplicity into the Taylor hypotheses of the actual section kernel theorem. -/
theorem actual_kernel_from_local_polynomial_multiplicity {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (A : ℕ → Fin q → MvPolynomial (Fin 2) ℂ)
    (κ : ℕ → Fin q → (ℂ × ℂ) → (ℂ × ℂ))
    (hκ : ∀ n i, AnalyticAt ℂ (κ n i) (ξ n i, 0))
    (hmult : ∀ n i, Nagata.AffineMultiplicity.orderAtLeast
      (fun j : Fin 2 => if j = 0 then (κ n i (ξ n i, 0)).1
        else (κ n i (ξ n i, 0)).2) m (A n i))
    (hrep : ∀ n i,
      (fun p : ℂ × ℂ => MvPolynomial.eval
        (fun j : Fin 2 => if j = 0 then (κ n i p).1 else (κ n i p).2) (A n i))
        =ᶠ[𝓝 (ξ n i, 0)] (fun p => localScalar (F n) z₀ p.1 p.2)) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  have hs : ∀ n i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun p : ℂ × ℂ => localScalar (F n) z₀ p.1 p.2) (ξ n i, 0) m := by
    intro n i
    have hp := Nagata.Workers.W28.polynomial_order_implies_analytic_order
      (A n i) (κ n i (ξ n i, 0)) m (hmult n i)
    exact (hp.comp (hκ n i)).congr (hrep n i)
  choose S hS hzero using hs
  exact actual_kernel_from_local_powerSeries hP hz₀ B F hF hU h0 ξ
    hξlim hξinj hξmem S hS hzero

/-- The same genuine polynomial multiplicity bridge allows an analytic local
frame factor, including all holomorphic units used by the manuscript. -/
theorem actual_kernel_from_local_polynomial_with_frame {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (A : ℕ → Fin q → MvPolynomial (Fin 2) ℂ)
    (κ : ℕ → Fin q → (ℂ × ℂ) → (ℂ × ℂ))
    (hκ : ∀ n i, AnalyticAt ℂ (κ n i) (ξ n i, 0))
    (hmult : ∀ n i, Nagata.AffineMultiplicity.orderAtLeast
      (fun j : Fin 2 => if j = 0 then (κ n i (ξ n i, 0)).1
        else (κ n i (ξ n i, 0)).2) m (A n i))
    (u : ℕ → Fin q → (ℂ × ℂ) → ℂ)
    (hu : ∀ n i, AnalyticAt ℂ (u n i) (ξ n i, 0))
    (hrep : ∀ n i,
      (fun p : ℂ × ℂ => u n i p * MvPolynomial.eval
        (fun j : Fin 2 => if j = 0 then (κ n i p).1 else (κ n i p).2) (A n i))
        =ᶠ[𝓝 (ξ n i, 0)] (fun p => localScalar (F n) z₀ p.1 p.2)) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  have hs : ∀ n i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun p : ℂ × ℂ => localScalar (F n) z₀ p.1 p.2) (ξ n i, 0) m := by
    intro n i
    have hp := Nagata.Workers.W28.polynomial_order_implies_analytic_order
      (A n i) (κ n i (ξ n i, 0)) m (hmult n i)
    exact (Nagata.VariableUnitOrder.analytic_order_mul_left
      (hu n i) (hp.comp (hκ n i))).congr (hrep n i)
  choose S hS hzero using hs
  exact actual_kernel_from_local_powerSeries hP hz₀ B F hF hU h0 ξ
    hξlim hξinj hξmem S hS hzero

end Nagata.W20

end

end OAI
