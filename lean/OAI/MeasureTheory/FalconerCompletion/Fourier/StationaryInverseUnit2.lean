import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.AngularDerivativeEventuallyEq

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Polynomial
open scoped ContDiff

noncomputable def stationaryInverseUnitND (c : ℂ) (hc : c ≠ 0) : (Polynomial ℂ)ˣ :=
  Units.map (Polynomial.C : ℂ →+* Polynomial ℂ).toMonoidHom (Units.mk0 c hc)

lemma stationaryInverseUnitND_val (c : ℂ) (hc : c ≠ 0) :
    (stationaryInverseUnitND c hc : Polynomial ℂ) = C c := rfl

lemma stationaryInverseUnitND_inv (c : ℂ) (hc : c ≠ 0) :
    (↑((stationaryInverseUnitND c hc)⁻¹) : Polynomial ℂ) = C c⁻¹ := rfl

noncomputable def stationaryInversePolynomialND (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (j : ℕ) : Polynomial ℂ :=
  PowerSeries.coeff j (PowerSeries.invOfUnit (PowerSeries.mk L) (stationaryInverseUnitND c hc))

lemma stationaryInversePolynomialND_zero (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) :
    stationaryInversePolynomialND L c hc 0 = C c⁻¹ := by
  simp [stationaryInversePolynomialND,PowerSeries.coeff_zero_eq_constantCoeff_apply,
    stationaryInverseUnitND_inv]

lemma stationaryInversePolynomialND_convolution (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (h₀ : L 0 = C c) (j : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, L p.1 * stationaryInversePolynomialND L c hc p.2 =
      if j=0 then 1 else 0 := by
  have he := PowerSeries.mul_invOfUnit (PowerSeries.mk L) (stationaryInverseUnitND c hc)
    (by simpa [stationaryInverseUnitND_val] using h₀)
  have hh := congrArg (PowerSeries.coeff j) he
  simpa only [PowerSeries.coeff_mul,PowerSeries.coeff_mk,stationaryInversePolynomialND,
    PowerSeries.coeff_one] using hh

lemma stationaryInversePolynomialND_succ (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (h₀ : L 0 = C c) (j : ℕ) :
    stationaryInversePolynomialND L c hc (j+1) =
      -C c⁻¹ * ∑ h ∈ Finset.range (j+1), L (h+1) * stationaryInversePolynomialND L c hc (j-h) := by
  have hh := stationaryInversePolynomialND_convolution L c hc h₀ (j+1)
  rw [Finset.Nat.sum_antidiagonal_succ,ite_eq_right (Nat.succ_ne_zero _),h₀] at hh
  have hz : C c⁻¹ * C c = (1 : Polynomial ℂ) := by rw [← map_mul,inv_mul_cancel₀ hc,map_one]
  have he := congrArg (fun x : Polynomial ℂ => C c⁻¹ * x) hh
  rw [mul_add,← mul_assoc,hz,one_mul,mul_zero] at he
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  linear_combination he

lemma stationaryInversePolynomialND_degree (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (h₀ : L 0 = C c) (hdeg : ∀ j, (L j).natDegree ≤ j) (j : ℕ) :
    (stationaryInversePolynomialND L c hc j).natDegree ≤ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [stationaryInversePolynomialND_zero]
    | succ j =>
      rw [stationaryInversePolynomialND_succ L c hc h₀]
      apply (Polynomial.natDegree_mul_le ..).trans
      simp only [Polynomial.natDegree_neg,Polynomial.natDegree_C,zero_add]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro h hh
      apply (Polynomial.natDegree_mul_le ..).trans
      have hh' := Finset.mem_range.mp hh
      have hB := ih (j-h) (by omega)
      have hL := hdeg (h+1)
      omega

noncomputable def stationaryFactorPolynomialND (shift : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | j+1 => (X+C (shift j))*stationaryFactorPolynomialND shift j

lemma stationaryFactorPolynomialND_degree (shift : ℕ → ℂ) (j : ℕ) :
    (stationaryFactorPolynomialND shift j).natDegree ≤ j := by
  induction j with
  | zero => simp [stationaryFactorPolynomialND]
  | succ j ih =>
    apply (Polynomial.natDegree_mul_le ..).trans
    have h₁ : (X+C (shift j)).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_add_le ..).trans (by simp)
    exact Nat.add_le_add h₁ ih |>.trans (by omega)

lemma stationaryFactorPolynomialND_product (shift : ℕ → ℂ) (j : ℕ) :
    stationaryFactorPolynomialND shift j = ∏ q ∈ Finset.range j, (X+C (shift q)) := by
  induction j with
  | zero => simp [stationaryFactorPolynomialND]
  | succ j ih => rw [stationaryFactorPolynomialND,ih,Finset.prod_range_succ,mul_comm]

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]

noncomputable def smoothFunctionSpaceND (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    Submodule ℂ (V → ℂ) where
  carrier := {b | ContDiff ℝ ∞ b}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : V => (0:ℂ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact contDiff_const.mul hf

abbrev SmoothFunctionND (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  ↥(smoothFunctionSpaceND V)

noncomputable def casimirOperatorND (B : OrthonormalBasis ι ℝ V) : Module.End ℂ (SmoothFunctionND V) where
  toFun b := ⟨sphereCasimirND B b.1,sphereCasimirND_contDiff B b.2⟩
  map_add' b c := Subtype.ext (sphereCasimirND_add B b.2 c.2)
  map_smul' z b := Subtype.ext (sphereCasimirND_const_mul B b.2 z)

noncomputable def differentialPolynomialND (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) :
    Module.End ℂ (SmoothFunctionND V) := aeval (casimirOperatorND B) p

lemma differentialPolynomialND_add (B : OrthonormalBasis ι ℝ V) (p q : Polynomial ℂ) :
    differentialPolynomialND B (p+q) = differentialPolynomialND B p + differentialPolynomialND B q :=
  map_add _ p q

lemma differentialPolynomialND_mul (B : OrthonormalBasis ι ℝ V) (p q : Polynomial ℂ) :
    differentialPolynomialND B (p*q) = differentialPolynomialND B p * differentialPolynomialND B q :=
  map_mul _ p q

lemma differentialPolynomialND_C (B : OrthonormalBasis ι ℝ V) (c : ℂ) :
    differentialPolynomialND B (C c) = c • (1 : Module.End ℂ (SmoothFunctionND V)) := by
  simp [differentialPolynomialND,Algebra.algebraMap_eq_smul_one]

lemma differentialPolynomialND_X (B : OrthonormalBasis ι ℝ V) :
    differentialPolynomialND B X = casimirOperatorND B := by simp [differentialPolynomialND]

lemma differentialPolynomialND_factor (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) (b : SmoothFunctionND V) :
    (differentialPolynomialND B (stationaryFactorPolynomialND shift j) b).1 =
      casimirPolynomialND B shift j b.1 := by
  induction j with
  | zero => simp [stationaryFactorPolynomialND,differentialPolynomialND,casimirPolynomialND]
  | succ j ih =>
    rw [stationaryFactorPolynomialND,differentialPolynomialND_mul,differentialPolynomialND_add,
      differentialPolynomialND_X,differentialPolynomialND_C]
    change sphereCasimirND B (differentialPolynomialND B (stationaryFactorPolynomialND shift j) b).1 +
      shift j • (differentialPolynomialND B (stationaryFactorPolynomialND shift j) b).1 = _
    rw [ih,casimirPolynomialND_factor B shift j b.2]
    rfl

noncomputable def stationaryLPolynomialND (c : ℂ) (shift : ℕ → ℂ) (j : ℕ) : Polynomial ℂ :=
  C (c * ((2*Complex.I)^j * (j.factorial:ℂ))⁻¹) * stationaryFactorPolynomialND shift j

lemma stationaryLPolynomialND_zero (c : ℂ) (shift : ℕ → ℂ) :
    stationaryLPolynomialND c shift 0 = C c := by simp [stationaryLPolynomialND,stationaryFactorPolynomialND]

lemma stationaryLPolynomialND_degree (c : ℂ) (shift : ℕ → ℂ) (j : ℕ) :
    (stationaryLPolynomialND c shift j).natDegree ≤ j := by
  apply (Polynomial.natDegree_mul_le ..).trans
  simpa only [Polynomial.natDegree_C,zero_add] using stationaryFactorPolynomialND_degree shift j

lemma differentialPolynomialND_L (B : OrthonormalBasis ι ℝ V) (c : ℂ) (shift : ℕ → ℂ)
    (j : ℕ) (b : SmoothFunctionND V) :
    (differentialPolynomialND B (stationaryLPolynomialND c shift j) b).1 =
      fun w => c * ((2*Complex.I)^j * (j.factorial:ℂ))⁻¹ * casimirPolynomialND B shift j b.1 w := by
  rw [stationaryLPolynomialND,differentialPolynomialND_mul,differentialPolynomialND_C]
  change _ • (differentialPolynomialND B (stationaryFactorPolynomialND shift j) b).1 = _
  rw [differentialPolynomialND_factor]
  rfl

lemma differentialPolynomialND_inverse_convolution (B : OrthonormalBasis ι ℝ V)
    (L : ℕ → Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) (h₀ : L 0 = C c) (j : ℕ)
    (b : SmoothFunctionND V) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j,
      differentialPolynomialND B (L p.1) (differentialPolynomialND B (stationaryInversePolynomialND L c hc p.2) b) =
      if j=0 then b else 0 := by
  have he := congrArg (fun p => differentialPolynomialND B p b)
    (stationaryInversePolynomialND_convolution L c hc h₀ j)
  by_cases hj : j=0 <;>
    simpa [differentialPolynomialND,map_sum,map_mul,LinearMap.sum_apply,Module.End.mul_apply,hj] using he

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
