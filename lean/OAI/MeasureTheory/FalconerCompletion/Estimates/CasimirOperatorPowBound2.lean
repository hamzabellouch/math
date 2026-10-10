import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirOperatorPowBound
import OAI.MeasureTheory.FalconerCompletion.Fourier.StationaryInverseUnit3
import OAI.MeasureTheory.FalconerCompletion.Sphere.AngularDerivativeBound3

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Polynomial
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

theorem casimirOperatorND_pow_bound (B : OrthonormalBasis ι ℝ V) (k m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ) (s : ℕ), 1 ≤ A →
      (∀ j ≤ m+2*k, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (((casimirOperatorND B)^k) b).1 w‖ ≤ D*A^(j+(s+2*k)) := by
  induction k generalizing m with
  | zero =>
    refine ⟨C,hC,?_⟩
    intro b A s hA hderiv
    simpa using hderiv
  | succ k ih =>
    obtain ⟨D,hD,hDb⟩ := ih (m+2)
    obtain ⟨F,hF,hFb⟩ := sphereCasimirND_bound B m D hD
    refine ⟨F,hF,?_⟩
    intro b A s hA hderiv
    have hb : ContDiff ℝ ∞ (((casimirOperatorND B)^k) b).1 := (((casimirOperatorND B)^k) b).2
    have hh := hFb (((casimirOperatorND B)^k) b).1 A (s+2*k) hb hA
      (hDb b A s hA (fun j hj w hw => hderiv j (by omega) w hw))
    rw [pow_succ',Module.End.mul_apply]
    change ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j
      (sphereCasimirND B (((casimirOperatorND B)^k) b).1) w‖ ≤ _
    simpa only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using hh

omit [FiniteDimensional ℝ V] in
lemma differentialPolynomialND_sum (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (b : SmoothFunctionND V) :
    (differentialPolynomialND B p b).1 = fun w =>
      ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * (((casimirOperatorND B)^i) b).1 w := by
  unfold differentialPolynomialND
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Submodule.coe_sum,Submodule.coe_smul]
  funext w
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem differentialPolynomialND_bound (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (k : ℕ) (hpk : p.natDegree ≤ k) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ) (s : ℕ), 1 ≤ A →
      (∀ j ≤ m+2*k, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (differentialPolynomialND B p b).1 w‖ ≤ D*A^(j+(s+2*k)) := by
  have hd (i : ℕ) := casimirOperatorND_pow_bound B i m C hC
  choose D hD hDb using hd
  refine ⟨∑ i ∈ Finset.range (p.natDegree+1), ‖p.coeff i‖*D i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hD i)),?_⟩
  intro b A s hA hderiv
  rw [differentialPolynomialND_sum]
  apply sphere_derivative_sum_bound _ _
    (fun i _ => contDiff_const.mul ((((casimirOperatorND B)^i) b).2)) _
    (fun i _ => mul_nonneg (norm_nonneg _) (hD i)) A (by linarith) (s+2*k) m
  intro i hi
  have hik : i ≤ k := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hpk
  have hh := hDb i b A s hA (fun j hj w hw => hderiv j (by omega) w hw)
  apply sphere_derivative_const_mul_bound _ ((((casimirOperatorND B)^i) b).2)
  intro j hj w hw
  exact (hh j hj w hw).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hA (by omega)) (hD i))

omit [FiniteDimensional ℝ V] in
lemma casimirOperatorND_pow_support (B : OrthonormalBasis ι ℝ V) (k : ℕ) (b : SmoothFunctionND V) :
    tsupport (((casimirOperatorND B)^k) b).1 ⊆ tsupport b.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply]
    exact (tsupport_sphereCasimirND_subset B _).trans ih

omit [FiniteDimensional ℝ V] in
lemma differentialPolynomialND_support (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (b : SmoothFunctionND V) : tsupport (differentialPolynomialND B p b).1 ⊆ tsupport b.1 := by
  rw [differentialPolynomialND_sum]
  apply closure_minimal _ (isClosed_tsupport b.1)
  intro w hw
  by_contra hn
  have hzero (i : ℕ) : (((casimirOperatorND B)^i) b).1 w = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hn (casimirOperatorND_pow_support B i b h))
  exact hw (by simp [hzero])

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
