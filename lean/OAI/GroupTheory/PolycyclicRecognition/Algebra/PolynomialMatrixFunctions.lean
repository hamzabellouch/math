import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteExponentialLogarithm

namespace OAI

/-! # Polynomial matrix exponentials and logarithms with uniform truncation -/

noncomputable section
namespace PolycyclicRecognition
open scoped BigOperators Matrix.Norms.Operator

theorem multivariatePolynomialFunctions_const {I : Type*} (r : ℝ) :
    (fun _ : I → ℝ => r) ∈ multivariatePolynomialFunctions I :=
  mem_multivariatePolynomialFunctions.mpr ⟨MvPolynomial.C r, fun _ => MvPolynomial.eval_C r⟩

theorem multivariatePolynomialFunctions_mul {I : Type*} {f g : (I → ℝ) → ℝ}
    (hf : f ∈ multivariatePolynomialFunctions I)
    (hg : g ∈ multivariatePolynomialFunctions I) :
    (fun x => f x * g x) ∈ multivariatePolynomialFunctions I := by
  obtain ⟨p, hp⟩ := mem_multivariatePolynomialFunctions.mp hf
  obtain ⟨q, hq⟩ := mem_multivariatePolynomialFunctions.mp hg
  exact mem_multivariatePolynomialFunctions.mpr
    ⟨p * q, fun x => by rw [map_mul, hp, hq]⟩

def HasPolynomialMatrixEntries {I : Type*} {n : ℕ}
    (A : (I → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (fun x => A x i j) ∈ multivariatePolynomialFunctions I

namespace HasPolynomialMatrixEntries
variable {I : Type*} {n : ℕ}
  {A B : (I → ℝ) → Matrix (Fin n) (Fin n) ℝ}

theorem linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ V)
    (f : V →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    HasPolynomialMatrixEntries (fun x => f (b.equivFun.symm x)) := by
  intro i j
  let a : (Fin d → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj j).comp
    ((LinearMap.proj i).comp (f.comp b.equivFun.symm.toLinearMap))
  let h : (Fin d → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.pi (fun _ => a)
  exact coordinatePolynomial_iff_components.mp (IsCoordinatePolynomial.linear h) 0

theorem linear_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ V)
    (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] V) (hA : HasPolynomialMatrixEntries A) :
    IsCoordinatePolynomial (fun x => b.equivFun (f (A x))) := by
  let e : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n × Fin n) → ℝ) :=
    { toFun M p := M p.1 p.2
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have he : Function.Injective e := by
    intro M N h
    ext i j
    exact congrFun h (i, j)
  apply coordinatePolynomial_iff_components.mpr
  intro j
  exact polynomial_of_multivariate_evaluations e he A
    (fun p => hA p.1 p.2)
    ((LinearMap.proj j).comp (b.equivFun.toLinearMap.comp f))

theorem const (C : Matrix (Fin n) (Fin n) ℝ) :
    HasPolynomialMatrixEntries (fun _ : I → ℝ => C) :=
  fun i j => multivariatePolynomialFunctions_const (C i j)

theorem add (hA : HasPolynomialMatrixEntries A) (hB : HasPolynomialMatrixEntries B) :
    HasPolynomialMatrixEntries (fun x => A x + B x) :=
  fun i j => (multivariatePolynomialFunctions I).add_mem (hA i j) (hB i j)

theorem sub (hA : HasPolynomialMatrixEntries A) (hB : HasPolynomialMatrixEntries B) :
    HasPolynomialMatrixEntries (fun x => A x - B x) :=
  fun i j => (multivariatePolynomialFunctions I).sub_mem (hA i j) (hB i j)

theorem smul (r : ℝ) (hA : HasPolynomialMatrixEntries A) :
    HasPolynomialMatrixEntries (fun x => r • A x) :=
  fun i j => (multivariatePolynomialFunctions I).smul_mem r (hA i j)

theorem mul (hA : HasPolynomialMatrixEntries A) (hB : HasPolynomialMatrixEntries B) :
    HasPolynomialMatrixEntries (fun x => A x * B x) := by
  intro i j
  change (fun x => ∑ k, A x i k * B x k j) ∈ _
  convert (Submodule.sum_mem (multivariatePolynomialFunctions I) (t := Finset.univ)
    (fun k _ => multivariatePolynomialFunctions_mul (hA i k) (hB k j))) using 1
  funext x
  simp only [Finset.sum_apply]

theorem pow (hA : HasPolynomialMatrixEntries A) (k : ℕ) :
    HasPolynomialMatrixEntries (fun x => A x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (const (I := I) (1 : Matrix (Fin n) (Fin n) ℝ))
  | succ k ih => simpa only [pow_succ] using ih.mul hA

theorem sum {K : Type*} (s : Finset K)
    (F : K → (I → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ k ∈ s, HasPolynomialMatrixEntries (F k)) :
    HasPolynomialMatrixEntries (fun x => ∑ k ∈ s, F k x) := by
  intro i j
  simp only [Matrix.sum_apply]
  convert (Submodule.sum_mem (multivariatePolynomialFunctions I)
    (fun k hk => hF k hk i j)) using 1
  funext x
  simp only [Finset.sum_apply]

theorem exp_of_pow_eq_zero (hA : HasPolynomialMatrixEntries A) (k : ℕ)
    (hk : ∀ x, A x ^ k = 0) :
    HasPolynomialMatrixEntries (fun x => NormedSpace.exp (A x)) := by
  have hp := sum (Finset.range k)
    (fun j x => ((j.factorial : ℝ)⁻¹) • A x ^ j)
    (fun j _ => (hA.pow j).smul _)
  intro i j
  have heq : (fun x => NormedSpace.exp (A x) i j) =
      (fun x => (∑ l ∈ Finset.range k, ((l.factorial : ℝ)⁻¹) • A x ^ l) i j) := by
    funext x
    exact congrArg (fun C : Matrix (Fin n) (Fin n) ℝ => C i j)
      (exp_eq_finite_sum_of_pow_eq_zero (A x) (hk x))
  rw [heq]
  exact hp i j

theorem finiteLog (hA : HasPolynomialMatrixEntries A) (k : ℕ) :
    HasPolynomialMatrixEntries (fun x => finiteNilpotentLog k (A x)) := by
  have hp := sum (Finset.range k)
    (fun j x => algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) ((PowerSeries.log ℚ).coeff j) * A x ^ j)
    (fun j _ => (const _).mul (hA.pow j))
  simpa only [finiteNilpotentLog, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range] using hp

end HasPolynomialMatrixEntries
end PolycyclicRecognition

end

end OAI
