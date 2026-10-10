import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialIntegerGrid
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

namespace OAI

/-! # Polynomiality of the coordinate operations in a finite Lie word -/

noncomputable section
namespace PolycyclicRecognition
namespace IsCoordinatePolynomial
variable {I J S : Type*}

theorem const (v : J → ℝ) : IsCoordinatePolynomial (fun _ : I → ℝ => v) := by
  exact ⟨fun j => MvPolynomial.C (v j), fun _ _ => MvPolynomial.eval_C _⟩

theorem add {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨fun j => p j + q j, ?_⟩
  intro x j
  simp only [map_add, hp, hq, Pi.add_apply]

theorem smul (r : ℝ) {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (fun x => r • f x) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun j => MvPolynomial.C r * p j, ?_⟩
  intro x j
  simp only [map_mul, MvPolynomial.eval_C, hp, Pi.smul_apply, smul_eq_mul]

theorem coordinate_smul (i : I) (v : J → ℝ) :
    IsCoordinatePolynomial (fun x : I → ℝ => x i • v) := by
  refine ⟨fun j => MvPolynomial.X i * MvPolynomial.C (v j), ?_⟩
  intro x j
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Pi.smul_apply, smul_eq_mul]

theorem neg {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (fun x => -f x) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem iterate {f : (I → ℝ) → (I → ℝ)} (hf : IsCoordinatePolynomial f) (n : ℕ) :
    IsCoordinatePolynomial (f^[n]) := by
  induction n with
  | zero => exact reindex id
  | succ n ih =>
    have heq : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    rw [heq]
    exact hf.comp ih

theorem iterate_zero_of_integer_grid {f : (I → ℝ) → (I → ℝ)}
    (hf : IsCoordinatePolynomial f) (n : ℕ)
    (hn : ∀ z : I → ℤ, f^[n] (fun i => (z i : ℝ)) = 0) : ∀ x, f^[n] x = 0 := by
  have hzero : IsCoordinatePolynomial (fun _ : I → ℝ => (0 : I → ℝ)) := const 0
  exact congrFun ((hf.iterate n).ext_integer_grid hzero hn)

theorem sum (s : Finset S) (f : S → (I → ℝ) → (J → ℝ))
    (hf : ∀ i ∈ s, IsCoordinatePolynomial (f i)) :
    IsCoordinatePolynomial (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (const (I := I) (0 : J → ℝ))
  | @insert a s ha ih =>
    have hpoly := (hf a (Finset.mem_insert_self ..)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using hpoly

theorem linear {d e : ℕ} (A : (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ)) :
    IsCoordinatePolynomial A := by
  let b := Pi.basisFun ℝ (Fin d)
  refine ⟨fun j => ∑ i, MvPolynomial.C (A (b i) j) * MvPolynomial.X i, ?_⟩
  intro x j
  calc
    _ = ∑ i, A (b i) j * x i := by simp
    _ = A (∑ i, x i • b i) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = A x j := by rw [show ∑ i, x i • b i = x from b.sum_equivFun x]

theorem bilinear {d e k : ℕ}
    (B : (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    {f : (I → ℝ) → (Fin d → ℝ)} {g : (I → ℝ) → (Fin e → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => B (f x) (g x)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  let b := Pi.basisFun ℝ (Fin d)
  let c := Pi.basisFun ℝ (Fin e)
  refine ⟨fun l => ∑ i, ∑ j,
    MvPolynomial.C (B (b i) (c j) l) * p i * q j, ?_⟩
  intro x l
  have hx : ∑ i, f x i • b i = f x := b.sum_equivFun _
  have hy : ∑ j, g x j • c j = g x := c.sum_equivFun _
  calc
    _ = ∑ i, ∑ j, B (b i) (c j) l * f x i * g x j := by
      simp only [map_sum, map_mul, MvPolynomial.eval_C, hp, hq]
    _ = B (∑ i, f x i • b i) (∑ j, g x j • c j) l := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = B (f x) (g x) l := by rw [hx, hy]

end IsCoordinatePolynomial
end PolycyclicRecognition

end

end OAI
