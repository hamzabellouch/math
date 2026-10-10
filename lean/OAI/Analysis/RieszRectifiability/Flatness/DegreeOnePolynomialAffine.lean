import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Affine representations of degree-one polynomials

Evaluation of a homogeneous degree-one complex polynomial on real Euclidean
space is a continuous real-linear map. Splitting off the constant homogeneous
component gives an affine representation for polynomials of degree at most one.
-/

namespace RieszRectifiability

noncomputable section

theorem homogeneous_degree_one_eval_linear {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous 1) :
    ∃ L : Ambient d →L[ℝ] ℂ, ∀ x : Ambient d,
      MvPolynomial.eval (fun j => (x j : ℂ)) P = L x := by
  have hmem : P ∈ Submodule.span ℂ (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℂ)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hP
  clear hP
  induction hmem using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨i, rfl⟩ := hQ
    refine ⟨Complex.ofRealCLM.comp (EuclideanSpace.proj i), fun x => ?_⟩
    rw [MvPolynomial.eval_X]
    rfl
  | zero =>
    exact ⟨0, fun x => by simp only [map_zero, zero_apply]⟩
  | add Q R _ _ hQ hR =>
    obtain ⟨L, hL⟩ := hQ
    obtain ⟨M, hM⟩ := hR
    refine ⟨L + M, fun x => ?_⟩
    rw [map_add, hL x, hM x]
    rfl
  | smul c Q _ hQ =>
    obtain ⟨L, hL⟩ := hQ
    refine ⟨c • L, fun x => ?_⟩
    rw [MvPolynomial.smul_eval, hL x]
    rfl

theorem degree_one_polynomial_eval_affine {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.totalDegree ≤ 1) :
    ∃ c : ℂ, ∃ L : Ambient d →L[ℝ] ℂ, ∀ x : Ambient d,
      MvPolynomial.eval (fun j => (x j : ℂ)) P = c + L x := by
  rcases (show P.totalDegree = 0 ∨ P.totalDegree = 1 by omega) with h0 | h1
  · have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    refine ⟨P.coeff 0, 0, fun x => ?_⟩
    calc
      _ = MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.C (P.coeff 0)) :=
        congrArg (MvPolynomial.eval (fun j => (x j : ℂ))) heq
      _ = _ := by simp only [MvPolynomial.eval_C, zero_apply, add_zero]
  · obtain ⟨L, hL⟩ := homogeneous_degree_one_eval_linear (MvPolynomial.homogeneousComponent 1 P)
      (MvPolynomial.homogeneousComponent_isHomogeneous 1 P)
    have hsplit : P = MvPolynomial.C (P.coeff 0) + MvPolynomial.homogeneousComponent 1 P := by
      have h := MvPolynomial.sum_homogeneousComponent P
      rw [h1] at h
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        MvPolynomial.homogeneousComponent_zero] using! h.symm
    refine ⟨P.coeff 0, L, fun x => ?_⟩
    calc
      _ = MvPolynomial.eval (fun j => (x j : ℂ))
          (MvPolynomial.C (P.coeff 0) + MvPolynomial.homogeneousComponent 1 P) :=
        congrArg (MvPolynomial.eval (fun j => (x j : ℂ))) hsplit
      _ = _ := by rw [map_add, MvPolynomial.eval_C, hL x]

end

end RieszRectifiability

end OAI
