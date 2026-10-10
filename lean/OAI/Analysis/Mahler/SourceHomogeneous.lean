import OAI.Analysis.Mahler.ExteriorFlux
import OAI.Analysis.Mahler.HorizontalForms
import OAI.Analysis.Mahler.MassTarget
import Mathlib.Analysis.Analytic.Polynomial

namespace OAI

open Complex
open scoped BigOperators Topology

namespace Mahler

/-- Conversion from the polynomial homogeneity predicate to
its scaling equation; no functional homogeneity assumption is added. -/
lemma eval_homogeneous_scale {σ : Type*} {p : MvPolynomial σ ℂ} {m : ℕ}
    (hp : p.IsHomogeneous m) (z : σ → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun i => c * z i) p = c ^ m * MvPolynomial.eval z p := by
  classical
  simp only [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hd]
  ring

noncomputable def polynomialMap {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ)
    (j : Fin N) (z : ComplexEuclidean n) : ℂ := MvPolynomial.eval (fun i => z i) (G j)

lemma polynomialMap_differentiable {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ) :
    ∀ j, Differentiable ℂ (polynomialMap G j) := by
  intro j x
  have ha : AnalyticAt ℂ (fun z : ComplexEuclidean n =>
      MvPolynomial.eval (fun i => z i) (G j)) x :=
    AnalyticAt.aeval_mvPolynomial
      (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)
  exact ha.differentiableAt

lemma polynomialMap_homogeneous {n N m : ℕ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (hG : ∀ j, (G j).IsHomogeneous m) :
    ∀ j (z : ComplexEuclidean n) (c : ℂ),
      polynomialMap G j (c • z) = c ^ m * polynomialMap G j z := by
  intro j z c
  exact eval_homogeneous_scale (hG j) (fun i => z i) c

lemma tau_pos_of_component_ne_zero {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ι → E → ℂ} {x : E} (hf : ∃ j, f j x ≠ 0) : 0 < tau f x := by
  obtain ⟨j, hj⟩ := hf
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (f k x)) (Finset.mem_univ j)

/-- The original mass hypotheses imply horizontality of the actual homogeneous
exterior derivative at every nonzero point. -/
theorem MassHypotheses.homogeneous_extDeriv_horizontal {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (v : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (logTau (polynomialMap G)))) z ![I • z, v] = 0 :=
  Mahler.homogeneous_extDeriv_horizontal (polynomialMap_differentiable G)
    (tau_pos_of_component_ne_zero (f := polynomialMap G) (x := z) (h.leading_nonzero z hz))
    (polynomialMap_homogeneous h.homogeneous) v

end Mahler

end OAI
