import Mathlib
import OAI.Analysis.SymmetricDomains.GenericAlgebraicRamificationUniform

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial Set Filter Topology Metric MeasureTheory

lemma complexify_mv_eval {n : ℕ} (D : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (realParameter x) (MvPolynomial.map Complex.ofRealHom D) =
      (MvPolynomial.eval x D : ℂ) := by
  rw [MvPolynomial.eval_map]
  change _ = Complex.ofRealHom (MvPolynomial.eval x D)
  rw [MvPolynomial.eval₂_comp]
  rfl

lemma complexify_polynomial_eval {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℝ))
    (x : Fin n → ℝ) (y : ℝ) :
    (q.map (MvPolynomial.map Complex.ofRealHom)).eval₂ (MvPolynomial.eval (realParameter x))
      (y : ℂ) = ((q.eval₂ (MvPolynomial.eval x) y : ℝ) : ℂ) := by
  change _ = Complex.ofRealHom (q.eval₂ (MvPolynomial.eval x) y)
  rw [Polynomial.eval₂_map,Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext (fun D => complexify_mv_eval D x)

theorem semialgebraic_function_algebraic_data {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
        P.resultant P.derivative ≠ 0 ∧
        ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a ∧
          P.eval₂ (MvPolynomial.eval (realParameter a)) (f a : ℂ) = 0 := by
  obtain ⟨D₁,hD₁,hfa⟩ := semialgebraic_function_analytic_off_polynomial B f hgraph
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let p' := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hp' : p' ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) p' hp'
  let e : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℂ :=
    MvPolynomial.map Complex.ofRealHom
  have hei : Function.Injective e := MvPolynomial.map_injective _ Complex.ofReal_injective
  have hQ : q.map e ≠ 0 := by
    simpa only [Polynomial.map_zero] using (Polynomial.map_injective e hei).ne hq
  have hres : (q.map e).resultant (q.map e).derivative ≠ 0 := by
    rw [Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective hei,
      Polynomial.natDegree_map_eq_of_injective hei,Polynomial.resultant_map_map]
    exact hei.ne (resultant_derivative_ne_zero_of_generic_separable q hqs)
  refine ⟨D₀*D₁,mul_ne_zero hD₀ hD₁,q.map e,hQ,hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  refine ⟨hfa a ha hD₁a,?_⟩
  have hpr' : p'.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,p'] using hpr a ha
  have hqr := (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  change (q.map (MvPolynomial.map Complex.ofRealHom)).eval₂ _ _ = 0
  rw [complexify_polynomial_eval,hqr,Complex.ofReal_zero]

lemma realParameter_dist {n : ℕ} (x y : Fin n → ℝ) :
    dist (realParameter x) (realParameter y) = dist x y := by
  rw [dist_eq_norm,dist_eq_norm]
  have hh : realParameter x-realParameter y = realParameter (x-y) := by
    ext i
    exact (Complex.ofReal_sub _ _).symm
  rw [hh,norm_realParameter]

theorem generic_real_parameter_polynomial_nonzero {n : ℕ}
    (D : MvPolynomial (Fin (n+1)) ℝ) (hD : D ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) r,
        MvPolynomial.eval (Fin.cons t x) D ≠ 0 := by
  have hi := MvPolynomial.map_injective (σ := Fin (n+1)) Complex.ofRealHom
    Complex.ofReal_injective
  obtain ⟨E,hE,hn⟩ := generic_fin_polynomial_parameter_nonzero
    (MvPolynomial.map Complex.ofRealHom D) (hi.ne hD)
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨r,hr,hn⟩ := hn s hs
  refine ⟨r,hr,?_⟩
  intro x hx t ht
  have hx' : realParameter x ∈ ball (realParameter s) r := by
    simpa only [mem_ball,realParameter_dist] using hx
  have ht' : (t : ℂ) ∈ ball 0 r := by
    simpa only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] using ht.2
  have hh := hn (realParameter x) hx' (t : ℂ) ht' (Complex.ofReal_ne_zero.mpr ht.1.ne')
  have he : Fin.cons (t : ℂ) (realParameter x) = realParameter (Fin.cons t x) := by
    ext i
    refine Fin.cases rfl (fun _ => rfl) i
  rw [he,complexify_mv_eval] at hh
  exact fun hz => hh (by rw [hz,Complex.ofReal_zero])

end Release061

end

end OAI
