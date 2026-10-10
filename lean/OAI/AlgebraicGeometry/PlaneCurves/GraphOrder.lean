import OAI.AlgebraicGeometry.PlaneCurves.AnalyticOrder
import OAI.AlgebraicGeometry.PlaneCurves.DividedFamilies
import OAI.AlgebraicGeometry.PlaneCurves.LineRestriction

namespace OAI

/-!
# Nested, parametric, and line order along normal graphs
-/

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The selected central expression is an actual analytic function near any
zero-normal point where the inverse chart is analytic. -/
theorem central_expression_analyticAt
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (κ : ComplexPlane → ComplexPlane) (ξ c : ℂ)
    (hκ : AnalyticAt ℂ κ (ξ, 0)) :
    AnalyticAt ℂ
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (κ (q.1, 0))) (ξ, c) := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (ξ, c)
  have hw := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (ξ, c)
  have harg : AnalyticAt ℂ (fun q : ComplexPlane => (q.1, (0 : ℂ))) (ξ, c) :=
    hf.prod analyticAt_const
  have hc := hκ.comp (f := fun q : ComplexPlane => (q.1, (0 : ℂ))) harg
  apply Finset.analyticAt_fun_sum
  intro α hα
  have hr : AnalyticAt ℂ (fun q : ComplexPlane => planePolynomialEval (R α) (κ (q.1, 0))) (ξ, c) :=
    AnalyticAt.comp (g := planePolynomialEval (R α))
      (f := fun q : ComplexPlane => κ (q.1, 0))
      (planePolynomialEval_analyticAt (R α) (κ (ξ, 0))) hc
  exact (hw.pow (j α)).mul hr

/-- The actual central derivative conclusion implies actual analytic order
for the graph-restricted polynomial expression, with the local graph equality
proved from the normal chart rather than assumed as a representation field. -/
theorem graph_expression_order_of_central_jets
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ c : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0)
    (hi : AnalyticAt ℂ e.symm (ξ, 0)) (m : ℕ)
    (hjets : ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0))) (ξ, c) = 0) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) (ξ, c) m := by
  have h := Nagata.Workers.W17.analytic_order_of_iteratedFDeriv_zero
    (central_expression_analyticAt I j R u e.symm ξ c hi) m hjets
  exact h.congr (central_expression_eq_graph_locally I j R u G e he b ξ c hb hsource hG)

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The actual normal polynomial with univariate graph-restricted coefficients. -/
def selectedGraphPolynomial (I : Finset ℕ) (j : ℕ → ℕ)
    (B : ℕ → Polynomial ℂ) (u : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (B α)

theorem eval_selectedGraphPolynomial
    (I : Finset ℕ) (j : ℕ → ℕ) (B : ℕ → Polynomial ℂ) (u : ℕ) (q : ComplexPlane) :
    ((selectedGraphPolynomial I j B u).eval (Polynomial.C q.2)).eval q.1 =
      ∑ α ∈ I.filter (fun α => α + j α = u), q.2 ^ j α * (B α).eval q.1 := by
  simp [selectedGraphPolynomial, Polynomial.eval_finsetSum, mul_comm]

/-- The genuine local graph analytic order gives ordinary ideal-power
multiplicity for its actual finite normal polynomial, via exact coefficient evaluation. -/
theorem selectedGraphPolynomial_order_of_graph_order
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (B : ℕ → Polynomial ℂ) (u : ℕ) (b : ℂ → ℂ) (ξ c : ℂ) (m : ℕ)
    (hR : ∀ α ∈ I.filter (fun α => α + j α = u), ∀ z : ℂ,
      planePolynomialEval (R α) (z, b z) = (B α).eval z)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) (ξ, c) m) :
    selectedGraphPolynomial I j B u ∈ (Nagata.W18.nestedPointIdeal ξ c) ^ m := by
  apply Nagata.W18.nested_polynomial_ideal_order_of_analytic_order _ ξ c m
  apply horder.congr
  exact Filter.Eventually.of_forall fun q => by
    dsimp only
    rw [eval_selectedGraphPolynomial]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hR α hα q.1]

/-- Coefficientwise restriction of the actual selected plane normal polynomial
is literally the graph normal polynomial used above. -/
theorem map_selected_monomial_sum
    {A : Type*} [CommRing A] (φ : A →+* Polynomial ℂ)
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → A) (u : ℕ) :
    Polynomial.map φ
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) =
        selectedGraphPolynomial I j (fun α => φ (T α)) u := by
  simp [selectedGraphPolynomial, Polynomial.map_sum]

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- An actual curve parametrization on G=0 agrees locally with the zero-normal
slice of the normal chart. No inverse for the tangential parametrization is used. -/
theorem inverse_normal_chart_eq_parametric_curve
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (p : ℂ → ComplexPlane) (z₀ : ℂ) (hp : ContinuousAt p z₀)
    (hsource : p z₀ ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 z₀, planePolynomialEval G (p z) = 0) :
    ∀ᶠ z in 𝓝 z₀, e.symm ((p z).1, 0) = p z := by
  have hs : ∀ᶠ z in 𝓝 z₀, p z ∈ e.source :=
    hp.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hs, hG] with z hz hg
  have hh := e.left_inv hz
  simpa only [he, polynomialNormalCoordinates, hg] using hh

/-- Actual reparametrization and homogeneous normal-fiber rescaling. -/
def curveNormalParameter (p : ℂ → ComplexPlane) (a : ℂ → ℂ) (k : ℕ)
    (q : ComplexPlane) : ComplexPlane := ((p q.1).1, q.2 / a q.1 ^ k)

theorem curveNormalParameter_analyticAt
    (p : ℂ → ComplexPlane) (a : ℂ → ℂ) (k : ℕ) (z₀ w₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) (ha : AnalyticAt ℂ a z₀) (ha0 : a z₀ ≠ 0) :
    AnalyticAt ℂ (curveNormalParameter p a k) (z₀, w₀) := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hw := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hpc := hp.comp (f := Prod.fst) hf
  have ht := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := fun q : ComplexPlane => p q.1) hpc
  have hac := ha.comp (f := Prod.fst) hf
  exact ht.prod (hw.div (hac.pow k) (pow_ne_zero k ha0))

/-- Actual central normal order pulls back along an analytic curve and is
preserved by multiplication with the actual homogeneous frame factor a(z)^d. -/
theorem parametric_frame_order_of_central_order
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (p : ℂ → ComplexPlane) (a : ℂ → ℂ) (d k : ℕ) (z₀ w₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) (ha : AnalyticAt ℂ a z₀) (ha0 : a z₀ ≠ 0)
    (hsource : p z₀ ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 z₀, planePolynomialEval G (p z) = 0)
    (m : ℕ)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
      ((p z₀).1, w₀ / a z₀ ^ k) m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => a q.1 ^ d * ∑ α ∈ I,
        (q.2 / a q.1 ^ k) ^ j α * planePolynomialEval (R α) (p q.1)) (z₀, w₀) m := by
  have hc := horder.comp (f := curveNormalParameter p a k) (curveNormalParameter_analyticAt p a k z₀ w₀ hp ha ha0)
  have hg := inverse_normal_chart_eq_parametric_curve G e he p z₀ hp.continuousAt hsource hG
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hge := hf.continuousAt.tendsto.eventually hg
  have hlocal : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        (q.2 / a q.1 ^ k) ^ j α * planePolynomialEval (R α) (p q.1)) (z₀, w₀) m := by
    apply hc.congr
    exact hge.mono fun q hq => by
      change e.symm ((p q.1).1, 0) = p q.1 at hq
      simp only [Function.comp_apply, curveNormalParameter, hq]
  exact Nagata.VariableUnitOrder.analytic_order_mul_left
    ((ha.comp (f := Prod.fst) hf).pow d) hlocal

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The actual selected homogeneous normal polynomial, restricted to a line,
has ordinary surface multiplicity forced by the local normal specialization.
All coefficient/frame identifications use the actual Z=1 chart homomorphism
and actual homogeneous line-restriction homomorphism. -/
theorem line_restricted_initial_order
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 3) ℂ) (i ξ c : ℂ)
    (hline : Nagata.W04.ReducibleSquare.lineRestriction i G = 0)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) =
      polynomialNormalCoordinates (Nagata.W27.directChartHom (2 : Fin 3) G))
    (hsource : (ξ, i ^ 2 - i * ξ) ∈ e.source)
    (hi : AnalyticAt ℂ e.symm (ξ, 0)) (m : ℕ)
    (hjets : ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) (T α))
          (e.symm (q.1, 0))) (ξ, c) = 0) :
    Polynomial.map (Nagata.W04.ReducibleSquare.lineRestriction i)
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) ∈
      (Nagata.W18.nestedPointIdeal ξ c) ^ m := by
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α)
  let b : ℂ → ℂ := fun z => i ^ 2 - i * z
  have hb : ContinuousAt b ξ :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
  have hg : ∀ᶠ z in 𝓝 ξ,
      planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) G) (z, b z) = 0 := by
    exact Filter.Eventually.of_forall fun z => by
      change planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) G) (z, i ^ 2 - i * z) = 0
      rw [Nagata.Workers.W24.planePolynomialEval_directChart_on_line, hline]
      simp
  have horder := graph_expression_order_of_central_jets I j R u
    (Nagata.W27.directChartHom (2 : Fin 3) G) e he b ξ c hb hsource hg hi m hjets
  rw [map_selected_monomial_sum]
  apply selectedGraphPolynomial_order_of_graph_order I j R
    (fun α => Nagata.W04.ReducibleSquare.lineRestriction i (T α)) u b ξ c m _ horder
  intro α hα z
  exact Nagata.Workers.W24.planePolynomialEval_directChart_on_line (T α) i z

end Nagata.Workers.W28

end
end

end OAI
