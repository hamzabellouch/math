import OAI.AlgebraicGeometry.PlaneCurves.GraphOrder
import OAI.AlgebraicGeometry.PlaneCurves.NormalPolynomials

namespace OAI

/-!
# Homogeneous multiplicity in normal frames and swapped charts; Homogeneous smooth curve charts
-/

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology

/-- Actual affine chart coordinates of a homogeneous analytic parametrization. -/
def normalizedCurvePoint (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ) : ComplexPlane :=
  (X (c.succAbove 0) z / X c z, X (c.succAbove 1) z / X c z)

theorem normalizedCurvePoint_analyticAt
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ : ℂ)
    (hX : ∀ i, AnalyticAt ℂ (X i) z₀) (hc : X c z₀ ≠ 0) :
    AnalyticAt ℂ (normalizedCurvePoint X c) z₀ :=
  ((hX (c.succAbove 0)).div (hX c) hc).prod
    ((hX (c.succAbove 1)).div (hX c) hc)

/-- The actual homogeneous curve equation implies the actual affine chart equation. -/
theorem normalizedCurvePoint_equation
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ)
    (hc : X c z ≠ 0) (hzero : MvPolynomial.eval (fun a => X a z) G = 0) :
    planePolynomialEval (Nagata.W27.directChartHom c G) (normalizedCurvePoint X c z) = 0 := by
  let x : Fin 3 → ℂ := fun a => X a z
  let v : Fin 2 → ℂ := fun a => x (c.succAbove a) / x c
  let y : Fin 3 → ℂ := Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v
  have hy : (fun a => x c * y a) = x := by
    exact Nagata.Workers.W17.scaled_chart_vector c x hc
  have hh := Nagata.W16.homogeneous_eval_scale hG y (x c)
  rw [hy, hzero] at hh
  have hz : MvPolynomial.eval y G = 0 :=
    (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero k hc)
  have he : planePolynomialEval (Nagata.W27.directChartHom c G) (normalizedCurvePoint X c z) =
      MvPolynomial.eval v (Nagata.W27.directChartHom c G) := by
    apply congrArg (fun a : Fin 2 → ℂ => MvPolynomial.eval a (Nagata.W27.directChartHom c G))
    funext a
    fin_cases a <;> rfl
  rw [he, Nagata.Workers.W17.eval_directChartHom]
  exact hz

/-- The homogeneous-to-affine equation holds on an actual neighborhood where
the chosen analytic homogeneous coordinate stays nonzero. -/
theorem normalizedCurvePoint_equation_locally
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ : ℂ)
    (ha : ContinuousAt (X c) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0) :
    ∀ᶠ z in 𝓝 z₀, planePolynomialEval (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z) = 0 := by
  filter_upwards [ha.eventually_ne hc, hzero] with z hcz hz
  exact normalizedCurvePoint_equation G k hG X c z hcz hz

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

theorem homogeneous_normal_frame_identity_plane
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z w : ℂ) (hc : X c z ≠ 0) :
    (∑ α ∈ I, w ^ j α * MvPolynomial.eval (fun a => X a z) (T α)) =
      (X c z)^d * ∑ α ∈ I, (w/(X c z)^k)^j α *
        planePolynomialEval (Nagata.W27.directChartHom c (T α)) (normalizedCurvePoint X c z) := by
  rw [Nagata.Workers.W17.normal_polynomial_frame_identity I j T d k hhom hbound c (fun a => X a z) hc w]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v (Nagata.W27.directChartHom c (T α)))
  funext a
  fin_cases a <;> rfl

/-- Central normal order implies actual homogeneous polynomial order on an
analytic parametrized curve, with the exact variable degree-d frame factor. -/
theorem homogeneous_normal_order_of_central_order
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates (Nagata.W27.directChartHom c G))
    (hsource : normalizedCurvePoint X c z₀ ∈ e.source) (m : ℕ)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        q.2 ^ j α * planePolynomialEval (Nagata.W27.directChartHom c (T α)) (e.symm (q.1, 0)))
      ((normalizedCurvePoint X c z₀).1, w₀ / X c z₀ ^ k) m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  have hp := normalizedCurvePoint_analyticAt X c z₀ hX hc
  have hcurve := normalizedCurvePoint_equation_locally G k hG X c z₀ (hX c).continuousAt hc hzero
  have h := parametric_frame_order_of_central_order I j
    (fun α => Nagata.W27.directChartHom c (T α)) (Nagata.W27.directChartHom c G)
    e he (normalizedCurvePoint X c) (X c) d k z₀ w₀ hp (hX c) hc hsource hcurve m horder
  apply h.congr
  have hne := (hX c).continuousAt.eventually_ne hc
  have hf : ContinuousAt (Prod.fst : ComplexPlane → ℂ) (z₀, w₀) := continuousAt_fst
  exact (hf.tendsto.eventually hne).mono fun q hq => by
    exact (homogeneous_normal_frame_identity_plane I j T d k hhom hbound X c q.1 q.2 hq).symm

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- Swapping actual affine coordinates preserves analyticity of a curve. -/
theorem analyticAt_curve_swap (p : ℂ → ComplexPlane) (z₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) : AnalyticAt ℂ (fun z => (p z).swap) z₀ := by
  exact (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := p) hp).prod
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := p) hp)

/-- The alternative tangential coordinate changes neither the homogeneous
normal expression nor its variable frame and fiber weights. -/
theorem homogeneous_normal_order_of_swapped_central_order
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates
      (Nagata.Workers.W17.affineSwap (Nagata.W27.directChartHom c G)))
    (hsource : (normalizedCurvePoint X c z₀).swap ∈ e.source) (m : ℕ)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        q.2 ^ j α * planePolynomialEval
          (Nagata.Workers.W17.affineSwap (Nagata.W27.directChartHom c (T α))) (e.symm (q.1, 0)))
      ((normalizedCurvePoint X c z₀).2, w₀ / X c z₀ ^ k) m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I,
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  have hp := analyticAt_curve_swap (normalizedCurvePoint X c) z₀
    (normalizedCurvePoint_analyticAt X c z₀ hX hc)
  have hcurve : ∀ᶠ z in 𝓝 z₀,
      planePolynomialEval (Nagata.Workers.W17.affineSwap (Nagata.W27.directChartHom c G))
        (normalizedCurvePoint X c z).swap = 0 := by
    simpa only [Nagata.Workers.W17.eval_affineSwap, Prod.swap_swap] using
      normalizedCurvePoint_equation_locally G k hG X c z₀ (hX c).continuousAt hc hzero
  have h := parametric_frame_order_of_central_order I j
    (fun α => Nagata.Workers.W17.affineSwap (Nagata.W27.directChartHom c (T α)))
    (Nagata.Workers.W17.affineSwap (Nagata.W27.directChartHom c G))
    e he (fun z => (normalizedCurvePoint X c z).swap) (X c) d k z₀ w₀
    hp (hX c) hc hsource hcurve m horder
  simp only [Nagata.Workers.W17.eval_affineSwap, Prod.swap_swap] at h
  apply h.congr
  have hne := (hX c).continuousAt.eventually_ne hc
  have hf : ContinuousAt (Prod.fst : ComplexPlane → ℂ) (z₀, w₀) := continuousAt_fst
  exact (hf.tendsto.eventually hne).mono fun q hq => by
    exact (homogeneous_normal_frame_identity_plane I j T d k hhom hbound X c q.1 q.2 hq).symm

end Nagata.Workers.W28

end
end

end OAI
