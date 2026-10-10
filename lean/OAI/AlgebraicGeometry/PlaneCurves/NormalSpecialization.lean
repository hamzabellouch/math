import OAI.AlgebraicGeometry.PlaneCurves.HomogeneousOrder

namespace OAI

/-!
# Homogeneous normal specialization for lines and smooth curves
-/

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- A nonzero actual normal partial makes the actual polynomial differential nonzero. -/
theorem polynomialGradient_ne_zero_of_partial
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0) :
    polynomialGradient G p ≠ 0 := by
  intro h
  have hh := congrArg (fun L : ComplexPlane →L[ℂ] ℂ => L (0, 1)) h
  apply hpartial
  simpa [polynomialGradient] using hh

/-- Local normal specialization with its analytic chart and actual derivative
constructed from the polynomial and a nonzero actual normal partial. -/
theorem exists_normal_specialization_from_partial
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (p V : ComplexPlane)
    (hp : planePolynomialEval G p = 0)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (factoredPlaneFamily I j R G s)) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧ AnalyticAt ℂ e.symm (e p) ∧
      ∀ n < m, iteratedFDeriv ℂ n
        (fun q : ComplexPlane =>
          ∑ α ∈ I.filter (fun α => α + j α = u),
            q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
        (p.1, polynomialGradient G p V) = 0 := by
  obtain ⟨e, he, hsource, hi⟩ := exists_analytic_normal_chart_of_partial_ne_zero G p hpartial
  have hi' : AnalyticAt ℂ e.symm (e p) := by simpa only [he] using hi
  refine ⟨e, he, hsource, hi', ?_⟩
  exact normal_specialization_central_jets I j R u hmin G e he
    (polynomialGradient G p) p V hsource hi' (planePolynomialEval_hasFDerivAt G p)
    hp exceptional m horders

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- Actual ordinary multiplicities of a finite plane polynomial family along
an affine motion specialize to actual ideal-power multiplicity of the literal
line-restricted initial normal polynomial. The chart and analytic limit are
constructed in the proof from the nonzero actual normal partial. -/
theorem line_normal_specialization
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 3) ℂ) (i ξ : ℂ) (V : ComplexPlane)
    (hline : Nagata.W04.ReducibleSquare.lineRestriction i G = 0)
    (hpartial : planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ, i ^ 2 - i * ξ) ≠ 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then ((ξ, i ^ 2 - i * ξ) + s • V).1
          else ((ξ, i ^ 2 - i * ξ) + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α))
          (Nagata.W27.directChartHom (2 : Fin 3) G) s)) :
    Polynomial.map (Nagata.W04.ReducibleSquare.lineRestriction i)
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) ∈
      (Nagata.W18.nestedPointIdeal ξ
        (polynomialGradient (Nagata.W27.directChartHom (2 : Fin 3) G)
          (ξ, i ^ 2 - i * ξ) V)) ^ m := by
  let p : ComplexPlane := (ξ, i ^ 2 - i * ξ)
  let A := Nagata.W27.directChartHom (2 : Fin 3) G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α)
  have hp : planePolynomialEval A p = 0 := by
    dsimp [A, p]
    rw [Nagata.Workers.W24.planePolynomialEval_directChart_on_line, hline]
    simp
  obtain ⟨e, he, hs, hi, hjets⟩ := exists_normal_specialization_from_partial
    I j R u hmin A p V hp hpartial exceptional m horders
  have hi' : AnalyticAt ℂ e.symm (ξ, 0) := by
    have hep : e p = (ξ, (0 : ℂ)) := by
      rw [he]
      change (p.1, planePolynomialEval A p) = (ξ, 0)
      rw [hp]
    rwa [hep] at hi
  exact line_restricted_initial_order I j T u G i ξ
    (polynomialGradient A p V) hline e he hs hi' m hjets

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- Actual moving plane-curve multiplicities imply actual homogeneous normal
polynomial order along an analytic parametrized homogeneous curve. Every local
normal chart, derivative, zero-parameter limit, and variable frame factor is
constructed by the checked bridge chain. -/
theorem homogeneous_normal_specialization
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z₀) ≠ 0)
    (V : ComplexPlane)
    (hvelocity : polynomialGradient (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then (normalizedCurvePoint X c z₀ + s • V).1
          else (normalizedCurvePoint X c z₀ + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom c (T α))
          (Nagata.W27.directChartHom c G) s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  let p := normalizedCurvePoint X c z₀
  let A := Nagata.W27.directChartHom c G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom c (T α)
  have hp : planePolynomialEval A p = 0 :=
    normalizedCurvePoint_equation G k hG X c z₀ hc hzero.self_of_nhds
  obtain ⟨e, he, hs, hi, hjets⟩ := exists_normal_specialization_from_partial
    I j R u hmin A p V hp hpartial exceptional m horders
  have hi' : AnalyticAt ℂ e.symm (p.1, 0) := by
    have hep : e p = (p.1, (0 : ℂ)) := by
      rw [he]
      change (p.1, planePolynomialEval A p) = (p.1, 0)
      rw [hp]
    rwa [hep] at hi
  have hcentral : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
      (p.1, w₀ / X c z₀ ^ k) m := by
    rw [← hvelocity]
    exact Nagata.Workers.W17.analytic_order_of_iteratedFDeriv_zero
      (central_expression_analyticAt I j R u e.symm p.1 (polynomialGradient A p V) hi') m hjets
  exact homogeneous_normal_order_of_central_order (I.filter (fun α => α + j α = u)) j T d k
    (fun α hα => hhom α (Finset.mem_filter.mp hα).1)
    (fun α hα => hbound α (Finset.mem_filter.mp hα).1) G hG X c z₀ w₀ hX hc hzero
    e he hs m hcentral

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The same actual homogeneous family and normal displacement specialize
when only the first affine partial is known nonzero. The proof swaps actual
polynomials, points and velocities, and restores the original frame expression. -/
theorem homogeneous_normal_specialization_of_partialX
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 0 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z₀) ≠ 0)
    (V : ComplexPlane)
    (hvelocity : polynomialGradient (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then (normalizedCurvePoint X c z₀ + s • V).1
          else (normalizedCurvePoint X c z₀ + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom c (T α))
          (Nagata.W27.directChartHom c G) s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  let p := normalizedCurvePoint X c z₀
  let A := Nagata.W27.directChartHom c G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom c (T α)
  have hp : planePolynomialEval A p = 0 :=
    normalizedCurvePoint_equation G k hG X c z₀ hc hzero.self_of_nhds
  have hps : planePolynomialEval (Nagata.Workers.W17.affineSwap A) p.swap = 0 := by
    simpa only [Nagata.Workers.W17.eval_affineSwap, Prod.swap_swap] using hp
  have hpartialS : planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.Workers.W17.affineSwap A)) p.swap ≠ 0 := by
    rwa [Nagata.Workers.W17.partialY_affineSwap]
  have hvelocityS : polynomialGradient (Nagata.Workers.W17.affineSwap A) p.swap V.swap =
      w₀ / X c z₀ ^ k := by
    rw [Nagata.Workers.W17.polynomialGradient_affineSwap]
    exact hvelocity
  have hordersS : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then (p.swap + s • V.swap).1 else (p.swap + s • V.swap).2)
        m (factoredPlaneFamily I j (fun α => Nagata.Workers.W17.affineSwap (R α))
          (Nagata.Workers.W17.affineSwap A) s) := by
    filter_upwards [horders] with s hs hex
    rw [← Nagata.Workers.W17.affineSwap_factoredPlaneFamily]
    exact (Nagata.Workers.W17.order_affineSwap_iff
      (factoredPlaneFamily I j R A s) (p + s • V) m).mpr (hs hex)
  obtain ⟨e, he, hs, hi, hjets⟩ := exists_normal_specialization_from_partial
    I j (fun α => Nagata.Workers.W17.affineSwap (R α)) u hmin
    (Nagata.Workers.W17.affineSwap A) p.swap V.swap hps hpartialS exceptional m hordersS
  have hi' : AnalyticAt ℂ e.symm (p.2, 0) := by
    have hep : e p.swap = (p.2, (0 : ℂ)) := by
      rw [he]
      change (p.2, planePolynomialEval (Nagata.Workers.W17.affineSwap A) p.swap) = (p.2, 0)
      rw [hps]
    rwa [hep] at hi
  have hcentral : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (Nagata.Workers.W17.affineSwap (R α)) (e.symm (q.1, 0)))
      (p.2, w₀ / X c z₀ ^ k) m := by
    rw [← hvelocityS]
    exact Nagata.Workers.W17.analytic_order_of_iteratedFDeriv_zero
      (central_expression_analyticAt I j (fun α => Nagata.Workers.W17.affineSwap (R α)) u e.symm
        p.2 (polynomialGradient (Nagata.Workers.W17.affineSwap A) p.swap V.swap) hi') m hjets
  exact homogeneous_normal_order_of_swapped_central_order (I.filter (fun α => α + j α = u)) j T d k
    (fun α hα => hhom α (Finset.mem_filter.mp hα).1)
    (fun α hα => hbound α (Finset.mem_filter.mp hα).1) G hG X c z₀ w₀ hX hc hzero
    e he hs m hcentral

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The actual polynomial differential is nonzero exactly when at least one
of its two actual coordinate partials is nonzero. -/
theorem polynomialGradient_ne_zero_iff_partials
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    polynomialGradient G p ≠ 0 ↔
      planePolynomialEval (MvPolynomial.pderiv 0 G) p ≠ 0 ∨
      planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0 := by
  constructor
  · intro h
    by_cases h0 : planePolynomialEval (MvPolynomial.pderiv 0 G) p ≠ 0
    · exact Or.inl h0
    · right
      intro h1
      apply h
      apply ContinuousLinearMap.ext
      intro z
      simp [polynomialGradient, not_ne_iff.mp h0, h1]
  · intro h
    rcases h with h0 | h1
    · intro hz
      have hh := congrArg (fun L : ComplexPlane →L[ℂ] ℂ => L (1, 0)) hz
      apply h0
      simpa [polynomialGradient] using hh
    · exact polynomialGradient_ne_zero_of_partial G p h1

/-- Both genuine smooth affine directions lead to the same actual normal
polynomial, same original moving family and same homogeneous frame scaling. -/
theorem homogeneous_normal_specialization_of_gradient
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hgradient : planePolynomialEval (MvPolynomial.pderiv 0 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z₀) ≠ 0 ∨
      planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z₀) ≠ 0)
    (V : ComplexPlane)
    (hvelocity : polynomialGradient (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then (normalizedCurvePoint X c z₀ + s • V).1
          else (normalizedCurvePoint X c z₀ + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom c (T α))
          (Nagata.W27.directChartHom c G) s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  rcases hgradient with h0 | h1
  · exact homogeneous_normal_specialization_of_partialX I j T u hmin d k hhom hbound
      G hG X c z₀ w₀ hX hc hzero h0 V hvelocity exceptional m horders
  · exact homogeneous_normal_specialization I j T u hmin d k hhom hbound
      G hG X c z₀ w₀ hX hc hzero h1 V hvelocity exceptional m horders

/-- The source smoothness input is the actual nonzero polynomial differential,
with no fixed partial direction or analytic normal chart supplied as a hypothesis. -/
theorem homogeneous_normal_specialization_of_nonzero_differential
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hdifferential : polynomialGradient (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z₀) ≠ 0)
    (V : ComplexPlane)
    (hvelocity : polynomialGradient (Nagata.W27.directChartHom c G)
      (normalizedCurvePoint X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then (normalizedCurvePoint X c z₀ + s • V).1
          else (normalizedCurvePoint X c z₀ + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom c (T α))
          (Nagata.W27.directChartHom c G) s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  exact homogeneous_normal_specialization_of_gradient I j T u hmin d k hhom hbound
    G hG X c z₀ w₀ hX hc hzero
    ((polynomialGradient_ne_zero_iff_partials _ _).mp hdifferential)
    V hvelocity exceptional m horders

end Nagata.Workers.W28

end
end

end OAI
