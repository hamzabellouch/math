import OAI.Analysis.KadisonKastler.StandardBoundaryIsomorphism
import OAI.Analysis.KadisonKastler.ConstantFieldCocycle
import OAI.Analysis.KadisonKastler.AlgebraCocycleRepresentatives

namespace OAI

/-! # The finite-factor isomorphism in common tracial position

All boundary fields are constructed from the actual Kadison--Kastler
approximants. Only the scalar boundary means and their double-ergodicity
property, together with the precisely stated Tomiyama input, are supplied.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u v w

variable {H : Type u} {G : Type v} {D : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [Group G] [Countable G]
  [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace D]
  {μ : Measure D} [IsProbabilityMeasure μ] {M N : VonNeumannAlgebra H}

/-- Common standard position and the `768b` conjugation estimate produce
an actual star isomorphism with displacement at most `378b`. -/
theorem exists_standard_finiteFactor_isomorphism
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (hΩ : pM.vector = pN.vector)
    (α : NonsingularAction G D μ) (m : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean α.prod)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (hTom₂ : PublishedFieldTomiyama (G := G × G) (H := H) (μ := μ.prod μ))
    (herg : UnitaryDoubleErgodic.{v, w, u} α)
    (U : G →* unitary (Algebra M))
    (hU : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm pM.trace ((u : Algebra M) - U g) < ε)
    {b : ℝ} (hb : b < 1 / 100000) (hgap : kkDistance M N < b)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ 768 * b) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤ 378 * b * ‖x‖ := by
  classical
  have hb0 : 0 < b := (kkDistance_nonneg M N).trans_lt hgap
  choose V hV using fun g : G => exists_unitary_approx_of_kkDistance hN hgap (U g)
  let U₀ : G →* unitary (H →L[ℂ] H) :=
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)).toMonoidHom.comp U
  have hV₀ (g : G) : ‖(V g : H →L[ℂ] H) - (U₀ g : H →L[ℂ] H)‖ ≤ 3 * b :=
    (hV g).le
  obtain ⟨W, hWm, hWN, hWc, hWclose⟩ := m.exists_measurable_cocycle_near_representation
    hTom U₀ V (by positivity : 0 ≤ 3 * b) (by linarith : 3 * (3 * b) ≤ 1 / 64) hV₀
  let WN := algebraCocycleRepresentative N W
  have hWNm := algebraCocycleRepresentative_measurable N W hWN hWm
  have hWNc (g t : G) : ∀ᵐ x ∂μ, (WN (g * t) x : Algebra N) =
      (WN g x : Algebra N) * WN t (α.toPerm g⁻¹ x) :=
    (algebraCocycleRepresentative_cocycle N α W hWN hWc g t).mono fun _ hx => hx.symm
  have hWNclose (g : G) : ∀ᵐ x ∂μ,
      ‖(WN g x : Algebra N).val - (U g : Algebra M).val‖ ≤ 21 * b := by
    have hc := algebraCocycleRepresentative_close N W hWN
      (fun t => (U₀ t : H →L[ℂ] H)) hWclose g
    change ∀ᵐ x ∂μ, ‖(algebraCocycleRepresentative N W g x : Algebra N).val -
      (U₀ g : H →L[ℂ] H)‖ ≤ 21 * b
    simpa only [show 7 * (3 * b) = 21 * b by ring] using hc
  have hC0 : 0 ≤ 378 * b := by positivity
  have hC1 : 378 * b < 1 / 10 := by linarith
  have hC2 : (378 * b) ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hC1 hC0 (by norm_num)
  obtain ⟨θ, hθ⟩ := exists_standard_starEquiv_of_boundary_cocycle hM hN pM pN hΩ
    α m₂ hTom₂ herg U hU WN hWNm hWNc
    (by positivity : 0 ≤ 21 * b) (by positivity : 0 ≤ 768 * b) hWNclose hJ
    (by linarith : 2 * (21 * b) + 2 * (768 * b) < 1)
    (by linarith : 2 * (21 * b) < 1)
    (by nlinarith only [hC1, hC2] : 3 * (18 * (21 * b)) + (18 * (21 * b)) ^ 2 < 2)
    (by linarith : kkDistance M N + 18 * (21 * b) < 1)
  refine ⟨θ, fun x => ?_⟩
  convert hθ x using 1; ring

end

end KadisonKastler

end OAI
