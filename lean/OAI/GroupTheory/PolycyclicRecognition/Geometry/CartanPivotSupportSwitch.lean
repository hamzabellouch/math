import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportVisits

namespace OAI

/-! # The short-switch estimate at the actual pivot/support product -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The polynomial logarithm of the pivot/support product supplies the
logarithmic switch diameter, uniformly over all starting sheets. -/
theorem exists_pivot_support_switch_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (w₀ : W) (w : Fin M.letterCount → W)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ), 0 ≤ r → ∀ h₀ : H,
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ →
      ∀ (n : G) (i : Fin M.letterCount) (b : ℝ), |b| ≤ B * Real.exp (r * s i) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist
          (n * Exp ((t * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (supportLegDirection T H eW w₀ (w i) :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))))
          (n * Exp ((u * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (supportLegDirection T H eW w₀ (w i) :
              GroupLieAlgebra (𝓘(ℝ, EG)) G)))) ≤ K * Real.log (2 + r) := by
  obtain ⟨D, q, hD, hpos⟩ := F.exists_support_position_bound T eW haarD dynkinD
    π hπ w₀ w hA p
  obtain ⟨K, hK, hswitch⟩ := M.exists_uniform_support_switch_curve_bound T Exp hExp realize hD hB q
  refine ⟨K, hK, ?_⟩
  intro r hr h₀ hnorm hheight n i b hb t ht u hu
  obtain ⟨h, he, hnorm', hheight'⟩ := hpos r hr h₀ hnorm hheight i
  have hweight : M.weight i h = r * s i := by
    rw [← cartanHeightWeight_projection T H (M.weight i) h]
    have hp : heightProjection T.character h = eW.symm (r • w i) := by
      rw [← hheight', eW.symm_apply_apply]
    rw [hp, map_smul, map_smul, hs, smul_eq_mul]
  have hh := hswitch i r hr n h (s i) b hnorm' hweight hb t ht u hu
  simpa only [rootSwitchCurve, he] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
