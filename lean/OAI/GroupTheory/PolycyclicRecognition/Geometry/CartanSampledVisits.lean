import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDirectionalVisits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitRescale

namespace OAI

/-! # Support visits for the actual exponentially scaled root samples -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

/-- The root curve uses the normalized interval amplitude. -/
def sampledDirectionalVisitPath (v : H) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r s b : ℝ) :
    Path (n * Exp h₀)
      (n * Exp ((b * Real.exp (r * s)) •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d := fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f := fun t : ℝ => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd := continuous_exp_line_of_published_realization T Exp hExp realize v
  have hf := continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i)
  exact supportVisitPath d hd (by simp [d, hExp.map_zero])
    (fun t => f (t * Real.exp (r * s))) (hf.comp (continuous_id.mul_const _))
    (by simp [f, hExp.map_zero]) n (Exp h₀) r b

omit [IsIsometricSMul G G] in
/-- Scaling the root amplitude does not alter the parametrized geometric visit. -/
theorem sampledDirectionalVisitPath_apply (v : H) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r s b : ℝ) (t : unitInterval) :
    M.sampledDirectionalVisitPath T hExp realize v i n h₀ r s b t =
      M.directionalVisitPath T hExp realize v i n h₀ r (b * Real.exp (r * s)) t := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact supportVisitPath_comp_mul
    (fun u : ℝ => Exp (u • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun u : ℝ => Exp (u • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i))
    (by simp [hExp.map_zero]) n (Exp h₀) r b (Real.exp (r * s)) t

include F in
/-- One uniform constant controls the actual normalized interval samples,
with no dependence on the starting sheet or the scale. -/
theorem exists_sampled_directional_visit_bound
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (v : Fin M.letterCount → H) (w₀ : W) (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (w₀ + eW (heightProjection T.character (v i)))) = s i)
    {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ h₀ : H,
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ n : G, ∀ i b,
      |b| ≤ 2 * ρ →
      PathMetricBound (M.sampledDirectionalVisitPath T hExp realize (v i) i n h₀ r (s i) b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (n * Exp (((t * b) * Real.exp (r * s i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
          (n * Exp (((u * b) * Real.exp (r * s i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) ≤
          C * Real.log (2 + r) := by
  obtain ⟨C, hC, hv⟩ := M.exists_directional_visit_bound T F hExp realize haarD dynkinD
    eW π hπ v w₀ s hs hA (show (0 : ℝ) ≤ 2 * ρ by positivity) p
  refine ⟨C, hC, ?_⟩
  intro r hr h₀ hh₀ hheight n i b hb
  have hamp : |b * Real.exp (r * s i)| ≤ (2 * ρ) * Real.exp (r * s i) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  obtain ⟨hmetric, hswitch⟩ := hv r hr h₀ hh₀ hheight n i _ hamp
  constructor
  · intro u t
    rw [sampledDirectionalVisitPath_apply, sampledDirectionalVisitPath_apply]
    exact hmetric u t
  · intro t ht u hu
    simpa only [mul_assoc] using hswitch t ht u hu

end PolycyclicRecognition.CartanWordModel

end

end OAI
