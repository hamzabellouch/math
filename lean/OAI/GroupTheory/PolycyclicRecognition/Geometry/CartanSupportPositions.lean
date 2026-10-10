import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProductCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs

namespace OAI

/-! # Actual Cartan positions reached by support legs

The positions are products in the nilpotent Cartan group. Their logarithms
are polynomially bounded and have precisely the prescribed canonical height.
-/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] in
/-- Each fixed support direction has an actual product position, uniformly
bounded for every pivot with polynomial logarithmic coordinates. -/
theorem exists_support_position_bound
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (w₀ : W) (w : I → W) {A : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ (h₀ : H),
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ i,
      ∃ h : H,
        Exp h = Exp h₀ * Exp (r • (supportLegDirection T H eW w₀ (w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        ‖(finBasis ℝ H).equivFun h‖ ≤ C * (1 + r) ^ q ∧
        eW (heightProjection T.character h) = r • w i := by
  classical
  let v i := supportLegDirection T H eW w₀ (w i)
  let V := ∑ i, ‖(finBasis ℝ H).equivFun (v i)‖
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv i : ‖(finBasis ℝ H).equivFun (v i)‖ ≤ V :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((finBasis ℝ H).equivFun (v j)))
      (Finset.mem_univ i)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, q, hC, hb⟩ := exists_cartan_scaled_mul_log_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD hA hV p
  refine ⟨C, q, hC, ?_⟩
  intro r hr h₀ hh₀ hπ₀ i
  let d := F.ExpD (F.D.equiv h₀) * F.ExpD (F.D.equiv (r • v i))
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : Exp h = Exp h₀ * Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [← F.compatibleD h,
      show F.ExpD (F.D.equiv h) = d from exp_cartanLog H F.D.equiv F.ExpD hbijD d]
    dsimp only [d]
    rw [map_mul, F.compatibleD, F.compatibleD]
    rfl
  refine ⟨h, he, hb r hr h₀ (v i) hh₀ (hv i), ?_⟩
  rw [← hπ, he, map_mul]
  change (π (Exp h₀)).toAdd +
    (π (Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd = _
  rw [hπ₀, hπ, map_smul, map_smul,
    show eW (heightProjection T.character (v i)) = w i - w₀ from
      supportLegDirection_height T H eW w₀ (w i)]
  module

end PolycyclicRecognition.CartanFactorModel

end

end OAI
