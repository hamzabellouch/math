import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentNegativePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeights

namespace OAI

/-! # Actual negative chains between Cartan-factor representatives -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- Every fixed Cartan-factor displacement admits actual unit-step chains
along the chosen negative ray, with polynomial length and linear radius. -/
theorem exists_negative_height_cartan_fiber_chains
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (β : W →L[ℝ] ℝ) (v₀ : W) (hv₀ : β v₀ < 0) (d : F.D.carrier) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (q : ℕ) (R : ℝ), 0 ≤ R ∧ ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = ray n) ∧
      (∀ᶠ n in atTop, z n (m n) = F.inclusionD d * ray n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ R * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, β ((height (z n i)).toAdd) ≤ (β v₀ / 4) * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  let h₀ := cartanHeightSection T H (eW.symm v₀)
  let v := F.D.equiv h₀
  let u := chartD.symm d
  let η : G →* Multiplicative ℝ := β.toLinearMap.toAddMonoidHom.toMultiplicative.comp height
  let ℓ := β.toLinearMap.comp (eW.toLinearMap.comp
    ((heightProjection T.character).comp (H.subtype.comp F.D.equiv.symm.toLinearMap)))
  have hη (w) : (η (F.inclusionD (F.ExpD w))).toAdd = ℓ w := by
    change β ((height (F.inclusionD (F.ExpD w))).toAdd) = _
    have he := F.compatibleD (F.D.equiv.symm w)
    rw [F.D.equiv.apply_symm_apply] at he
    rw [he, hheight]
    rfl
  have hℓv : ℓ v = β v₀ := by simp [ℓ, v, h₀]
  have hnil := F.D.tangent_nilpotent (inferInstance : LieRing.IsNilpotent H)
  obtain ⟨q, hq⟩ := (LieModule.isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨C, R, hC, hR, hsource, hpaths⟩ := exists_nilpotent_negative_paths
    F.inclusionD F.closedD.continuous dynkinD F.ExpD F.isExpD chartD hchartD hq
    (finBasis ℝ _) η ℓ hη u v (by rwa [hℓv])
  have hscalar (x y : G) : |(η x).toAdd - (η y).toAdd| ≤ (‖β‖ * Kheight) * dist x y := by
    change |β ((height x).toAdd) - β ((height y).toAdd)| ≤ _
    calc
      _ = ‖β ((height x).toAdd - (height y).toAdd)‖ := by rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖β‖ * ‖(height x).toAdd - (height y).toAdd‖ := β.le_opNorm _
      _ ≤ ‖β‖ * (Kheight * dist x y) := mul_le_mul_of_nonneg_left (hLip x y) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨B, hB, m, z, hz0, hzend, hcount, hnegative, hball, hsteps⟩ :=
    polynomial_negative_path_chains hpath (fun g => (η g).toAdd)
      (mul_nonneg (norm_nonneg _) hKheight) hC hR
      (show 0 < -ℓ v / 2 by rw [hℓv]; linarith) hscalar
      (fun n => F.inclusionD (F.ExpD ((n : ℝ) • v)))
      (fun n => F.inclusionD (F.ExpD u) * F.inclusionD (F.ExpD ((n : ℝ) • v)))
      hsource (hpaths.mono fun n hn => by
        obtain ⟨γ, hm, hh, hr⟩ := hn
        exact ⟨γ, hm, fun t => by have ht := hh t; linarith, hr⟩)
  have hbase (n : ℕ) : F.inclusionD (F.ExpD ((n : ℝ) • v)) =
      ExpG ((n : ℝ) • (h₀ : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    change F.inclusionD (F.ExpD ((n : ℝ) • F.D.equiv h₀)) = _
    rw [← map_smul, F.compatibleD]
    rfl
  have hend : F.ExpD u = d := by
    change F.ExpD (chartD.symm d) = d
    rw [← hchartD, chartD.apply_symm_apply]
  refine ⟨q, B, hB, m, z, fun n => (hz0 n).trans (hbase n), ?_, hcount, ?_, hball, hsteps⟩
  · filter_upwards [hzend] with n hn
    exact hn.trans (congrArg₂ (fun x y => F.inclusionD x * y) hend (hbase n))
  · filter_upwards [hnegative] with n hn
    intro i hi
    have hh := hn i hi
    change β ((height (z n i)).toAdd) ≤ _ at hh
    rw [hℓv] at hh
    linarith

end PolycyclicRecognition.CartanFactorModel

end

end OAI
