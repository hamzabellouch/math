import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # Contact points and source templates in the actual Cartan height space -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The contact point has positive value on the chosen root. All three
translated templates lie in one open convex domain strictly inside the
shrunk sampling polytope. The inward contact uses `c + 1`, while the
concentration domain uses `c`. -/
theorem exists_polar_sampling_geometry
    (i : Fin M.letterCount) (K : ProperCone ℝ (StrongDual ℝ W))
    (hi : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ (pivot : H) (ε₀ δ₀ : ℝ),
      cartanHeightSection T H (heightProjection T.character (pivot : L)) = pivot ∧
      0 < M.weight i pivot ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        let w := (1 - (c + 1) * δ) • eW (heightProjection T.character (pivot : L))
        let E := polarSamplingTemplates K ε w
        let V := samplingHeightDomain
          (fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (1 - c * δ)
        0 < 1 - (c + 1) * δ ∧
        (∀ k, IsCompact (E k) ∧ Convex ℝ (E k) ∧ w ∈ E k ∧ E k ⊆ V) ∧
        IsOpen V ∧ Convex ℝ V ∧
        V ⊆ (fun y : W => (1 - c * δ) • y) '' interior (M.samplingPolytope T hunimod eW) ∧
        V ⊆ M.samplingPolytope T hunimod eW := by
  let α := fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
  obtain ⟨p, ε₀, δ₁, hp, hε₀, hd₁, hinside⟩ :=
    exists_polar_template_facet_slack α (M.sampling_weight_ne_zero T hunimod eW)
      i K hi hc (by linarith : c < c + 1)
  let δ₀ := min δ₁ (1 / (2 * (c + 2)))
  have hd₀ : 0 < δ₀ := lt_min hd₁ (by positivity)
  let pivot := cartanHeightSection T H (eW.symm p)
  have hpivot : eW (heightProjection T.character (pivot : L)) = p := by
    simp only [pivot, cartanHeightSection_height, eW.apply_symm_apply]
  have hroot : 0 < M.weight i pivot := by
    have he : M.weight i pivot = α i p := rfl
    rw [he, hp]
    exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)
  refine ⟨pivot, ε₀, δ₀, ?_, hroot, hε₀, hd₀, ?_⟩
  · simp only [pivot, cartanHeightSection_height]
  intro ε hε hεmax δ hδ hδ₀
  have hbound : δ ≤ 1 / (2 * (c + 2)) := hδ₀.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (c + 2))).mp hbound
  have hfactor : 0 < 1 - (c + 1) * δ := by nlinarith
  have hfacets : ∀ k : Fin 3, ∀ z ∈ conePolarTemplate K, ∀ j,
      α j ((1 - (c + 1) * δ) • p + threePolarRadii ε k • z) <
        (1 - c * δ) * ‖α j‖ := by
    intro k z hz j
    have hrad : 0 ≤ threePolarRadii ε k ∧ threePolarRadii ε k ≤ ε := by
      fin_cases k <;> dsimp [threePolarRadii] <;> constructor <;> linarith
    exact hinside δ hδ (hδ₀.trans (min_le_left _ _)) _ hrad.1
      (hrad.2.trans hεmax) z hz j
  dsimp only
  rw [hpivot]
  exact ⟨hfactor, polar_sampling_template_geometry α K p ε δ c hc hδ hfactor hfacets⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
