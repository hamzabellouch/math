import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FixedWeightContact

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

/-- Canonical-section lifts of the Euclidean contact points satisfy the
root-neighbor affinity hypotheses simultaneously for all generators. -/
theorem exists_sampling_contact_pivots :
    ∃ pivot : Fin M.letterCount → H, ∀ i,
      cartanHeightSection T H (heightProjection T.character (pivot i : L)) = pivot i ∧
      ‖eW (heightProjection T.character (pivot i : L))‖ = 1 ∧
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
        (eW (heightProjection T.character (pivot i : L))) =
          ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖ ∧
      0 < M.weight i (pivot i) ∧
      eW (heightProjection T.character (pivot i : L)) ∈ M.samplingPolytope T hunimod eW ∧
      ∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
          (eW (heightProjection T.character (pivot i : L))) =
            ‖((M.supportIn T hunimod eW).weight j).toContinuousLinearMap‖ →
        ∃ t : ℝ, 0 < t ∧ ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap =
          t • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap := by
  classical
  let α := fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
  choose p hpn hpa hstrict using fun i =>
    exists_weight_contact_point (α i) (M.sampling_weight_ne_zero T hunimod eW i)
  let pivot := fun i => cartanHeightSection T H (eW.symm (p i))
  have hheight (i) : eW (heightProjection T.character (pivot i : L)) = p i := by
    simp only [pivot, cartanHeightSection_height, eW.apply_symm_apply]
  refine ⟨pivot, fun i => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [pivot, cartanHeightSection_height]
  · rw [hheight]; exact hpn i
  · rw [hheight]; exact hpa i
  · have he : M.weight i (pivot i) = α i (p i) := rfl
    rw [he, hpa]
    exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)
  · change ∀ j, α j (eW (heightProjection T.character (pivot i : L))) ≤ ‖α j‖
    rw [hheight]
    intro j
    calc
      α j (p i) ≤ |α j (p i)| := le_abs_self _
      _ ≤ ‖α j‖ * ‖p i‖ := (α j).le_opNorm _
      _ = ‖α j‖ := by rw [hpn, mul_one]
  · intro j hj
    rw [hheight] at hj
    by_contra hn
    exact (ne_of_lt (hstrict i (α j) (M.sampling_weight_ne_zero T hunimod eW j) hn)) hj

/-- All cone tests for one root use the same unit contact point. Only the
positive template radius and enlargement threshold depend on the cone. -/
theorem exists_fixed_polar_sampling_geometry
    (i : Fin M.letterCount) (p : W) (hp : ‖p‖ = 1)
    (hpi : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap p =
      ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hi : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ (ε₀ δ₀ : ℝ), 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        let w := (1 - (c + 1) * δ) • p
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
  obtain ⟨ε₀, δ₁, hε₀, hd₁, hinside⟩ :=
    exists_polar_template_facet_slack_at α (M.sampling_weight_ne_zero T hunimod eW)
      i p hp hpi K hi hc (by linarith : c < c + 1)
  let δ₀ := min δ₁ (1 / (2 * (c + 2)))
  have hd₀ : 0 < δ₀ := lt_min hd₁ (by positivity)
  refine ⟨ε₀, δ₀, hε₀, hd₀, ?_⟩
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
  exact ⟨hfactor, polar_sampling_template_geometry α K p ε δ c hc hδ hfactor hfacets⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
