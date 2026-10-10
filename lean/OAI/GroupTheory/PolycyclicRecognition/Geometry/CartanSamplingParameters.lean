import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarProbeTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightSamplingSupport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeSamplingTemplate

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual normalized halfspaces used to sample the root ideal. -/
def samplingPolytope : Set W :=
  weightSamplingPolytope (fun i => ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)

theorem sampling_weight_ne_zero (i : Fin M.letterCount) :
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ≠ 0 := by
  intro hz
  apply M.weight_nonzero i
  funext h
  have he := congrArg (fun f : W →L[ℝ] ℝ =>
    f (eW (heightProjection T.character (h : L)))) hz
  simpa [supportIn, SupportDatum.transport, supportDatum_weight,
    cartanHeightWeight_projection] using he

theorem isCompact_samplingPolytope : IsCompact (M.samplingPolytope T hunimod eW) := by
  exact (M.supportIn T hunimod eW).isCompact_weightSamplingPolytope (Classical.arbitrary M.Bases)

theorem sampling_weightSupport_eq (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i =
      ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖ :=
  weightSampling_support_eq_norm _ (M.isCompact_samplingPolytope T hunimod eW)
    i (M.sampling_weight_ne_zero T hunimod eW i)

theorem sampling_weightSupport_pos (i : Fin M.letterCount) :
    0 < (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i := by
  rw [M.sampling_weightSupport_eq T hunimod eW i]
  exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)

/-- The finite word list supplies positive lower and upper widths and a
strict concentration gap. These constants are chosen from the actual
sampling polytope rather than assumed as geometric inputs. -/
theorem exists_sampling_gap [Nonempty (Fin M.letterCount)] :
    ∃ lo hi c : ℝ, 0 < lo ∧ 0 < hi ∧ 0 < c ∧
      (∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW
        (M.samplingPolytope T hunimod eW) w ∧
        M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW) w ≤ hi) ∧
      (M.bound : ℝ) * hi < c * lo := by
  classical
  let cost := M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)
  have hcost (w : M.wordList) : 0 < cost w :=
    bracketWordExponent_pos _ (M.sampling_weightSupport_pos T hunimod eW) w
  have hne : (Finset.univ : Finset M.wordList).Nonempty := by
    let i : Fin M.letterCount := Classical.arbitrary _
    have hi : FreeMagma.of i ∈ M.wordList := by
      apply M.mem_wordList_of_eval_ne_zero
      simp only [evalBracketWord_of]
      intro hz
      have hq := M.letter_quotient i
      rw [hz, map_zero] at hq
      exact M.abelianBasis.ne_zero i hq.symm
    exact ⟨⟨FreeMagma.of i, hi⟩, Finset.mem_univ _⟩
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ cost hne
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ cost hne
  let c := ((M.bound : ℝ) * cost v + 1) / cost u
  have hc : 0 < c := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) (hcost v).le) zero_lt_one)
    (hcost u)
  refine ⟨cost u, cost v, c, hcost u, hcost v, hc,
    fun w => ⟨hu w (Finset.mem_univ w), hv w (Finset.mem_univ w)⟩, ?_⟩
  dsimp only [c]
  rw [div_mul_cancel₀ _ (hcost u).ne']
  linarith

end PolycyclicRecognition.CartanWordModel

namespace PolycyclicRecognition

open Set

/-- Source, reverse anchor, and within-tile radii, in that order. -/
def threePolarRadii (ε : ℝ) : Fin 3 → ℝ := ![2 * ε / 3, ε, ε / 3]

/-- The exact translated templates used by the three probe chains. -/
def polarSamplingTemplates {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (W →L[ℝ] ℝ)) (ε : ℝ) (w : W) (k : Fin 3) : Set W :=
  (fun x => x + w) '' ((fun z => threePolarRadii ε k • z) '' conePolarTemplate K)

/-- The open profile-height domain retains the strict facet inequalities. -/
def samplingHeightDomain {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (a : ℝ) : Set W := {w | ∀ i, α i w < a * ‖α i‖}

/-- All three radii and the contact point can be fixed before choosing
the chart enlargement. Every translated template has strict facet slack. -/
theorem exists_three_polar_sampling_templates
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0)
    (i₀ : I) (K : ProperCone ℝ (W →L[ℝ] ℝ)) (hK : α i₀ ∈ K)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ (p : W) (ε δ₀ : ℝ), α i₀ p = ‖α i₀‖ ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < threePolarRadii ε 2 ∧ threePolarRadii ε 2 < threePolarRadii ε 0 ∧
      threePolarRadii ε 0 < threePolarRadii ε 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        0 < 1 - (c + 1) * δ ∧
        ∀ k : Fin 3, ∀ z ∈ conePolarTemplate K, ∀ i,
          α i ((1 - (c + 1) * δ) • p + threePolarRadii ε k • z) <
            (1 - c * δ) * ‖α i‖ := by
  obtain ⟨p, ε, δ₁, hp, hε, hδ₁, hinside⟩ :=
    exists_polar_template_facet_slack α hne i₀ K hK hc (by linarith : c < c + 1)
  let δ₀ := min δ₁ (1 / (2 * (c + 2)))
  have hδ₀ : 0 < δ₀ := lt_min hδ₁ (by positivity)
  refine ⟨p, ε, δ₀, hp, hε, hδ₀, by dsimp [threePolarRadii]; positivity,
    by dsimp [threePolarRadii]; linarith, by dsimp [threePolarRadii]; linarith, ?_⟩
  intro δ hδ hd
  have hbound : δ ≤ 1 / (2 * (c + 2)) := hd.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (c + 2))).mp hbound
  refine ⟨by nlinarith, ?_⟩
  intro k z hz i
  have hrad : 0 ≤ threePolarRadii ε k ∧ threePolarRadii ε k ≤ ε := by
    fin_cases k <;> dsimp [threePolarRadii] <;> constructor <;> linarith
  exact hinside δ hδ (hd.trans (min_le_left _ _)) _ hrad.1 hrad.2 z hz i

/-- The facet inequalities give precisely the compact, convex templates
inside one open convex profile domain required by both path construction
and raw concentration. The domain is also inside the original sampling
polytope, which supplies the common coordinate bound. -/
theorem polar_sampling_template_geometry
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (K : ProperCone ℝ (W →L[ℝ] ℝ))
    (p : W) (ε δ c : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hfactor : 0 < 1 - (c + 1) * δ)
    (hfacet : ∀ k : Fin 3, ∀ z ∈ conePolarTemplate K, ∀ i,
      α i ((1 - (c + 1) * δ) • p + threePolarRadii ε k • z) <
        (1 - c * δ) * ‖α i‖) :
    let w := (1 - (c + 1) * δ) • p
    let E := polarSamplingTemplates K ε w
    let V := samplingHeightDomain α (1 - c * δ)
    (∀ k, IsCompact (E k) ∧ Convex ℝ (E k) ∧ w ∈ E k ∧ E k ⊆ V) ∧
      IsOpen V ∧ Convex ℝ V ∧
      V ⊆ (fun y : W => (1 - c * δ) • y) '' interior (weightSamplingPolytope α) ∧
      V ⊆ weightSamplingPolytope α := by
  dsimp only
  let w := (1 - (c + 1) * δ) • p
  have hf : 0 < 1 - c * δ := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨((isCompact_conePolarTemplate K).image
      (continuous_const.smul continuous_id)).image (continuous_id.add_const w), ?_, ?_, ?_⟩
    · have hcv := ((convex_conePolarTemplate K).smul (threePolarRadii ε k)).translate w
      change Convex ℝ ((fun x => w + x) ''
        ((fun z => threePolarRadii ε k • z) '' conePolarTemplate K)) at hcv
      simpa only [polarSamplingTemplates, w, add_comm] using hcv
    · exact ⟨0, ⟨0, zero_mem_conePolarTemplate K, smul_zero _⟩, zero_add w⟩
    · rintro x ⟨u, ⟨z, hz, rfl⟩, rfl⟩ i
      simpa only [add_comm] using hfacet k z hz i
  · simp only [samplingHeightDomain, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (α i).continuous continuous_const)
  · simp only [samplingHeightDomain, Set.ofPred_forall]
    exact convex_iInter (fun i => convex_halfSpace_lt (α i).toLinearMap.isLinear _)
  · intro x hx
    exact mem_smul_weightSamplingInterior α hf x hx
  · intro x hx i
    have hle : (1 - c * δ) * ‖α i‖ ≤ ‖α i‖ := by
      nlinarith [norm_nonneg (α i), mul_nonneg hc hδ.le]
    exact (hx i).le.trans hle

end PolycyclicRecognition

end

end OAI
