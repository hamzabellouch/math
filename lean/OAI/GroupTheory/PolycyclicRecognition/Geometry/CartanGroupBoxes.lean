import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Actual group boxes for the Cartan word model

The finite Cartan construction supplies the bases, bracket bounds, nilpotence
and support exponents used here. The only external group facts are the two
explicit published exponential inputs. In particular no box multiplication or
volume estimate is an assumption.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual scaled word basis, selected before taking its exponential image. -/
def boxBasis (E : Set W) (β : M.Bases) (r : ℝ) :
    Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H) :=
  exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
    (fun i => M.boxCost T hunimod eW E (β.val i)) r

/-- A Cartan group box is the exponential image of its scaled coordinate cube. -/
def groupBox {G : Type*} (Exp : cartanRootIdeal H → G)
    (E : Set W) (β : M.Bases) (r R : ℝ) : Set G :=
  exponentialCoordinateBox Exp (M.boxBasis T hunimod eW E β r) R

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

include hExp

/-- A uniform product estimate for the actual Cartan boxes. No assumptions
about compactness or convexity of the template are needed for this part. -/
theorem exists_groupBox_product_bound
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → N,
      (∀ i, g i ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) →
      (List.ofFn g).prod ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
        (C * (1 + (n : ℝ)) ^ M.bound * (1 + R) ^ M.bound) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_word_box_product_bound dynkin eN Exp hExp
    M.letter M.bound_zero b₀
  exact ⟨C, hC, fun E β hβ r hr n R hR g hg =>
    hbound ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr n R hR g hg⟩

omit [T2Space N] in
/-- Inversion requires no extra group input beyond the intrinsic exponential. -/
theorem groupBox_inv_mem (E : Set W) (β : M.Bases) (r R : ℝ) {g : N}
    (hg : g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) :
    g⁻¹ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R :=
  inv_mem_exponentialCoordinateBox eN Exp hExp (M.boxBasis T hunimod eW E β r) hg

variable [SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]

/-- Exact Haar volume in a maximizing actual word basis. All scaling and
support factors have been derived from the Cartan model. -/
theorem exists_groupBox_haar_volume
    (haarInput : NilpotentExponentialHaarInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ μ : Measure N, μ.IsHaarMeasure ∧
      ∀ (E : Set W) (β : M.Bases),
      columnBasisWeight (M.boxCost T hunimod eW E) β.val =
        (M.supportIn T hunimod eW).templateSupport E →
      ∀ (r R : ℝ), 0 ≤ R →
        μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀)
            β.val).det| *
          ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) := (LieModule.isNilpotent_iff ℝ (cartanRootIdeal H) (cartanRootIdeal H)).mpr
    ⟨M.bound, M.bound_zero⟩
  obtain ⟨μ, hμ, hvol⟩ := exists_haar_measure_model_weighted_boxes haarInput Exp hExp eN
    hnil M.letter M.wordList b₀
  refine ⟨μ, hμ, ?_⟩
  intro E β hβ r R hR
  have hv := hvol (M.boxCost T hunimod eW E) β r R hR
  change μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) = _ at hv
  rw [hβ] at hv
  exact hv

/-- Uniform two-sided Haar estimates for all maximizing group boxes. -/
theorem exists_groupBox_haar_bounds
    (haarInput : NilpotentExponentialHaarInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (μ : Measure N) (c C : ℝ), μ.IsHaarMeasure ∧ 0 < c ∧ 0 < C ∧
      ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (r R : ℝ), 0 ≤ R →
        ENNReal.ofReal c *
          ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) ≤
            μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) ∧
        μ (M.groupBox T hunimod eW (Exp ∘ eN) E β r R) ≤
          ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  obtain ⟨μ, hμ, hvol⟩ := M.exists_groupBox_haar_volume T hunimod eW eN Exp hExp haarInput b₀
  obtain ⟨c, C, hc, hC, hdet⟩ := M.exists_uniform_wordBasis_determinant_bounds b₀
  refine ⟨μ, c, C, hμ, hc, hC, ?_⟩
  intro E β hβ r R hR
  rw [hvol E β (M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E β hβ)
    r R hR]
  constructor
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet β).1) le_rfl) le_rfl
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet β).2) le_rfl) le_rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
