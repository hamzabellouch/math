import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentVisits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordSupportPaths

namespace OAI

/-! # Paths to segment boxes before height factorization

Every point of the actual box determined by a Cartan segment is reached by
a controlled path. Under an arbitrary linearly bounded homomorphism, that
path stays over the corresponding target segment. No factorization through
canonical height is required.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- Actual segment-box reachability with control under the homomorphism
that will be constrained by stationary volume comparison. -/
theorem exists_segment_box_path_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : H) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.segmentSupportExponent v) w) β.val →
      ∀ n ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent (M.segmentSupportExponent v) (β.val j)) r) R,
      ∃ γ : Path (1 : G) (F.inclusionN n),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        ∀ t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd, (l (γ t)).toAdd = r • z := by
  obtain ⟨N, B, hB, hgen⟩ := M.exists_uniform_cartan_rescaled_generator_words T F hExp
    realize haarN dynkinN b₀ R
  obtain ⟨C, hC, hvisit⟩ := M.exists_segment_support_visit_bound T hExp realize l hl hL hbound
    v (by linarith : 0 ≤ B)
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr β hβ n hn
  obtain ⟨x, hx, hnorm⟩ := hn
  obtain ⟨u, hu, hub, hue⟩ := hgen (M.segmentSupportExponent v) β hβ r hr x hnorm
  let f (z : Fin M.letterCount × ℝ) : G :=
    Exp (z.2 • (Real.exp (r * M.segmentSupportExponent v z.1) •
      (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  let P (z : Fin M.letterCount × ℝ) : Prop := |z.2| ≤ B
  have hamp z (hz : P z) :
      |z.2 * Real.exp (r * M.segmentSupportExponent v z.1)| ≤
        B * Real.exp (r * M.segmentSupportExponent v z.1) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
  have hlf z (_hz : P z) : l (f z) = 1 := by
    dsimp only [f]
    rw [smul_smul]
    exact M.hom_eq_one_on_letter T hExp realize l hl hL hbound z.1 _
  let S : Set G := {g | ∃ w ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
    (l g).toAdd = r • w}
  have hbase m (hm : l m = 1) : m * 1 ∈ S := by
    refine ⟨0, left_mem_segment ℝ _ _, ?_⟩
    simp [hm]
  have hstep m (hm : l m = 1) z (hz : P z) :
      ∃ γ : Path (m * 1) (m * f z * 1),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧ ∀ t, γ t ∈ S := by
    obtain ⟨γ, hγ, hγS, _⟩ := hvisit r hr m hm z.1
      (z.2 * Real.exp (r * M.segmentSupportExponent v z.1)) (hamp z hz)
    have he : m * f z * 1 = m *
        Exp ((z.2 * Real.exp (r * M.segmentSupportExponent v z.1)) •
          (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1 := by
      simp only [f, smul_smul]
    exact ⟨γ.cast rfl he, hγ.cast rfl he, hγS⟩
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨γ, hγ, hγS⟩ := exists_word_support_path l f P hlf 1 hbase
    (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep u hub 1 (map_one l)
  have hprod : (u.map f).prod = F.inclusionN n := by
    rw [← hx]
    change (u.map f).prod = F.inclusionN (F.ExpN (F.N.equiv x))
    rw [← hue]
    unfold generatorGroupWord
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    dsimp only [Function.comp_apply, f]
    exact (F.compatibleN (z.2 • (Real.exp (r * M.segmentSupportExponent v z.1) •
      M.letter z.1))).symm
  have hp : (2 : ℝ) ^ u.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hu
  have hγ' := hγ.mono
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  have hsource : (1 : G) = 1 * 1 := by simp
  have htarget : F.inclusionN n = 1 * (u.map f).prod * 1 := by rw [one_mul, mul_one, hprod]
  refine ⟨γ.cast hsource htarget, ?_, hγS⟩
  convert hγ'.cast hsource htarget using 1 <;> ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
