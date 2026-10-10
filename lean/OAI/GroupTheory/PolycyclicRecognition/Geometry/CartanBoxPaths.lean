import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportVisits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordSupportPaths

namespace OAI

/-! # Continuous controlled-height paths to the actual Cartan boxes

Uniform generation and support visits now combine without a path premise.
Every endpoint of a fixed-radius box is reached, on any allowed pivot, by
one continuous path with uniform coarse speed and logarithmic error.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The fixed-radius support-path conclusion for the actual box and its
actual inclusion in the ambient group. All geometric bounds are derived. -/
theorem exists_cartan_box_path_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hcE : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
    (R : ℝ) {A : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (h₀ : H),
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R,
      ∃ γ : Path (Exp h₀) (F.inclusionN n * Exp h₀),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        ∀ t, ∃ w ∈ E, (π (γ t)).toAdd = r • w := by
  classical
  let D := M.supportIn T hunimod eW
  let s := D.weightSupport E
  choose w hw hs using (fun i => D.exists_weightSupport_point hE ⟨w₀, hw₀⟩ i)
  have hs' i : cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i := (hs i).symm
  obtain ⟨N, B, hB, hgen⟩ := M.exists_uniform_cartan_rescaled_generator_words T F hExp
    realize haarN dynkinN b₀ R
  obtain ⟨C, hC, hvisit⟩ := M.exists_cartan_support_visit_bound T F eW hExp realize haarD
    dynkinD π hπ hcE hw₀ w hw s hs' hA (by linarith : 0 ≤ B) p
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr h₀ hh₀ hπ₀ β hβ n hn
  obtain ⟨v, hv, hnorm⟩ := hn
  obtain ⟨u, hu, hub, hue⟩ := hgen s β hβ r hr v hnorm
  let f (z : Fin M.letterCount × ℝ) : G :=
    Exp (z.2 • (Real.exp (r * s z.1) • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  let P (z : Fin M.letterCount × ℝ) : Prop := |z.2| ≤ B
  have hamp z (hz : P z) : |z.2 * Real.exp (r * s z.1)| ≤ B * Real.exp (r * s z.1) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
  have hπf z (_hz : P z) : π (f z) = 1 := by
    dsimp only [f]
    rw [smul_smul]
    exact cartan_letter_exp_height_eq_one T M Exp eW π hπ z.1 _
  let S : Set G := {g | ∃ w ∈ E, (π g).toAdd = r • w}
  have hbase m (hm : π m = 1) : m * Exp h₀ ∈ S := by
    refine ⟨w₀, hw₀, ?_⟩
    simpa only [map_mul, hm, one_mul] using hπ₀
  have hstep m (hm : π m = 1) z (hz : P z) :
      ∃ γ : Path (m * Exp h₀) (m * f z * Exp h₀),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧ ∀ t, γ t ∈ S := by
    obtain ⟨γ, hγ, hγS, _⟩ :=
      hvisit r hr h₀ hh₀ hπ₀ m hm z.1 (z.2 * Real.exp (r * s z.1)) (hamp z hz)
    have he : m * f z * Exp h₀ = m *
        Exp ((z.2 * Real.exp (r * s z.1)) •
          (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀ := by
      simp only [f, smul_smul]
    exact ⟨γ.cast rfl he, hγ.cast rfl he, hγS⟩
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨γ, hγ, hγS⟩ := exists_word_support_path π f P hπf (Exp h₀) hbase
    (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep u hub 1 (map_one π)
  have hprod : (u.map f).prod = F.inclusionN n := by
    rw [← hv]
    change (u.map f).prod = F.inclusionN (F.ExpN (F.N.equiv v))
    rw [← hue]
    unfold generatorGroupWord
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    dsimp only [Function.comp_apply, f]
    exact (F.compatibleN (z.2 • (Real.exp (r * s z.1) • M.letter z.1))).symm
  have hp : (2 : ℝ) ^ u.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hu
  have hγ' := hγ.mono
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  have hsource : Exp h₀ = 1 * Exp h₀ := (one_mul _).symm
  have htarget : F.inclusionN n * Exp h₀ = 1 * (u.map f).prod * Exp h₀ := by
    rw [one_mul, hprod]
  refine ⟨γ.cast hsource htarget, ?_, hγS⟩
  convert hγ'.cast hsource htarget using 1 <;> ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
