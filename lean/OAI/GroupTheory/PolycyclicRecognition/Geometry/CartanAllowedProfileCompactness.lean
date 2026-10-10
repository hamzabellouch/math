import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDependentProfileCompactness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileAnchors

namespace OAI

/-! # Compact containment for all allowed sheet suffixes -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G I W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- After deleting finitely many scales, one compact profile family
contains every sample and every allowed suffix in the enlarged word box.
The only suffix assumption is its vanishing coordinate-error envelope. -/
theorem exists_compact_allowed_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (bN₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s t : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (βN γN : M.Bases)
    (hβN : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN₀)
      (fun w => bracketWordExponent s w) βN.val)
    (hγN : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN₀)
      (fun w => bracketWordExponent t w) γN.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n)) (x : ℕ → G) :
    ∃ n₀ : ℕ, ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∀ n y v,
      ‖y‖ ≤ 1 →
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γN)
        (fun j => bracketWordExponent t (γN.val j)) (scale (n + n₀))).equivFun v‖ ≤
          Real.exp (scale (n + n₀) * ε (n + n₀)) →
      ∃ f ∈ S, ∀ z, f z =
        rescaledMapProfile (J (n + n₀)) (x (n + n₀))
          (F.inclusionN (F.ExpN (F.N.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList βN)
              (fun j => bracketWordExponent s (βN.val j)) (scale (n + n₀))).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv v)))
          (max (Real.log (scale (n + n₀))) 0)
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
              (max (Real.log (scale (n + n₀))) 0)).equivFun.symm z)))) z := by
  classical
  obtain ⟨B, lo, _, hlo, hanchor⟩ := exists_bounded_box_profile_anchors T M F
    hExpG realize haarN dynkinN bN₀ s t hs ht
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hlo))
  let r := fun n => scale (n + n₀)
  let δ := fun n => max (Real.log (r n)) 0
  have hr (n : ℕ) : 1 ≤ r n := hscale1 _
  have hrpos (n : ℕ) : 0 < r n := lt_of_lt_of_le zero_lt_one (hr n)
  have hδ (n : ℕ) : δ n = Real.log (r n) := max_eq_left (Real.log_nonneg (hr n))
  have hexp (n : ℕ) : Real.exp (δ n) = r n := by rw [hδ, Real.exp_log (hrpos n)]
  have hδlim : Tendsto δ atTop atTop := by
    exact tendsto_atTop_mono (fun n => le_max_left _ _)
      (Real.tendsto_log_atTop.comp (hscale.comp (tendsto_add_atTop_nat n₀)))
  let A := fun n => {yv : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × cartanRootIdeal H |
    ‖yv.1‖ ≤ 1 ∧
    ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γN)
      (fun j => bracketWordExponent t (γN.val j)) (r n)).equivFun yv.2‖ ≤
        Real.exp (r n * ε (n + n₀))}
  let : ∀ n, Nonempty (A n) := fun n => ⟨⟨(0, 0), by
    change ‖(0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)‖ ≤ 1 ∧
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γN)
        (fun j => bracketWordExponent t (γN.val j)) (r n)).equivFun
          (0 : cartanRootIdeal H)‖ ≤ Real.exp (r n * ε (n + n₀))
    simpa only [norm_zero, map_zero] using And.intro zero_le_one (Real.exp_pos _).le⟩⟩
  let suffix := fun n (yv : A n) => F.inclusionN
    (F.ExpN (F.N.equiv ((exponentialRescaleBasis
      (WordBasisSelections.basis M.letter M.wordList βN)
      (fun j => bracketWordExponent s (βN.val j)) (r n)).equivFun.symm yv.val.1)) *
      F.ExpN (F.N.equiv yv.val.2))
  have hsuffix (n : ℕ) (yv : A n) : dist 1 (suffix n yv) / Real.exp (δ n) ≤ B := by
    rw [hexp]
    apply hanchor βN γN hβN hγN (r n) (ε (n + n₀)) (hr n)
      (hn₀ (n + n₀) (Nat.le_add_left n₀ n)).le
    · exact ⟨_, rfl, by simpa only [LinearEquiv.apply_symm_apply] using yv.property.1⟩
    · exact ⟨_, rfl, yv.property.2⟩
  obtain ⟨S, hS, hmem⟩ := exists_compact_dependent_cartan_profiles T F hExpG realize
    haarD dynkinD X hk hletters b₀ β hβ δ hδlim (fun _ => le_max_right _ _)
    (fun n (_ : A n) => J (n + n₀)) (fun n _ => hJ (n + n₀))
    (fun n _ => x (n + n₀)) suffix B hsuffix
  refine ⟨n₀, S, hS, ?_⟩
  intro n y v hy hv
  have hm := hmem n (⟨(y, v), hy, hv⟩ : A n)
  simpa only [suffix, map_mul, r, δ] using hm

end PolycyclicRecognition

end

end OAI
