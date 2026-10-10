import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PublishedRootDistortion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentWordMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxRadius
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Linear ambient length of the exponentially large root-ideal boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold BigOperators

/-- An exponential factor inside a logarithm contributes at most its
exponent, uniformly for nonnegative scales. -/
theorem log_two_add_exp_le {A S r : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hr : 0 ≤ r) :
    Real.log (2 + A * Real.exp (r * S)) ≤ Real.log (2 + A) + r * S := by
  have he : 1 ≤ Real.exp (r * S) := Real.one_le_exp_iff.mpr (mul_nonneg hr hS)
  calc
    _ ≤ Real.log ((2 + A) * Real.exp (r * S)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Each exponentially rescaled root generator has ambient length linear
in the logarithmic scale, uniformly over a bounded range of weights. -/
theorem root_generators_linear_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    {B S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ (s : Fin M.letterCount → ℝ), (∀ i, s i ≤ S) →
      ∀ (i : Fin M.letterCount) (t : ℝ), |t| ≤ B →
      dist 1 (ExpG (t • (Real.exp (r * s i) •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) ≤ C * (1 + r) := by
  let v := fun i => (⟨M.letter i, M.letter_root i⟩ : rootSpace H (M.weight i))
  choose D hD hd using fun i => root_distortion_of_published_realization T H (M.weight i)
    (M.weight_nonzero i) ExpG hExpG realize
  let A := fun i => B * ‖(rootCoordinates H (M.weight i)) (v i)‖
  let C := fun i => D i * (Real.log (2 + A i) + S)
  have hA : ∀ i, 0 ≤ A i := fun i => mul_nonneg hB (norm_nonneg _)
  have hC : ∀ i, 0 ≤ C i := fun i => mul_nonneg (hD i).le
    (add_nonneg (Real.log_nonneg (by linarith [hA i])) hS)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro r hr s hs i t ht
  have harg : ‖(rootCoordinates H (M.weight i)) (t • (Real.exp (r * s i) • v i))‖ ≤
      A i * Real.exp (r * S) := by
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ B * (Real.exp (r * S) * ‖(rootCoordinates H (M.weight i)) (v i)‖) := by
        gcongr
        exact hs i
      _ = _ := by dsimp [A]; ring
  have hdist := hd i (t • (Real.exp (r * s i) • v i))
  have hstep : dist 1 (ExpG (t • (Real.exp (r * s i) •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) ≤ C i * (1 + r) := by
    apply hdist.trans
    calc
      _ ≤ D i * Real.log (2 + A i * Real.exp (r * S)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (hD i).le
      _ ≤ D i * (Real.log (2 + A i) + r * S) :=
        mul_le_mul_of_nonneg_left (log_two_add_exp_le (hA i) hS hr) (hD i).le
      _ ≤ C i * (1 + r) := by
        dsimp [C]
        have hlog : 0 ≤ Real.log (2 + A i) := Real.log_nonneg (by linarith [hA i])
        calc
          _ ≤ D i * ((Real.log (2 + A i) + S) * (1 + r)) :=
            mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hr hlog]) (hD i).le
          _ = _ := by ring
  exact hstep.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) (by linarith))

include T in
/-- Bounded normalized root-ideal coordinates give linear ambient length.
This is the anchor bound for chart profiles, even though the nilpotent
coordinates themselves grow exponentially. -/
theorem exists_cartan_n_chart_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) {S : ℝ} (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Fin M.letterCount → ℝ), (∀ i, s i ≤ S) →
      ∀ (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ R →
      dist 1 (F.inclusionN (F.ExpN (F.N.equiv v))) ≤ C * (1 + r) := by
  obtain ⟨N, B, hB, hgen⟩ := M.exists_uniform_cartan_rescaled_generator_words T F
    hExpG realize haarN dynkinN b₀ R
  obtain ⟨C, hC, hstep⟩ := root_generators_linear_metric_bound T M hExpG realize
    (le_trans zero_le_one hB) hS
  refine ⟨(N : ℝ) * C, by positivity, ?_⟩
  intro s hs β hβ r hr v hv
  obtain ⟨u, hu, hub, hue⟩ := hgen s β hβ r hr v hv
  let E : cartanRootIdeal H → G := fun v => F.inclusionN (F.ExpN (F.N.equiv v))
  have he : generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i) E u = E v := by
    simpa only [E, generatorGroupWord, map_list_prod, List.map_map, Function.comp_def] using
      congrArg F.inclusionN hue
  change dist 1 (E v) ≤ _
  rw [← he]
  calc
    _ ≤ (u.length : ℝ) * (C * (1 + r)) :=
      dist_generatorGroupWord_le _ E u hub (fun i t ht => by
        simpa [E, F.compatibleN] using hstep r hr s hs i t ht)
    _ ≤ (N : ℝ) * (C * (1 + r)) := by gcongr
    _ = _ := by ring

include T in
/-- The same linear bound allows subexponential enlargement of the box
radius. Only the fixed positive lower word cost is needed. -/
theorem exists_cartan_n_expanded_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ C lo : ℝ, 0 ≤ C ∧ 0 < lo ∧ ∀ (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r ε : ℝ, 0 ≤ r → ε ≤ lo → ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ Real.exp (r * ε) →
      dist 1 (F.inclusionN (F.ExpN (F.N.equiv v))) ≤ C * (1 + r) := by
  obtain ⟨lo, hi, hlo, _, hword⟩ := exists_positive_wordExponent_bounds s hs M.wordList
  let S := ∑ i, s i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hs i).le)
  have hsi (i : Fin M.letterCount) : s i ≤ S :=
    Finset.single_le_sum (fun j _ => (hs j).le) (Finset.mem_univ i)
  obtain ⟨C, hC, hm⟩ := exists_cartan_n_chart_metric_bound T M F hExpG realize haarN dynkinN
    b₀ 1 hS
  refine ⟨2 * C, lo, by positivity, hlo, ?_⟩
  intro β hβ r ε hr hε v hv
  have hn := norm_double_scale_le_one (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => bracketWordExponent s (β.val j)) hr
    (fun j => hε.trans (hword (β.val j)).1) v hv
  exact (hm s hsi β hβ (2 * r) (by positivity) v hn).trans (by nlinarith)

end PolycyclicRecognition

end

end OAI
