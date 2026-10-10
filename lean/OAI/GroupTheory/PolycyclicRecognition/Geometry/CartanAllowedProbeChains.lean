import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTranslatedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactSupportSlack
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBoxComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportOrder

namespace OAI

/-! # Placing actual probe chains in the sampling coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Reexpress an actual probe chain in the enlarged sampling basis.
The word-basis comparison gives a constant radius for every prefix;
all endpoints, coefficients and generator edges are preserved. -/
def BoxProbeChains.inSamplingBox
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E C : Set W) (γ β : M.Bases) (t : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW C) β.val)
    (ht : ∀ i, t i ≤ (M.supportIn T hunimod eW).weightSupport C i)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport C i)
    {δ : ℝ} (hδ : 0 ≤ δ) (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe) :
    M.BoxProbeChains T F hunimod eW b₀ E β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) scale probe := by
  let hex := exists_word_box_comparison_constant M.letter M.wordList b₀
  let D := Classical.choose hex
  have hD := (Classical.choose_spec hex).1
  have hcompare := (Classical.choose_spec hex).2
  have hscaled : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro β' hβ'
    simp only [columnBasisWeight, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 β' hβ') (by linarith)
  have hcost (w : M.wordList) : bracketWordExponent t w ≤
      bracketWordExponent
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w + 0 := by
    rw [add_zero]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hmul := mul_nonneg hδ (hw i)
    nlinarith [ht i]
  refine {
    length := P.length
    amplitude := P.amplitude
    prefixRadius := D * P.prefixRadius
    amplitude_ge_one := P.amplitude_ge_one
    prefixRadius_nonneg := mul_nonneg hD P.prefixRadius_nonneg
    mode := P.mode
    coefficient := P.coefficient
    vertex := P.vertex
    coefficient_measurable := P.coefficient_measurable
    vertex_measurable := P.vertex_measurable
    coefficient_bound := P.coefficient_bound
    vertex_zero := P.vertex_zero
    vertex_last := P.vertex_last
    vertex_step := P.vertex_step
    vertex_bound := ?_ }
  intro n y j
  have hb := hcompare
    (fun w => bracketWordExponent
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport C i) w)
    (fun w => bracketWordExponent t w) β γ hscaled (hr n) hcost (P.vertex n y j)
  simp only [zero_mul, Real.exp_zero, mul_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (P.vertex_bound n y j) hD)

omit [SimplyConnectedSpace G] in
/-- Compact containment of the generator template supplies the strict
switching heights in the actual Cartan profile coordinates. -/
theorem exists_probe_switch_height
    {J : Type*} [Fintype J]
    (bD : Basis J ℝ H) (E U : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hU : IsOpen U) (hEU : E ⊆ U) (i : Fin M.letterCount) :
    ∃ z : J → ℝ,
      eW (heightProjection T.character (bD.equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ U ∧
      (M.supportIn T hunimod eW).weightSupport E i < M.weight i (bD.equivFun.symm z) := by
  obtain ⟨h, hh, hs⟩ := M.exists_cartan_height_above_compact_support T hunimod eW
    E U hE hne hU hEU i
  exact ⟨bD.equivFun h, by simpa only [LinearEquiv.symm_apply_apply] using hh,
    by simpa only [LinearEquiv.symm_apply_apply] using hs⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
