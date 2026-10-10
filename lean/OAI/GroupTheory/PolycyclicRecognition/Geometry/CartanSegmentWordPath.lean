import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentVisits
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParametrizedGeneratorSchemes

namespace OAI

/-! # Specified segment paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed segment visits. This retains both measurable samples and the
uniform metric bounds needed for endpoint integration.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

def segmentScaledWord (v : H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    List (Fin M.letterCount × ℝ) :=
  u.map (fun z => (z.1, z.2 * Real.exp (r * M.segmentSupportExponent v z.1)))

def segmentWordPath (v : H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    Path (1 : G) ((M.segmentScaledWord v r u).map
      (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  exact (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.segmentScaledWord v r u) 1).cast
    (by simp) (by simp [indexedWordProduct, f])

/-- Fixed-time samples remain continuous when the amplitudes of a fixed
combinatorial word vary continuously. -/
theorem continuous_segmentWordPath_sample
    {Y : Type*} [TopologicalSpace Y]
    (v : H) (r : ℝ) (w : List (Fin M.letterCount × (Y → ℝ)))
    (hw : ∀ z ∈ w, Continuous z.2) (t : unitInterval) :
    Continuous (fun y => M.segmentWordPath T hExp realize v r
      (w.map (fun z => (z.1, z.2 y))) t) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let w' := w.map (fun z => (z.1, fun y => z.2 y * Real.exp (r * M.segmentSupportExponent v z.1)))
  have hw' : ∀ z ∈ w', Continuous z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact (hw q hq).mul_const _
  have hh := continuous_supportWordPath_sample d f hd hf hd₀ hf₀ 1 r w' hw'
    (fun _ : Y => (1 : G)) continuous_const t
  change Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
    (M.segmentScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t)
  have he : (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
      (M.segmentScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t) =
      (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
        (w'.map (fun z => (z.1, z.2 y))) 1 t) := by
    funext y
    apply congrArg (fun u => supportWordPath d f hd hf hd₀ hf₀ 1 r u 1 t)
    simp only [segmentScaledWord, w', List.map_map, Function.comp_def]
  rw [he]
  exact hh

/-- Uniform metric and homomorphism-height bounds for the specified paths. -/
theorem exists_segmentWordPath_bound [IsIsometricSMul G G]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : H) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N → (∀ z ∈ u, |z.2| ≤ B) →
      PathMetricBound (M.segmentWordPath T hExp realize v r u)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
        (l (M.segmentWordPath T hExp realize v r u t)).toAdd = r • z := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨C, hC, hvisit⟩ := M.exists_segment_support_visit_bound T hExp realize l hl hL hbound v hB
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr u hu hub
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let P i b := |b| ≤ B * Real.exp (r * M.segmentSupportExponent v i)
  let S : Set G := {g | ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd, (l g).toAdd = r • z}
  have hbase n (hn : l n = 1) : n * 1 ∈ S := by
    exact ⟨0, left_mem_segment ℝ _ _, by simp [hn]⟩
  have hstep n (hn : l n = 1) i b (hb : P i b) :
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n 1 r b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n 1 r b t ∈ S := by
    obtain ⟨γ, hγ, hheight, he⟩ := hvisit r hr n hn i b hb
    subst γ
    exact ⟨hγ, hheight⟩
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  have hscaled : ∀ z ∈ M.segmentScaledWord v r u, P z.1 z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    dsimp [P]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hub q hq) (Real.exp_pos _).le
  obtain ⟨hb, hh⟩ := supportWordPath_bound d f hd hf hd₀ hf₀ 1 r l P
    (fun i b _ => M.hom_eq_one_on_letter T hExp realize l hl hL hbound i b)
    hbase (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep
    (M.segmentScaledWord v r u) hscaled 1 (map_one l)
  have hp : (2 : ℝ) ^ (M.segmentScaledWord v r u).length ≤ 2 ^ N := by
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [segmentScaledWord, List.length_map] using hu
  have hb' := hb.mono
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  constructor
  · change PathMetricBound
      (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.segmentScaledWord v r u) 1)
      ((C * 2 ^ N) * r) ((C * 2 ^ N) * (1 + Real.log (2 + r)))
    convert hb' using 1 <;> ring
  · exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
