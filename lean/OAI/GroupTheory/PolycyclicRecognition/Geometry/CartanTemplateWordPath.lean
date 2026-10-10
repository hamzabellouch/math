import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateVisits
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParametrizedGeneratorSchemes

namespace OAI

/-! # Specified template paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed template visits. This retains both measurable samples and the
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

def templateScaledWord (v : Fin M.letterCount → H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    List (Fin M.letterCount × ℝ) :=
  u.map (fun z => (z.1, z.2 * Real.exp (r * M.weight z.1 (v z.1))))

def templateWordPath (v : Fin M.letterCount → H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    Path (1 : G) ((M.templateScaledWord v r u).map
      (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  exact (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.templateScaledWord v r u) 1).cast
    (by simp) (by simp [indexedWordProduct, f])

/-- Fixed-time samples remain continuous when the amplitudes of a fixed
combinatorial word vary continuously. -/
theorem continuous_templateWordPath_sample
    {Y : Type*} [TopologicalSpace Y]
    (v : Fin M.letterCount → H) (r : ℝ) (w : List (Fin M.letterCount × (Y → ℝ)))
    (hw : ∀ z ∈ w, Continuous z.2) (t : unitInterval) :
    Continuous (fun y => M.templateWordPath T hExp realize v r
      (w.map (fun z => (z.1, z.2 y))) t) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let w' := w.map (fun z => (z.1, fun y => z.2 y * Real.exp (r * M.weight z.1 (v z.1))))
  have hw' : ∀ z ∈ w', Continuous z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact (hw q hq).mul_const _
  have hh := continuous_supportWordPath_sample d f hd hf hd₀ hf₀ 1 r w' hw'
    (fun _ : Y => (1 : G)) continuous_const t
  change Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
    (M.templateScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t)
  have he : (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
      (M.templateScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t) =
      (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
        (w'.map (fun z => (z.1, z.2 y))) 1 t) := by
    funext y
    apply congrArg (fun u => supportWordPath d f hd hf hd₀ hf₀ 1 r u 1 t)
    simp only [templateScaledWord, w', List.map_map, Function.comp_def]
  rw [he]
  exact hh

/-- Continuous parameters in a fixed conjugate scheme give continuous
samples of the prescribed template path. -/
theorem continuous_templateWordPath_scheme
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (v : Fin M.letterCount → H) (r : ℝ)
    (w : Fin n → List (Fin M.letterCount × ℝ)) (i : Fin n → Fin M.letterCount)
    (σ : Y → Fin n → ℝ) (hσ : Continuous σ) (t : unitInterval) :
    Continuous (fun y => M.templateWordPath T hExp realize v r
      (generatorSchemeWord w i (σ y)) t) := by
  have hc := M.continuous_templateWordPath_sample T hExp realize v r
    (parameterGeneratorSchemeWord w i σ)
    (parameterGeneratorSchemeWord_continuous w i σ hσ) t
  convert hc using 1
  funext y
  exact congrArg (fun z => M.templateWordPath T hExp realize v r z t)
    (parameterGeneratorSchemeWord_eval w i σ y).symm

omit [SimplyConnectedSpace G] in
/-- Inclusion carries the actual rescaled template word to its ambient
product, preserving every letter in the original order. -/
theorem templateScaledWord_product (F : CartanFactorModel H Exp)
    (v : Fin M.letterCount → H) (r : ℝ) (z : List (Fin M.letterCount × ℝ)) :
    ((M.templateScaledWord v r z).map
      (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod =
    F.inclusionN (generatorGroupWord
      (fun j => Real.exp (r * M.weight j (v j)) • M.letter j) (F.ExpN ∘ F.N.equiv) z) := by
  simp only [templateScaledWord, List.map_map, generatorGroupWord, map_list_prod]
  apply congrArg List.prod
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_apply]
  rw [F.compatibleN]
  simp only [SetLike.val_smul, smul_smul]

/-- Uniform metric and homomorphism-height bounds for the specified paths. -/
theorem exists_templateWordPath_bound [IsIsometricSMul G G]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : Fin M.letterCount → H) (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N → (∀ z ∈ u, |z.2| ≤ B) →
      PathMetricBound (M.templateWordPath T hExp realize v r u)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, ∃ z ∈ E,
        (l (M.templateWordPath T hExp realize v r u t)).toAdd = r • z := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨C, hC, hvisit⟩ := M.exists_template_support_visit_bound T hExp realize l hl hL hbound v E hE hE0 hvE hB
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr u hu hub
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let P i b := |b| ≤ B * Real.exp (r * M.weight i (v i))
  let S : Set G := {g | ∃ z ∈ E, (l g).toAdd = r • z}
  have hbase n (hn : l n = 1) : n * 1 ∈ S := by
    exact ⟨0, hE0, by simp [hn]⟩
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
  have hscaled : ∀ z ∈ M.templateScaledWord v r u, P z.1 z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    dsimp [P]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hub q hq) (Real.exp_pos _).le
  obtain ⟨hb, hh⟩ := supportWordPath_bound d f hd hf hd₀ hf₀ 1 r l P
    (fun i b _ => M.hom_eq_one_on_letter T hExp realize l hl hL hbound i b)
    hbase (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep
    (M.templateScaledWord v r u) hscaled 1 (map_one l)
  have hp : (2 : ℝ) ^ (M.templateScaledWord v r u).length ≤ 2 ^ N := by
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [templateScaledWord, List.length_map] using hu
  have hb' := hb.mono
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  constructor
  · change PathMetricBound
      (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.templateScaledWord v r u) 1)
      ((C * 2 ^ N) * r) ((C * 2 ^ N) * (1 + Real.log (2 + r)))
    convert hb' using 1 <;> ring
  · exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
