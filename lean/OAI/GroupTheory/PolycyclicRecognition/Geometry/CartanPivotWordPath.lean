import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportVisits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportWordImage

namespace OAI

/-! # Explicit word paths based at the actual Cartan pivot -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

def pivotSupportFlow (w₀ : W) (w : Fin M.letterCount → W)
    (i : Fin M.letterCount) (t : ℝ) : G :=
  Exp (t • (supportLegDirection T H eW w₀ (w i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))

def rootFlow (i : Fin M.letterCount) (t : ℝ) : G :=
  Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))

def pivotWordPath (w₀ : W) (w : Fin M.letterCount → W) (h₀ : H) (r : ℝ)
    (u : List (Fin M.letterCount × ℝ)) (n : G) :
    Path (n * Exp h₀) (n * indexedWordProduct (M.rootFlow (Exp := Exp)) u * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact supportWordPath (M.pivotSupportFlow T eW w₀ w) (M.rootFlow (Exp := Exp))
    (fun i => continuous_exp_line_of_published_realization T Exp hExp realize _)
    (fun i => continuous_exp_line_of_published_realization T Exp hExp realize _)
    (fun _ => by simp [pivotSupportFlow, hExp.map_zero])
    (fun _ => by simp [rootFlow, hExp.map_zero]) (Exp h₀) r u n

theorem continuous_pivotWordPath_sample
    {Y : Type*} [TopologicalSpace Y] (w₀ : W) (w : Fin M.letterCount → W)
    (h₀ : H) (r : ℝ) (u : List (Fin M.letterCount × (Y → ℝ)))
    (hu : ∀ z ∈ u, Continuous z.2) (n : Y → G) (hn : Continuous n)
    (t : unitInterval) :
    Continuous (fun y => M.pivotWordPath T hExp realize eW w₀ w h₀ r
      (u.map (fun z => (z.1, z.2 y))) (n y) t) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact continuous_supportWordPath_sample _ _ _ _ _ _ _ _ u hu n hn t

/-- One constant bounds every explicitly prescribed word through the
support positions. The word and its amplitudes may be chosen independently
of the initial sheet. -/
theorem exists_pivotWordPath_bound [IsIsometricSMul G G]
    (F : CartanFactorModel H Exp)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {E : Set W} (hE : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
    (w : Fin M.letterCount → W) (hw : ∀ i, w i ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ h₀ : H,
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N →
        (∀ z ∈ u, |z.2| ≤ B * Real.exp (r * s z.1)) →
        ∀ n : G, π n = 1 →
        PathMetricBound (M.pivotWordPath T hExp realize eW w₀ w h₀ r u n)
          (C * r) (C * (1 + Real.log (2 + r))) ∧
        ∀ t, ∃ z ∈ E,
          (π (M.pivotWordPath T hExp realize eW w₀ w h₀ r u n t)).toAdd = r • z := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨C, hC, hvisit⟩ := M.exists_cartan_support_visit_bound T F eW hExp realize
    haarD dynkinD π hπ hE hw₀ w hw s hs hA hB p
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr h₀ hnorm hheight u hlen hu n hn
  let d := M.pivotSupportFlow T (Exp := Exp) eW w₀ w
  let f := M.rootFlow (Exp := Exp)
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, pivotSupportFlow, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, rootFlow, hExp.map_zero]
  let P i b := |b| ≤ B * Real.exp (r * s i)
  let S := {g : G | ∃ z ∈ E, (π g).toAdd = r • z}
  have hbase m (hm : π m = 1) : m * Exp h₀ ∈ S := by
    refine ⟨w₀, hw₀, ?_⟩
    simpa only [map_mul, hm, one_mul] using hheight
  have hstep m (hm : π m = 1) i b (hb : P i b) :
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
        m (Exp h₀) r b) (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
        m (Exp h₀) r b t ∈ S := by
    obtain ⟨γ, hγ, hrange, he⟩ := hvisit r hr h₀ hnorm hheight m hm i b hb
    subst γ
    exact ⟨hγ, hrange⟩
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨hb, hrange⟩ := supportWordPath_bound d f hd hf hd₀ hf₀ (Exp h₀) r π P
    (fun i b _ => cartan_letter_exp_height_eq_one T M Exp eW π hπ i b)
    hbase (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep u hu n hn
  have hp : (2 : ℝ) ^ u.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hlen
  refine ⟨?_, hrange⟩
  have hb' := hb.mono (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  convert hb' using 1 <;> first | rfl | ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
