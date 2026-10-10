import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotWordPath
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDirectionalVisits

namespace OAI

/-! # Image bounds for the selected pivot word from its prefix sheets

The switch error is proved from the actual Cartan root curves. Only the
finitely many outward and return sheet comparisons enter as hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped Manifold NNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Once the profiles on the actual prefixes are close, their entire
chosen path has the same height restriction, up to a logarithmic switch
error. There is no assumption on profiles at unrelated sheets. -/
theorem exists_pivotWordPath_observable_bound
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
    ∃ Cp Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ Cs ∧ ∀ r : ℝ, 0 ≤ r → ∀ h₀ : H,
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N →
        (∀ z ∈ u, |z.2| ≤ B * Real.exp (r * s z.1)) →
      ∀ n : G, π n = 1 →
      PathMetricBound (M.pivotWordPath T hExp realize eW w₀ w h₀ r u n)
        (Cp * r) (Cp * (1 + Real.log (2 + r))) ∧
      ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J → ∀ center : W, ∀ E' : Set W,
        ∀ err : ℝ,
        (∃ z ∈ E', ‖J (n * Exp h₀) - center - r • z‖ ≤ err) →
        (∀ v i b tail, u = v ++ (i, b) :: tail → ∀ t : unitInterval,
          (∃ z ∈ E', ‖J (((n * indexedWordProduct (M.rootFlow (Exp := Exp)) v) * Exp h₀) *
              M.pivotSupportFlow T (Exp := Exp) eW w₀ w i (r * t)) - center - r • z‖ ≤ err) ∧
          (∃ z ∈ E', ‖J (((n * indexedWordProduct (M.rootFlow (Exp := Exp)) v) *
              M.rootFlow (Exp := Exp) i b * Exp h₀) *
              M.pivotSupportFlow T (Exp := Exp) eW w₀ w i (r * t)) - center - r • z‖ ≤ err)) →
        ∀ t, ∃ z ∈ E',
          ‖J (M.pivotWordPath T hExp realize eW w₀ w h₀ r u n t) - center - r • z‖ ≤
            err + K * (Cs * Real.log (2 + r)) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let v := fun i => supportLegDirection T H eW w₀ (w i)
  have hv i : cartanHeightWeight T H (M.weight i)
      (eW.symm (w₀ + eW (heightProjection T.character (v i)))) = s i := by
    rw [show eW (heightProjection T.character (v i)) = w i - w₀ from
      supportLegDirection_height T H eW w₀ (w i), add_sub_cancel]
    exact hs i
  obtain ⟨Cs, hCs, hswitch⟩ := M.exists_directional_visit_bound T F hExp realize
    haarD dynkinD eW π hπ v w₀ s hv hA hB p
  obtain ⟨Cp, hCp, hpath⟩ := M.exists_pivotWordPath_bound T hExp realize eW F
    haarD dynkinD π hπ hE hw₀ w hw s hs hA hB p N
  refine ⟨Cp, Cs, hCp, hCs, ?_⟩
  intro r hr h₀ hnorm hheight u hlen hu n hn
  refine ⟨(hpath r hr h₀ hnorm hheight u hlen hu n hn).1, ?_⟩
  intro J K hJ center E' err hbase hsheets
  let d := M.pivotSupportFlow T (Exp := Exp) eW w₀ w
  let f := M.rootFlow (Exp := Exp)
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, pivotSupportFlow, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, rootFlow, hExp.map_zero]
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  apply supportWordPath_image_bound d f hd hf hd₀ hf₀ (Exp h₀) r J hJ u n center E'
    (mul_nonneg hCs hlog) hbase
    (fun v i b tail he => ⟨fun t => (hsheets v i b tail he t).1,
      fun t => (hsheets v i b tail he t).2⟩)
  intro pref i b tail he t
  have hb : |b| ≤ B * Real.exp (r * s i) := hu (i, b) (by simp [he])
  have hh := (hswitch r hr h₀ hnorm hheight (n * indexedWordProduct f pref) i b hb).2
    t t.property 0 (by norm_num)
  simpa only [d, f, v, rootFlow, pivotSupportFlow,
    zero_mul, zero_smul, hExp.map_zero, mul_one, mul_assoc] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
