import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportPositions
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSwitchCurves
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage

namespace OAI

/-! # Visits along the prescribed horizontal directions

The direction of each leg is retained, so its profile is evaluated along
the original horizontal flow. Polynomial pivot coordinates give logarithmic
switch diameter at the chosen supporting endpoint.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

/-- The outward-switch-return path using an explicitly prescribed Cartan direction. -/
def directionalVisitPath (v : H) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r b : ℝ) :
    Path (n * Exp h₀) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact supportVisitPath (fun t => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i))
    (by simp [hExp.map_zero]) n (Exp h₀) r b

include F in
/-- Uniform path and switch bounds for any fixed finite list of prescribed
horizontal directions. The support condition is only an equality of heights. -/
theorem exists_directional_visit_bound
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (v : Fin M.letterCount → H) (w₀ : W) (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (w₀ + eW (heightProjection T.character (v i)))) = s i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ h₀ : H,
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ n : G, ∀ i b,
      |b| ≤ B * Real.exp (r * s i) →
      PathMetricBound (M.directionalVisitPath T hExp realize (v i) i n h₀ r b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (n * Exp ((t * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
          (n * Exp ((u * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp h₀ * Exp (r • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) ≤
          C * Real.log (2 + r) := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) := Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  choose C hC hvisit using (fun i => supportVisitPath_metric_bound (d i) (hd i) (hd₀ i)
    (fun t u => hExp.map_add_smul (v i) t u))
  let V := ∑ i, ‖(finBasis ℝ H).equivFun (v i)‖
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv i : ‖(finBasis ℝ H).equivFun (v i)‖ ≤ V :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((finBasis ℝ H).equivFun (v j))) (Finset.mem_univ i)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbij : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨D, q, hD, hpos⟩ := exists_cartan_scaled_mul_log_bound H F.D.equiv F.ExpD
    hbij F.isExpD dynkinD hA hV p
  obtain ⟨K, hK, hswitch⟩ := M.exists_uniform_support_switch_curve_bound T Exp hExp realize hD hB q
  let C' := 4 * (1 + (∑ i, C i) + K)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hCi i : C i ≤ ∑ j, C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨C', by dsimp [C']; positivity, ?_⟩
  intro r hr h₀ hh₀ hheight n i b hb
  let h := cartanLog H F.D.equiv F.ExpD hbij
    (F.ExpD (F.D.equiv h₀) * F.ExpD (F.D.equiv (r • v i)))
  have he : Exp h = Exp h₀ * d i r := by
    rw [← F.compatibleD h,
      show F.ExpD (F.D.equiv h) = F.ExpD (F.D.equiv h₀) * F.ExpD (F.D.equiv (r • v i)) from
        exp_cartanLog H F.D.equiv F.ExpD hbij _,
      map_mul, F.compatibleD, F.compatibleD]
    rfl
  have hnorm : ‖(finBasis ℝ H).equivFun h‖ ≤ D * (1 + r) ^ q :=
    hpos r hr h₀ (v i) hh₀ (hv i)
  have hheight' : eW (heightProjection T.character h) =
      r • (w₀ + eW (heightProjection T.character (v i))) := by
    rw [← hπ, he, map_mul]
    change (π (Exp h₀)).toAdd + (π (d i r)).toAdd = _
    rw [hheight, hπ]
    simp only [map_smul]
    module
  have hweight : M.weight i h = r * s i := by
    rw [← cartanHeightWeight_projection T H (M.weight i) h]
    have hp : heightProjection T.character h =
        eW.symm (r • (w₀ + eW (heightProjection T.character (v i)))) := by
      rw [← hheight', eW.symm_apply_apply]
    rw [hp, map_smul, map_smul, hs, smul_eq_mul]
  let f (t : ℝ) := Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hf : Continuous f := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf₀ : f 0 = 1 := by simp [f, hExp.map_zero]
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hdiam t (ht : t ∈ Set.Icc (0 : ℝ) 1) u (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      dist (n * f (t * b) * (Exp h₀ * d i r))
        (n * f (u * b) * (Exp h₀ * d i r)) ≤ K * Real.log (2 + r) := by
    simpa only [rootSwitchCurve, he, f] using
      hswitch i r hr n h (s i) b hnorm hweight hb t ht u hu
  constructor
  · have hh := hvisit i r hr n (Exp h₀) f hf hf₀ b (K * Real.log (2 + r))
      (mul_nonneg hK.le hlog) hdiam
    apply hh.mono
    · apply mul_le_mul_of_nonneg_right _ hr
      dsimp [C']
      nlinarith [hCi i]
    · dsimp [C']
      nlinarith [hCi i, mul_nonneg (sub_nonneg.mpr (hCi i)) hlog, mul_nonneg hsum hlog]
  · intro t ht u hu
    apply (hdiam t ht u hu).trans
    apply mul_le_mul_of_nonneg_right _ hlog
    dsimp [C']
    nlinarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
