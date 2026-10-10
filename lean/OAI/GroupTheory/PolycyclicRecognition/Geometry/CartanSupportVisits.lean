import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportPositions
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanVisitPath

namespace OAI

/-! # Controlled visits to actual Cartan support positions

Every letter displacement is realized by a continuous outward-switch-return
path. The constants are uniform over the finite alphabet and polynomially
bounded pivots. Canonical height remains exactly in the convex template.
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
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include F in
/-- Actual single-letter visits, with no path or reachability input. -/
theorem exists_cartan_support_visit_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {E : Set W} (hE : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
    (w : Fin M.letterCount → W) (hw : ∀ i, w i ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (h₀ : H),
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ (n : G), π n = 1 →
      ∀ (i : Fin M.letterCount) (b : ℝ), |b| ≤ B * Real.exp (r * s i) →
      ∃ γ : Path (n * Exp h₀)
          (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        (∀ t, ∃ z ∈ E, (π (γ t)).toAdd = r • z) ∧
        γ = cartanSupportVisitPath T M Exp hExp realize eW w₀ (w i) i n h₀ r b := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let v i := (supportLegDirection T H eW w₀ (w i) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let d (i : Fin M.letterCount) (t : ℝ) := Exp (t • v i)
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize (v i)
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hdmul i u t : d i (u + t) = d i u * d i t := hExp.map_add_smul (v i) u t
  have hπd i t : (π (d i t)).toAdd = t • (w i - w₀) := by
    dsimp only [d]
    rw [hπ, map_smul, map_smul,
      show eW (heightProjection T.character (v i)) = w i - w₀ from
        supportLegDirection_height T H eW w₀ (w i)]
  choose C hC hvisit using (fun i => supportVisitPath_uniform_bound π (d i) (hd i)
    (hd₀ i) (hdmul i) hE hw₀ (hw i) (hπd i))
  obtain ⟨D, q, hD, hpos⟩ := F.exists_support_position_bound T eW haarD dynkinD π hπ w₀ w hA p
  obtain ⟨K, hK, hswitch⟩ := M.exists_uniform_support_switch_curve_bound T Exp hExp realize hD hB q
  let C' := 4 * (1 + (∑ i, C i) + K)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hCi i : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨C', hC', ?_⟩
  intro r hr h₀ hnorm hheight n hn i b hb
  obtain ⟨h, he, hnorm', hheight'⟩ := hpos r hr h₀ hnorm hheight i
  have hweight : M.weight i h = r * s i := by
    rw [← cartanHeightWeight_projection T H (M.weight i) h]
    have hp : heightProjection T.character h = eW.symm (r • w i) := by
      rw [← hheight', eW.symm_apply_apply]
    rw [hp, map_smul, map_smul, hs, smul_eq_mul]
  let f (t : ℝ) := Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hf : Continuous f := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf₀ : f 0 = 1 := by simp [f, hExp.map_zero]
  have hπf t : π (f t) = 1 := cartan_letter_exp_height_eq_one T M Exp eW π hπ i t
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hdiam u (hu : u ∈ Set.Icc (0 : ℝ) 1) t (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dist (n * f (u * b) * (Exp h₀ * d i r))
        (n * f (t * b) * (Exp h₀ * d i r)) ≤ K * Real.log (2 + r) := by
    have hh := hswitch i r hr n h (s i) b hnorm' hweight hb u hu t ht
    simpa only [rootSwitchCurve, he, f, d, v] using hh
  obtain ⟨hγ, hγheight⟩ := hvisit i r hr n (Exp h₀) hn hheight f hf hf₀ hπf b
    (K * Real.log (2 + r)) (mul_nonneg hK.le hlog) hdiam
  refine ⟨cartanSupportVisitPath T M Exp hExp realize eW w₀ (w i) i n h₀ r b,
    hγ.mono ?_ ?_, hγheight, rfl⟩
  · apply mul_le_mul_of_nonneg_right _ hr
    dsimp [C']
    nlinarith [hCi i]
  · dsimp [C']
    have hh := hCi i
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hlog, mul_nonneg hsum hlog]

end PolycyclicRecognition.CartanWordModel

end

end OAI
