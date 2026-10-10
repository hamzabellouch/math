import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHomKernel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportDirections
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSwitchCurves
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitPaths

namespace OAI

/-! # Cartan support visits for finitely many prescribed template directions

The directions are actual Cartan vectors. A convex target containing their
images contains every support path, including the short root switches.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold BigOperators

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

/-- The specified support visit, retained for measurable path sampling. -/
def templateVisitPath (v : Fin M.letterCount → H) (i : Fin M.letterCount) (n : G) (r b : ℝ) :
    Path (n * 1) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let δ := (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  exact supportVisitPath (fun t => Exp (t • δ))
    (continuous_exp_line_of_published_realization T Exp hExp realize δ)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize _)
    (by simp [hExp.map_zero]) n 1 r b

include T hExp realize hl hL hbound in
/-- One common metric bound for the finite family of support directions.
Every value under the homomorphism lies exactly in the scaled target. -/
theorem exists_template_support_visit_bound
    (v : Fin M.letterCount → H) (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ n : G, l n = 1 →
      ∀ (i : Fin M.letterCount) (b : ℝ),
      |b| ≤ B * Real.exp (r * M.weight i (v i)) →
      ∃ γ : Path (n * 1) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        (∀ t, ∃ z ∈ E,
          (l (γ t)).toAdd = r • z) ∧
        γ = M.templateVisitPath T hExp realize v i n r b := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let δ i := v i
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (δ i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hdmul i s t : d i (s + t) = d i s * d i t := hExp.map_add_smul _ s t
  have hld i t : (l (d i t)).toAdd = t • ((l (Exp (δ i))).toAdd - 0) := by
    simpa [d] using hom_flow_eq_smul (d i) (hd i) (hd₀ i) (hdmul i) l hl t
  have hmem i : (l (Exp (δ i))).toAdd ∈ E := hvE i
  choose C hC hvisit using (fun i => supportVisitPath_uniform_bound l (d i) (hd i)
    (hd₀ i) (hdmul i) hE hE0 (hmem i) (hld i))
  let A := ∑ j, ‖(finBasis ℝ H).equivFun (v j)‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv i : ‖(finBasis ℝ H).equivFun (v i)‖ ≤ A :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((finBasis ℝ H).equivFun (v j)))
      (Finset.mem_univ i)
  obtain ⟨K, hK, hswitch⟩ := M.exists_uniform_support_switch_curve_bound T Exp hExp
    realize hA hB 1
  let C' := 4 * (1 + (∑ i, C i) + K)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hCi i : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨C', hC', ?_⟩
  intro r hr n hn i b hb
  let f (t : ℝ) := Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hf : Continuous f := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf₀ : f 0 = 1 := by simp [f, hExp.map_zero]
  have hlf t : l (f t) = 1 := M.hom_eq_one_on_letter T hExp realize l hl hL hbound i t
  have hnorm : ‖(finBasis ℝ H).equivFun (r • δ i)‖ ≤ A * (1 + r) ^ 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, pow_one]
    have hbδ := hv i
    change r * ‖(finBasis ℝ H).equivFun (v i)‖ ≤ A * (1 + r)
    nlinarith
  have hweight : M.weight i (r • δ i) = r * M.weight i (v i) := by
    rw [map_smul, smul_eq_mul]
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hdiam u (hu : u ∈ Set.Icc (0 : ℝ) 1) t (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dist (n * f (u * b) * (1 * d i r)) (n * f (t * b) * (1 * d i r)) ≤
        K * Real.log (2 + r) := by
    have hh := hswitch i r hr n (r • δ i) (M.weight i (v i)) b
      hnorm hweight hb u hu t ht
    simpa only [rootSwitchCurve, one_mul, SetLike.val_smul, d, f] using hh
  obtain ⟨hγ, hγheight⟩ := hvisit i r hr n 1 hn (by simp) f hf hf₀ hlf b
    (K * Real.log (2 + r)) (mul_nonneg hK.le hlog) hdiam
  refine ⟨supportVisitPath (d i) (hd i) (hd₀ i) f hf hf₀ n 1 r b,
    hγ.mono ?_ ?_, hγheight, rfl⟩
  · apply mul_le_mul_of_nonneg_right _ hr
    dsimp [C']
    nlinarith [hCi i]
  · dsimp [C']
    nlinarith [hCi i, mul_nonneg (sub_nonneg.mpr (hCi i)) hlog,
      mul_nonneg hsum hlog]

end PolycyclicRecognition.CartanWordModel

end

end OAI
