import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotVisits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSampling

namespace OAI

/-! # Physical visit bounds for the original root interval samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] [IsTopologicalGroup G] in
theorem inclusion_rootIntervalSample {m : ℕ} (letters : Fin m → Fin M.letterCount)
    (s : Fin M.letterCount → ℝ) (r : ℝ) (j : Fin m) (t : ℝ) :
    F.inclusionN (rootIntervalSample (F.ExpN ∘ F.N.equiv) letters M.letter s r j.val t) =
      Exp ((t * Real.exp (r * s (letters j))) •
        (M.letter (letters j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  rw [rootIntervalSample_letter]
  simp only [Function.comp_apply, F.compatibleN, smul_smul, SetLike.val_smul]

omit [IsIsometricSMul G G] in
/-- Coordinate descriptions of the same root curve produce the same visit. -/
theorem supportVisitPath_apply_eq_sampled
    (v : H) (i : Fin M.letterCount) (n k : G) (h₀ : H) (r s b : ℝ)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (he : ∀ t, f t = Exp ((t * Real.exp (r * s)) •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hd : Continuous (fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
    (hd₀ : Exp ((0 : ℝ) • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = 1)
    (hk : k = Exp h₀) (t : unitInterval) :
    supportVisitPath (fun t => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      hd hd₀ f hf hf₀ n k r b t =
      M.sampledDirectionalVisitPath T hExp realize v i n h₀ r s b t := by
  unfold sampledDirectionalVisitPath
  exact supportVisitPath_apply_congr _ _ _ _ hd
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    hd₀ (by simp [hExp.map_zero]) hf
    ((continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i)).comp
      (continuous_id.mul_const _)) hf₀ (by simp [hExp.map_zero])
    (fun _ => rfl) he n k (Exp h₀) hk r b t

end PolycyclicRecognition.CartanWordModel

end

end OAI
