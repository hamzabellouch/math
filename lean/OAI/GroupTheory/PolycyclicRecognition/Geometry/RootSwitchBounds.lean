import OAI.GroupTheory.PolycyclicRecognition.Geometry.PublishedRootDistortion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanResidualAction

namespace OAI

/-! # Ambient bounds for root switches at a Cartan position

Conjugating a root displacement back from its Cartan position removes its
scalar weight, up to the proved polynomial nilpotent correction. Applying
actual root distortion gives the logarithmic switch estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

/-- A switch on a translated right-positioned sheet is measured by its
conjugate displacement. -/
theorem dist_right_switch {G : Type*} [Group G] [PseudoMetricSpace G]
    [IsIsometricSMul G G] (x n d : G) :
    dist (x * d) (x * n * d) = dist 1 (d⁻¹ * n * d) := by
  calc
    _ = dist d (n * d) := by simpa only [mul_assoc] using dist_mul_left x d (n * d)
    _ = _ := by simpa only [inv_mul_cancel, mul_assoc] using
      (dist_mul_left d⁻¹ d (n * d)).symm

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- The ambient switch estimate, retaining the full nilpotent correction
and the exponential scalar contraction at the Cartan position. -/
theorem root_switch_bound_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (x : G) (h : H) (v : rootSpace H χ),
      dist (x * Exp h) (x * Exp v * Exp h) ≤
        D * Real.log (2 + C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^
          finrank ℝ (rootSpace H χ) * Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖) := by
  obtain ⟨D, hD, hdist⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  obtain ⟨C, hC, hbound⟩ := exists_rootAction_exp_bound H χ
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  refine ⟨C, D, hC, hD, ?_⟩
  intro x h v
  let w : rootSpace H χ := NormedSpace.exp (rootAction H χ (-h)) v
  have hw : Exp w = (Exp h)⁻¹ * Exp v * Exp h := by
    have hneg : j ((-h : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = -j h := by
      change j (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
      exact map_neg j _
    have hr := represented_root_exp_conjugation H χ j (-h) 1 v
    simp only [one_smul, hneg] at hr
    apply hρ
    rw [map_mul, map_mul, map_inv, hmatch, hmatch, hmatch]
    change algebraExpUnit (j (w : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [algebraExpUnit_neg] at hr
    simpa only [w, inv_inv] using hr
  have hn : ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖ := by
    have hb := hbound (-h) v
    change ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun (-h)‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (χ (-h)) * ‖(rootCoordinates H χ) v‖ at hb
    simpa only [map_neg, norm_neg] using hb
  rw [dist_right_switch, ← hw]
  apply (hdist w).trans
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (by linarith [hn])) hD.le

end PolycyclicRecognition

end

end OAI
