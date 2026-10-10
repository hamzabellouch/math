import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportSwitch
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs

namespace OAI

/-! # Continuous short switches with constant height

Use the actual root one-parameter subgroup for a switch. Every pair of its
points has logarithmic distance at a supporting Cartan position, while its
canonical height is exactly constant. No choice of geodesics is needed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

def rootSwitchCurve {L G : Type*} [SMul ℝ L] [Mul G]
    (Exp : L → G) (v : L) (a : ℝ) (x d : G) (t : ℝ) : G :=
  x * Exp ((t * a) • v) * d

theorem rootSwitchCurve_endpoints {L G : Type*} [AddCommGroup L] [Module ℝ L]
    [Group G] (Exp : L → G) (hzero : Exp 0 = 1) (v : L) (a : ℝ) (x d : G) :
    rootSwitchCurve Exp v a x d 0 = x * d ∧
      rootSwitchCurve Exp v a x d 1 = x * Exp (a • v) * d := by
  simp [rootSwitchCurve, hzero]

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

omit [IsIsometricSMul G G] in
include T hExp realize in
theorem continuous_rootSwitchCurve (i : Fin M.letterCount) (b : ℝ) (x d : G) :
    Continuous (rootSwitchCurve Exp (M.letter i) b x d) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have h := continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i)
  exact (continuous_const.mul (h.comp (continuous_id.mul continuous_const))).mul
    continuous_const

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] in
include T in
theorem cartan_letter_exp_height_eq_one
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ v, (π (Exp v)).toAdd = eW (heightProjection T.character v))
    (i : Fin M.letterCount) (t : ℝ) :
    π (Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  have hz : heightProjection T.character (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T (M.letter i).property)
  change (π (Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd = 0
  rw [hπ, map_smul, hz, smul_zero, map_zero]

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] in
include T in
theorem rootSwitchCurve_height
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ v, (π (Exp v)).toAdd = eW (heightProjection T.character v))
    (i : Fin M.letterCount) (b : ℝ) (x d : G) (t : ℝ) :
    (π (rootSwitchCurve Exp (M.letter i) b x d t)).toAdd = (π (x * d)).toAdd := by
  have hz : heightProjection T.character (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T (M.letter i).property)
  simp only [rootSwitchCurve, map_mul]
  change (π x).toAdd + (π (Exp ((t * b) • (M.letter i :
    GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd + (π d).toAdd = (π x).toAdd + (π d).toAdd
  rw [hπ, map_smul, hz, smul_zero, map_zero, add_zero]

include T hExp realize in
/-- One logarithmic diameter bound for all actual root switch curves. -/
theorem CartanWordModel.exists_uniform_support_switch_curve_bound
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin M.letterCount) (r : ℝ), 0 ≤ r →
      ∀ (x : G) (h : H) (s b : ℝ),
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      M.weight i h = r * s → |b| ≤ B * Real.exp (r * s) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      dist (rootSwitchCurve Exp (M.letter i) b x (Exp h) t)
        (rootSwitchCurve Exp (M.letter i) b x (Exp h) u) ≤ K * Real.log (2 + r) := by
  obtain ⟨K, hK, hb⟩ := M.exists_uniform_support_switch_bound T Exp hExp realize hA hB p
  refine ⟨K, hK, ?_⟩
  intro i r hr x h s b hh hs hb' t ht u hu
  have hsub : |u - t| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, ht.2], by linarith [hu.2, ht.1]⟩
  have hamp : |(u - t) * b| ≤ B * Real.exp (r * s) := by
    rw [abs_mul]
    calc
      |u - t| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right hsub (abs_nonneg b)
      _ ≤ B * Real.exp (r * s) := by simpa using hb'
  have he : Exp ((u * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
      Exp ((t * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
        Exp (((u - t) * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [← hExp.map_add_smul]
    congr 2
    ring
  have h := hb i r hr (x * Exp ((t * b) • (M.letter i :
    GroupLieAlgebra (𝓘(ℝ, EG)) G))) h s ((u - t) * b) hh hs hamp
  simpa only [rootSwitchCurve, he, mul_assoc] using h

end PolycyclicRecognition

end

end OAI
