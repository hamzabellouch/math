import OAI.Analysis.Cotype.ProjectionL2Gap
import OAI.Analysis.Cotype.WalshSymmetry

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def coordinateReflection {n : ℕ} (i : Fin n) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] PiLp 2 (fun _ : Cube n => X) :=
  (l2Reindex (signCubeTwist (unitIndex i))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem coordinateReflection_apply {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) (ε : Cube n) :
    coordinateReflection i f ε = f (signCubeTwist (unitIndex i) ε) := rfl

theorem coordinateReflection_norm {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) : ‖coordinateReflection i f‖ = ‖f‖ :=
  (l2Reindex (signCubeTwist (unitIndex i))).norm_map f

theorem coordinateReflection_sq {n : ℕ} (i : Fin n) :
    (coordinateReflection (X := X) i)^2 = 1 := by
  ext f ε
  change f (signCubeTwist (unitIndex i) (signCubeTwist (unitIndex i) ε)) = f ε
  apply congrArg (fun u : Cube n => f u)
  funext j
  change xor (unitIndex i j) (xor (unitIndex i j) (ε j)) = ε j
  cases unitIndex i j <;> cases ε j <;> rfl

theorem coordinateReflection_commute {n : ℕ} (i j : Fin n) :
    Commute (coordinateReflection (X := X) i) (coordinateReflection j) := by
  show _ * _ = _ * _
  ext f ε
  change f (signCubeTwist (unitIndex j) (signCubeTwist (unitIndex i) ε)) =
    f (signCubeTwist (unitIndex i) (signCubeTwist (unitIndex j) ε))
  apply congrArg (fun u : Cube n => f u)
  funext k
  change xor (unitIndex j k) (xor (unitIndex i k) (ε k)) =
    xor (unitIndex i k) (xor (unitIndex j k) (ε k))
  exact Bool.xor_left_comm _ _ _

def coordinateExpectation {n : ℕ} (i : Fin n) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] PiLp 2 (fun _ : Cube n => X) :=
  (1/2 : ℝ) • (1+coordinateReflection i)

@[simp] theorem coordinateExpectation_apply {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) (ε : Cube n) :
    coordinateExpectation i f ε = (1/2 : ℝ) • (f ε+f (signCubeTwist (unitIndex i) ε)) := rfl

theorem coordinateExpectation_contracts {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) : ‖coordinateExpectation i f‖ ≤ ‖f‖ := by
  change ‖(1/2 : ℝ) • (f+coordinateReflection i f)‖ ≤ ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have h := norm_add_le f (coordinateReflection i f)
  rw [coordinateReflection_norm] at h
  linarith

theorem coordinateExpectation_idempotent {n : ℕ} (i : Fin n) :
    coordinateExpectation (X := X) i * coordinateExpectation i = coordinateExpectation i := by
  ext f ε
  change (1/2 : ℝ) • ((1/2 : ℝ) • (f ε + f (signCubeTwist (unitIndex i) ε)) +
    (1/2 : ℝ) • (f (signCubeTwist (unitIndex i) ε) +
      f (signCubeTwist (unitIndex i) (signCubeTwist (unitIndex i) ε)))) =
        (1/2 : ℝ) • (f ε + f (signCubeTwist (unitIndex i) ε))
  have he : signCubeTwist (unitIndex i) (signCubeTwist (unitIndex i) ε) = ε :=
    (signCubeTwist (unitIndex i)).left_inv ε
  rw [he]
  module

theorem coordinateExpectation_commute {n : ℕ} (i j : Fin n) :
    Commute (coordinateExpectation (X := X) i) (coordinateExpectation j) := by
  show _ * _ = _ * _
  ext f ε
  simp only [mul_apply_eq_comp, coordinateExpectation_apply]
  have he : signCubeTwist (unitIndex j) (signCubeTwist (unitIndex i) ε) =
      signCubeTwist (unitIndex i) (signCubeTwist (unitIndex j) ε) := by
    funext k
    exact Bool.xor_left_comm _ _ _
  rw [he]
  module

theorem cube_coordinate_semigroup_power_gap (h : NontrivialType X) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 ≤ C ∧ C < (2 : ℝ)^N ∧
      ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
      ∀ f : PiLp 2 (fun _ : Cube n => X),
        ‖((1-projectionSemigroup (coordinateExpectation (X := X)) r)^N) f‖ ≤ C*‖f‖ := by
  obtain ⟨N,hN,C,hC,hC2,hgap⟩ := uniform_projectionSemigroup_power_gap_l2Amplification h
  refine ⟨N,hN,C,hC,hC2,fun n r hr hr1 f => ?_⟩
  exact hgap (Cube n) n coordinateExpectation coordinateExpectation_idempotent
    coordinateExpectation_commute coordinateExpectation_contracts r hr hr1 f

end Cotype

end

end OAI
