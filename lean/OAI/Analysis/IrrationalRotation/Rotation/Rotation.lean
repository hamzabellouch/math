import OAI.Analysis.IrrationalRotation.Model.Rotation
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

@[simp] theorem action_zero (θ : ℝ) (x : Circle) : action θ 0 x = x := by
  simp [action]

@[simp] theorem action_add (θ : ℝ) (m n : ℤ) (x : Circle) :
    action θ m (action θ n x) = action θ (m + n) x := by
  simp only [action, add_zsmul]
  abel

theorem action_continuous (θ : ℝ) (k : ℤ) : Continuous (action θ k) :=
  continuous_id.add continuous_const

theorem action_measurePreserving (θ : ℝ) (k : ℤ) :
    MeasurePreserving (action θ k) circleMeasure circleMeasure := by
  change MeasurePreserving (fun x : Circle => x + k • (θ : Circle)) volume volume
  exact measurePreserving_add_right volume (k • (θ : Circle))

@[simp] theorem orbitWeight_apply (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) (k : ℤ) :
    orbitWeight θ a x k = a (action θ k x) := rfl

theorem orbitWeight_norm_le (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) :
    ‖orbitWeight θ a x‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) (fun _ => a.norm_coe_le_norm _)

theorem representation_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    representation θ a ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (ξ x) :=
  WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun _ => lp.norm_le_of_forall_le (norm_nonneg a) (fun _ => a.norm_coe_le_norm _))
    (fun _ => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable) ξ

theorem representation_coordinates_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      representation θ a ξ x k = a (action θ k x) * ξ x k := by
  filter_upwards [representation_ae θ a ξ] with x hx
  intro k
  rw [hx]
  rfl

theorem U_ae (ξ : Hilbert) :
    U ξ =ᵐ[circleMeasure] fun x => WeightedShift.shift 1 (ξ x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem U_coordinates_ae (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, U ξ x k = ξ x (k - 1) := by
  filter_upwards [U_ae ξ] with x hx
  intro k
  rw [hx]
  rfl

theorem weighted_coordinates_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      weighted θ a ξ x k = a (action θ (k - 1) x) * ξ x (k - 1) := by
  filter_upwards [U_coordinates_ae (representation θ a ξ),
      representation_coordinates_ae θ a ξ] with x hU ha
  intro k
  exact (hU k).trans (ha (k - 1))

theorem action_one_ergodic {θ : ℝ} (hθ : Irrational θ) :
    Ergodic (action θ 1) circleMeasure := by
  change Ergodic (fun x : Circle => x + (1 : ℤ) • (θ : Circle)) circleMeasure
  simp only [one_zsmul]
  change Ergodic (fun x : Circle => x + (θ : Circle)) volume
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  simpa using hθ

theorem character_add (x y : Circle) :
    character (x + y) = character x * character y := by
  simp only [character, fourier_apply, one_zsmul, AddCircle.toCircle_add, Circle.coe_mul]

@[simp] theorem character_norm (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_angle (θ : ℝ) :
    character (θ : Circle) = Complex.exp (2 * Real.pi * Complex.I * θ) := by
  simp only [character, fourier_coe_apply, Int.cast_one, mul_one, Complex.ofReal_one, div_one]

theorem character_action_step (θ : ℝ) (x : Circle) (k : ℤ) :
    character (action θ k x) =
      character (θ : Circle) * character (action θ (k - 1) x) := by
  have h : action θ k x = (θ : Circle) + action θ (k - 1) x := by
    simp only [action, sub_zsmul, one_zsmul]
    abel
  rw [h, character_add]

theorem V_mul_U (θ : ℝ) :
    V θ * U = character (θ : Circle) • (U * V θ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [representation_coordinates_ae θ character (U ξ), U_coordinates_ae ξ,
    U_coordinates_ae (V θ ξ), representation_coordinates_ae θ character ξ,
    Lp.coeFn_smul (character (θ : Circle)) (U (V θ ξ))] with x hVU hU hUV hV hs
  apply lp.ext
  funext k
  change representation θ character (U ξ) x k =
    ((character (θ : Circle) • U (V θ ξ)) x) k
  rw [hs]
  change representation θ character (U ξ) x k =
    character (θ : Circle) * U (V θ ξ) x k
  rw [hVU k, hU k, hUV k]
  change character (action θ k x) * ξ x (k - 1) =
    character (θ : Circle) * representation θ character ξ x (k - 1)
  rw [hV (k - 1), character_action_step]
  ring

theorem V_mul_U_exp (θ : ℝ) :
    V θ * U = Complex.exp (2 * Real.pi * Complex.I * θ) • (U * V θ) := by
  rw [V_mul_U, character_angle]

theorem operator_ext_of_coordinates {A B : Hilbert →L[ℂ] Hilbert}
    (h : ∀ ξ : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, A ξ x k = B ξ x k) : A = B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [h ξ] with x hx
  exact lp.ext (funext hx)

@[simp] theorem representation_one (θ : ℝ) : representation θ 1 = 1 := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ 1 ξ] with x hx
  intro k
  simpa only [ContinuousMap.one_apply, one_mul, one_apply_eq_self] using hx k

@[simp] theorem representation_mul (θ : ℝ) (a b : C(Circle, ℂ)) :
    representation θ (a * b) = representation θ a * representation θ b := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (a * b) ξ,
    representation_coordinates_ae θ a (representation θ b ξ),
    representation_coordinates_ae θ b ξ] with x hab ha hb
  intro k
  change representation θ (a * b) ξ x k =
    representation θ a (representation θ b ξ) x k
  rw [hab k, ha k, hb k, ContinuousMap.mul_apply]
  ring

@[simp] theorem representation_add (θ : ℝ) (a b : C(Circle, ℂ)) :
    representation θ (a + b) = representation θ a + representation θ b := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (a + b) ξ,
    representation_coordinates_ae θ a ξ, representation_coordinates_ae θ b ξ,
    Lp.coeFn_add (representation θ a ξ) (representation θ b ξ)] with x hab ha hb hs
  intro k
  change representation θ (a + b) ξ x k =
    ((representation θ a ξ + representation θ b ξ) x) k
  rw [hs]
  change representation θ (a + b) ξ x k =
    representation θ a ξ x k + representation θ b ξ x k
  rw [hab k, ha k, hb k, ContinuousMap.add_apply]
  ring

@[simp] theorem representation_smul (θ : ℝ) (c : ℂ) (a : C(Circle, ℂ)) :
    representation θ (c • a) = c • representation θ a := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (c • a) ξ,
    representation_coordinates_ae θ a ξ, Lp.coeFn_smul c (representation θ a ξ)] with x hca ha hs
  intro k
  change representation θ (c • a) ξ x k = ((c • representation θ a ξ) x) k
  rw [hs]
  change representation θ (c • a) ξ x k = c * representation θ a ξ x k
  rw [hca k, ha k]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem representation_norm_le (θ : ℝ) (a : C(Circle, ℂ)) :
    ‖representation θ a‖ ≤ ‖a‖ := by
  unfold representation
  exact WeightedShift.norm_fieldDiagonal_le _ _ _ _ _

@[simp] theorem representation_star (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ (star a) = star (representation θ a) := by
  unfold representation
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Filter.Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

@[simp] theorem representation_zero (θ : ℝ) : representation θ 0 = 0 := by
  have hzero : (0 : ℂ) • (1 : C(Circle, ℂ)) = 0 := by
    ext x
    simp
  calc
    representation θ 0 = representation θ ((0 : ℂ) • (1 : C(Circle, ℂ))) :=
      congrArg (representation θ) hzero.symm
    _ = (0 : ℂ) • representation θ (1 : C(Circle, ℂ)) := representation_smul θ 0 1
    _ = 0 := by
      ext vector
      simp

def representationStarAlgHom (θ : ℝ) : C(Circle, ℂ) →⋆ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := representation θ
  map_one' := representation_one θ
  map_mul' := representation_mul θ
  map_zero' := representation_zero θ
  map_add' := representation_add θ
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, representation_smul, representation_one]
  map_star' := representation_star θ

theorem representation_continuous (θ : ℝ) : Continuous (representation θ) := by
  let L := (representationStarAlgHom θ).toAlgHom.toLinearMap
  have hL : ∀ a : C(Circle, ℂ), ‖L a‖ ≤ (1 : ℝ) * ‖a‖ := by
    intro a
    change ‖representation θ a‖ ≤ (1 : ℝ) * ‖a‖
    simpa only [one_mul] using representation_norm_le θ a
  exact (L.mkContinuous 1 hL).continuous

theorem U_mem_unitary : U ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem V_mem_unitary (θ : ℝ) : V θ ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  unfold V representation
  apply WeightedShift.fieldDiagonal_mem_unitary
  exact Filter.Eventually.of_forall fun x k => character_norm (action θ k x)

end Invariant233.Rotation

end

end OAI
