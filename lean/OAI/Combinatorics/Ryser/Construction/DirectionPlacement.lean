import OAI.Combinatorics.Ryser.Construction.LinearPlacement
import OAI.Combinatorics.Ryser.Geometry.AffineJoins

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def directionVector : Direction F → Point F
  | none => (0, 1)
  | some a => (1, a)

theorem directionVector_kernel_iff (d e : Direction F) :
    projection d (directionVector e) = 0 ↔ d = e := let _ := instDecidableEqF; by
  cases d <;> cases e <;> simp [directionVector, projection, sub_eq_zero, eq_comm]

namespace PlaneLinearMap

def directionMap (M : PlaneLinearMap F) : Direction F → Direction F
  | none => if M.xy = 0 then none else some (M.yy / M.xy)
  | some a => if M.xx + M.xy * a = 0 then none
      else some ((M.yx + M.yy * a) / (M.xx + M.xy * a))

def projectionScale (M : PlaneLinearMap F) : Direction F → F
  | none => if M.xy = 0 then M.xx else -M.determinant / M.xy
  | some a => if M.xx + M.xy * a = 0 then M.xy
      else M.determinant / (M.xx + M.xy * a)

theorem projectionScale_ne_zero (M : PlaneLinearMap F) (d : Direction F) :
    M.projectionScale d ≠ 0 := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp only [projectionScale, ite_eq_left hxy]
        intro hxx
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hxy]
        exact div_ne_zero (neg_ne_zero.mpr M.determinant_ne_zero) hxy
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · simp only [projectionScale, ite_eq_left hA]
        intro hxy
        have hxx : M.xx = 0 := by simpa only [hxy, zero_mul, add_zero] using hA
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hA]
        exact div_ne_zero M.determinant_ne_zero hA

theorem projection_directionMap_apply (M : PlaneLinearMap F)
    (d : Direction F) (p : Point F) :
    projection (M.directionMap d) (M.apply p) =
      M.projectionScale d * projection d p := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp [directionMap, projectionScale, hxy, projection, apply]
      · simp only [directionMap, projectionScale, ite_eq_right hxy, projection, apply]
        field_simp [hxy]
        simp only [determinant]
        ring
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · have hxx : M.xx = -(M.xy * a) := eq_neg_of_add_eq_zero_left hA
        simp only [directionMap, projectionScale, ite_eq_left hA, projection, apply]
        rw [hxx]
        ring
      · simp only [directionMap, projectionScale, ite_eq_right hA, projection, apply]
        apply mul_right_cancel₀ hA
        calc
          (M.yx * p.1 + M.yy * p.2 -
              (M.yx + M.yy * a) / (M.xx + M.xy * a) *
                (M.xx * p.1 + M.xy * p.2)) * (M.xx + M.xy * a) =
              (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                ((M.yx + M.yy * a) / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                  (M.xx * p.1 + M.xy * p.2) := by ring
          _ = (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                (M.yx + M.yy * a) * (M.xx * p.1 + M.xy * p.2) := by
              rw [div_mul_cancel₀ _ hA]
          _ = M.determinant * (p.2 - a * p.1) := by
              simp only [determinant]
              ring
          _ = (M.determinant / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                (p.2 - a * p.1) := by rw [div_mul_cancel₀ _ hA]
          _ = (M.determinant / (M.xx + M.xy * a) * (p.2 - a * p.1)) *
                (M.xx + M.xy * a) := by ring

theorem projection_directionMap_apply_eq_iff (M : PlaneLinearMap F)
    (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (M.apply p) =
      projection (M.directionMap d) (M.apply q) ↔
      projection d p = projection d q := by
  rw [M.projection_directionMap_apply, M.projection_directionMap_apply]
  exact ⟨mul_left_cancel₀ (M.projectionScale_ne_zero d),
    congrArg (fun x => M.projectionScale d * x)⟩

theorem directionMap_injective (M : PlaneLinearMap F) :
    Function.Injective M.directionMap := by
  intro d e hde
  have hd : projection d (directionVector d) = 0 :=
    (directionVector_kernel_iff d d).2 rfl
  have hz : projection (M.directionMap e) (M.apply (directionVector d)) = 0 := by
    rw [← hde, M.projection_directionMap_apply, hd, mul_zero]
  rw [M.projection_directionMap_apply] at hz
  have he : projection e (directionVector d) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (M.projectionScale_ne_zero e)
  exact ((directionVector_kernel_iff e d).1 he).symm

theorem projection_directionMap_placed_eq_iff (M : PlaneLinearMap F)
    (b : Point F) (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (b + M.apply p) =
      projection (M.directionMap d) (b + M.apply q) ↔
      projection d p = projection d q := by
  change projection (M.directionMap d)
      (b.1 + (M.apply p).1, b.2 + (M.apply p).2) =
    projection (M.directionMap d)
      (b.1 + (M.apply q).1, b.2 + (M.apply q).2) ↔ _
  rw [projection_add, projection_add, add_left_cancel_iff]
  exact M.projection_directionMap_apply_eq_iff d p q

@[simp] theorem diagonal_directionMap_none (a : F) (ha : a ≠ 0) :
    (diagonal a ha).directionMap none = none := by
  simp [directionMap, diagonal]

@[simp] theorem diagonal_directionMap_some (a : F) (ha : a ≠ 0) (t : F) :
    (diagonal a ha).directionMap (some t) = some (a * t) := by
  simp [directionMap, diagonal]

@[simp] theorem extra_directionMap_none (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap none = some v := by
  simp [directionMap, extra]

@[simp] theorem extra_directionMap_zero (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap (some 0) = some u := by
  simp [directionMap, extra]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k] [instDecidableEqk : DecidableEq k]

def mapDirection (σ : k →+* F) : Direction k → Direction F := Option.map σ

theorem mapDirection_injective (σ : k →+* F) : Function.Injective (mapDirection σ) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  intro d e hde
  cases d with
  | none =>
      cases e with
      | none => rfl
      | some b => cases hde
  | some a =>
      cases e with
      | none => cases hde
      | some b => exact congrArg Option.some (σ.injective (Option.some.inj hde))

theorem projection_mapDirection_mapPoint (σ : k →+* F) (d : Direction k)
    (p : Point k) :
    projection (mapDirection σ d) (mapPoint σ p) = σ (projection d p) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  cases d <;> simp [mapDirection, mapPoint, projection, map_sub, map_mul]

def placedDirection (σ : k →+* F) (M : PlaneLinearMap F) :
    Direction k → Direction F := fun d => M.directionMap (mapDirection σ d)

theorem placedDirection_injective (σ : k →+* F) (M : PlaneLinearMap F) :
    Function.Injective (placedDirection σ M) :=
  M.directionMap_injective.comp (mapDirection_injective σ)

theorem projection_placedPoint_eq_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (d : Direction k) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
      projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d p = projection d q := by
  unfold placedDirection placedPoint
  rw [M.projection_directionMap_placed_eq_iff,
    projection_mapDirection_mapPoint, projection_mapDirection_mapPoint]
  exact σ.injective.eq_iff

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
