import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Quadratic.BlockDimension

namespace OAI

section

/-!
# Exact nonlinear change count for a quadratic block

For every fixed input, a shear of the line/hyperplane parametrization makes
the output difference the hyperplane coordinate. This proves the uniform
change count before any recursion or random orientation is introduced.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The block's nonlinear observable. -/
def blockObservable (p : Vec F × Vec F) : Vec F := p.2 + Q p.1

omit [Algebra (ZMod 2) F] in
theorem blockObservable_difference (p u : Vec F × Vec F) :
    blockObservable (p + u) + blockObservable p =
      u.2 + Q u.1 + D p.1 u.1 := by
  change (p.2 + u.2) + Q (p.1 + u.1) + (p.2 + Q p.1) = _
  rw [Q_add]
  calc
    _ = u.2 + Q u.1 + D p.1 u.1 + (p.2 + p.2) + (Q p.1 + Q p.1) := by
      ac_rfl
    _ = _ := by rw [vec_add_self, vec_add_self, add_zero, add_zero]

omit [Algebra (ZMod 2) F] in
theorem blockObservable_difference_parametrized (p : Vec F × Vec F) (a w : Vec F) :
    blockObservable (p + (a, Q a + w)) + blockObservable p = w + D p.1 a := by
  rw [blockObservable_difference]
  change (Q a + w) + Q a + D p.1 a = _
  have h : (Q a + w) + Q a = w + (Q a + Q a) := by ac_rfl
  rw [h, vec_add_self, add_zero]

/-- Translation by the polar term permutes the vertical hyperplane. -/
def hyperplaneNoiseShift (v x a : Vec F) (ha : a ∈ line v) :
    hyperplane v ≃ hyperplane v where
  toFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  invFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  left_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]
  right_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]

/-- The polar shear preserves the first coordinate and is its own inverse. -/
def noiseParameterShift (v x : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ (lineBinary v × hyperplaneBinary v) where
  toFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  invFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]

/-- Coordinates in which the nonlinear output difference is just the second
coordinate, for every fixed input `x`. -/
def blockNoiseCoordinates (v x : Vec F) : U v ≃ (lineBinary v × hyperplaneBinary v) :=
  (blockParametrization v).toEquiv.symm.trans (noiseParameterShift v x)

theorem blockObservable_difference_eq_noiseCoordinate
    (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) + blockObservable p =
      ((blockNoiseCoordinates v p.1 u).2 : Vec F) :=
  blockObservable_difference p u

omit [Algebra (ZMod 2) F] in
private theorem vec_add_eq_zero_iff (x y : Vec F) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (fun z : Vec F => z + y) h
    simpa only [add_assoc, vec_add_self, add_zero, zero_add] using h'
  · rintro rfl
    exact vec_add_self _

theorem blockObservable_changes_iff (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p ↔
      (blockNoiseCoordinates v p.1 u).2 ≠ 0 := by
  apply not_congr
  rw [← vec_add_eq_zero_iff, blockObservable_difference_eq_noiseCoordinate]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg (fun w : hyperplaneBinary v => (w : Vec F)) h

theorem blockObservable_change_ne_zero (v : Vec F) (p : Vec F × Vec F) (u : U v)
    (h : blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p) : u ≠ 0 := by
  intro hu
  subst u
  exact h (by simp)

/-- Changed perturbations correspond exactly to an arbitrary line coordinate
and a nonzero hyperplane coordinate. In particular this is uniform in `p`. -/
def changedCoordinatesEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} ≃
      (lineBinary v × {w : hyperplaneBinary v // w ≠ 0}) :=
  ((blockNoiseCoordinates v p.1).subtypeEquiv
    (p := fun u : U v =>
      blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p)
    (q := fun u : lineBinary v × hyperplaneBinary v => u.2 ≠ 0)
    (fun u => blockObservable_changes_iff v p u)).trans
    { toFun := fun u => (u.1.1, ⟨u.1.2, u.2⟩)
      invFun := fun u => ⟨(u.1, u.2.1), u.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem natCard_ne_zero {A : Type*} [Finite A] [Zero A] :
    Nat.card {x : A // x ≠ 0} = Nat.card A - 1 := by
  classical
  let := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_line (v : Vec F) (hv : v ≠ 0) : Nat.card (line v) = Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_line v hv, pow_one]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Nat.card (hyperplane v) = Nat.card F ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_hyperplane v hv]

theorem natCard_U (v : Vec F) (hv : v ≠ 0) : Nat.card (U v) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (blockParametrization v).toEquiv, Nat.card_prod]
  change Nat.card (line v) * Nat.card (hyperplane v) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]
  ring

variable [Finite F]

/-- Exact numerator for the uniform nonzero-perturbation change probability.
Zero never changes the observable, so no exclusion correction is needed. -/
theorem natCard_block_changes (v : Vec F) (hv : v ≠ 0) (p : Vec F × Vec F) :
    Nat.card {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (changedCoordinatesEquiv v p), Nat.card_prod, natCard_ne_zero]
  change Nat.card (line v) * (Nat.card (hyperplane v) - 1) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]

/-- Exact denominator when the perturbation is conditioned to be nonzero. -/
theorem natCard_nonzero_U (v : Vec F) (hv : v ≠ 0) :
    Nat.card {u : U v // u ≠ 0} = Nat.card F ^ 3 - 1 := by
  rw [natCard_ne_zero, natCard_U v hv]

/-- The count ratio simplifies to the one-level survival factor `1-θ`. -/
theorem block_change_ratio (q : ℚ) (hq : 1 < q) :
    q * (q ^ 2 - 1) / (q ^ 3 - 1) = 1 - 1 / (q ^ 2 + q + 1) := by
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hq1 : q - 1 ≠ 0 := by linarith
  have hd : q ^ 2 + q + 1 ≠ 0 := by
    have hs := sq_nonneg q
    linarith
  have hc : q ^ 3 - 1 ≠ 0 := by
    have h : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    rw [h]
    exact mul_ne_zero hq1 hd
  field_simp [hc, hd]
  ring

end UniqueGamesTheorem.Quadratic

end

end OAI
