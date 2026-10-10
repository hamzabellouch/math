import Mathlib
import OAI.Computability.DirectedFeedback.Games.ChildLifts

namespace OAI

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev BlockOrientation (A : FieldLine F) :=
  Vec F ≃ₗ[ZMod 2] U (lineGenerator A)

noncomputable instance fieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _

instance finiteBlockOrientation (A : FieldLine F) : Finite (BlockOrientation A) :=
  DFunLike.finite _

noncomputable instance blockOrientationFintype (A : FieldLine F) :
    Fintype (BlockOrientation A) := Fintype.ofFinite _

noncomputable def chosenBlockOrientation (A : FieldLine F) : BlockOrientation A :=
  LinearEquiv.ofFinrankEq (Vec F) (U (lineGenerator A))
    (finrank_U_eq_finrank_vec (lineGenerator A) (lineGenerator_ne_zero A)).symm

noncomputable def blockOrientationEquiv (A : FieldLine F) :
    BlockOrientation A ≃ (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun J := J.trans (chosenBlockOrientation A).symm
  invFun J := J.trans (chosenBlockOrientation A)
  left_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).apply_symm_apply (J x)
  right_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).symm_apply_apply (J x)

theorem card_blockOrientation (A : FieldLine F) :
    Nat.card (BlockOrientation A) = Nat.card (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Nat.card_congr (blockOrientationEquiv A)

theorem card_blockOrientation_eq (A B : FieldLine F) :
    Nat.card (BlockOrientation A) = Nat.card (BlockOrientation B) := by
  rw [card_blockOrientation, card_blockOrientation]

theorem card_blockOrientation_pos (A : FieldLine F) :
    0 < Nat.card (BlockOrientation A) := by
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  exact Nat.card_pos

abbrev BlockOrientationIndex (F : Type*) [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] := Σ A : FieldLine F, BlockOrientation A

noncomputable def blockOrientationIndexEquiv :
    BlockOrientationIndex F ≃ FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun p := (p.1, blockOrientationEquiv p.1 p.2)
  invFun p := ⟨p.1, (blockOrientationEquiv p.1).symm p.2⟩
  left_inv := by
    rintro ⟨A, J⟩
    simp
  right_inv := by
    rintro ⟨A, J⟩
    simp

theorem card_blockOrientationIndex :
    Nat.card (BlockOrientationIndex F) =
      (Nat.card F ^ 2 + Nat.card F + 1) * Nat.card (Vec F ≃ₗ[ZMod 2] Vec F) := by
  rw [Nat.card_congr (blockOrientationIndexEquiv (F := F)), Nat.card_prod, card_FieldLine]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

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

def blockNoiseCoordinates (v x : Vec F) : U v ≃ (lineBinary v × hyperplaneBinary v) :=
  (blockParametrization v).toEquiv.symm.trans (noiseParameterShift v x)

theorem blockObservable_difference_eq_noiseCoordinate
    (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) + blockObservable p =
      ((blockNoiseCoordinates v p.1 u).2 : Vec F) :=
  blockObservable_difference p u

omit [Algebra (ZMod 2) F] in
private theorem vec_add_eq_zero_iff_inline_BlockNoise (x y : Vec F) : x + y = 0 ↔ x = y := by
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
  rw [← vec_add_eq_zero_iff_inline_BlockNoise, blockObservable_difference_eq_noiseCoordinate]
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

private theorem natCard_ne_zero_inline_BlockNoise {A : Type*} [Finite A] [Zero A] :
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

theorem natCard_block_changes (v : Vec F) (hv : v ≠ 0) (p : Vec F × Vec F) :
    Nat.card {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (changedCoordinatesEquiv v p), Nat.card_prod, natCard_ne_zero_inline_BlockNoise]
  change Nat.card (line v) * (Nat.card (hyperplane v) - 1) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]

theorem natCard_nonzero_U (v : Vec F) (hv : v ≠ 0) :
    Nat.card {u : U v // u ≠ 0} = Nat.card F ^ 3 - 1 := by
  rw [natCard_ne_zero_inline_BlockNoise, natCard_U v hv]

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
  field_simp [hc, hd] ; ring

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev NonzeroBlock (v : Vec F) := {u : U v // u ≠ 0}

def nonzeroBlockChangeProbability (v : Vec F) (p : Vec F × Vec F) : ℚ := by
  classical
  exact Finset.univ.expect fun u : NonzeroBlock v =>
    if blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p then 1 else 0

def conditionedChangedEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : NonzeroBlock v //
      blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p} ≃
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} where
  toFun u := ⟨u.val.val, u.property⟩
  invFun u := ⟨⟨u.val, blockObservable_change_ne_zero v p u.val u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nonzeroBlockChangeProbability_eq_count (v : Vec F) (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      (Nat.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} : ℚ) /
      (Nat.card (NonzeroBlock v) : ℚ) := by
  classical
  have hcard :
      (Finset.univ.filter (fun u : NonzeroBlock v =>
        blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p)).card =
      Fintype.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (conditionedChangedEquiv v p)
  simp only [nonzeroBlockChangeProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, hcard, Nat.card_eq_fintype_card]

theorem nonzeroBlockChangeProbability_eq (v : Vec F) (hv : v ≠ 0)
    (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [nonzeroBlockChangeProbability_eq_count, natCard_block_changes v hv p]
  change ((Nat.card F * (Nat.card F ^ 2 - 1) : ℕ) : ℚ) /
    (Nat.card {u : U v // u ≠ 0} : ℚ) = _
  rw [natCard_nonzero_U v hv]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqpos : 0 < Nat.card F := lt_trans Nat.zero_lt_one hq
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ hqpos
  have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow 3 _ hqpos
  have hq' : (1 : ℚ) < Nat.card F := by exact_mod_cast hq
  simpa only [Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_sub hq3,
    Nat.cast_pow, Nat.cast_one] using block_change_ratio (Nat.card F) hq'

end

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators

namespace DFVSGames.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def orientedBlockLinear (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def orientedBlockChange (i : BlockOrientationIndex F) (p : Vec F × Vec F)
    (d : Vec F) : ℚ := by
  classical
  exact if blockObservable (p + orientedBlockLinear i d) ≠ blockObservable p then 1 else 0

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_orientations_change (A : FieldLine F) (p : Vec F × Vec F)
    (d : Vec F) (hd : d ≠ 0) :
    (𝔼 J : BlockOrientation A, orientedBlockChange ⟨A, J⟩ p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  let : Finite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A)) := DFunLike.finite _
  let := Fintype.ofFinite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A))
  calc
    _ = nonzeroBlockChangeProbability (lineGenerator A) p := by
      unfold nonzeroBlockChangeProbability orientedBlockChange
      simp only [Fintype.expect_eq_sum_div_card]
      exact OrientationVectors.mean_iso_nonzero (chosenBlockOrientation A) d hd
        (fun u => if blockObservable (p + (u.val : Vec F × Vec F)) ≠
          blockObservable p then 1 else 0)
    _ = _ := nonzeroBlockChangeProbability_eq _ (lineGenerator_ne_zero A) p

variable [Fintype (FieldLine F)] [Fintype (Vec F ≃ₗ[ZMod 2] Vec F)]

theorem mean_block_pairs (f : BlockOrientationIndex F → ℚ) :
    (𝔼 i : BlockOrientationIndex F, f i) =
      𝔼 A : FieldLine F, 𝔼 J : BlockOrientation A, f ⟨A, J⟩ := by
  classical
  calc
    _ = 𝔼 z : FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F),
        f ((blockOrientationIndexEquiv (F := F)).symm z) := by
      exact Fintype.expect_equiv (blockOrientationIndexEquiv (F := F)) _ _
        (fun i => by simp)
    _ = 𝔼 A : FieldLine F, 𝔼 a : Vec F ≃ₗ[ZMod 2] Vec F,
        f ⟨A, (blockOrientationEquiv A).symm a⟩ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro A _
      exact Fintype.expect_equiv (blockOrientationEquiv A).symm _ _ (fun _ => rfl)

theorem mean_oriented_block_change (p : Vec F × Vec F) (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  simp_rw [mean_orientations_change _ p d hd]
  exact Fintype.expect_const _

theorem mean_oriented_block_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [Finset.expect_comm]
  simp_rw [mean_oriented_block_change _ d hd]
  exact Fintype.expect_const _

end DFVSGames.Gadget.OrientedBlockKernel
end

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem squareMap_injective : Function.Injective (fun x : F => x ^ 2) := by
  intro x y h
  change x ^ 2 = y ^ 2 at h
  have hs : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  have hz : x + y = 0 := (sq_eq_zero_iff).mp hs
  exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq y)

noncomputable def squareRoot (c : F) : F :=
  Classical.choose (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_sq (c : F) : squareRoot c ^ 2 = c :=
  Classical.choose_spec (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_of_sq (c : F) : squareRoot (c ^ 2) = c := by
  apply squareMap_injective
  exact squareRoot_sq _

theorem squareRoot_unique {c r : F} (h : r ^ 2 = c) : r = squareRoot c := by
  apply squareMap_injective
  change r ^ 2 = squareRoot c ^ 2
  rw [h, squareRoot_sq]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

noncomputable abbrev traceBinary : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F

omit [CharP F 2] in
theorem trace_square (x : F) : traceBinary (x ^ 2) = traceBinary x := by
  simpa only [traceBinary, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x

theorem trace_square_mul (t c : F) :
    traceBinary (t ^ 2 * c) = traceBinary (t * squareRoot c) := by
  calc
    traceBinary (t ^ 2 * c) = traceBinary ((t * squareRoot c) ^ 2) := by
      rw [mul_pow, squareRoot_sq]
    _ = traceBinary (t * squareRoot c) := trace_square _

omit [CharP F 2] in

theorem trace_mul_vanish_iff (a : F) :
    (∀ t : F, traceBinary (t * a) = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply (traceForm_nondegenerate (ZMod 2) F).1 a
    intro t
    simpa only [Algebra.traceForm_apply, mul_comm] using h t
  · rintro rfl
    simp

theorem trace_quadratic_vanish_iff (a c : F) :
    (∀ t : F, traceBinary (t * a + t ^ 2 * c) = 0) ↔ a = squareRoot c := by
  have heq (t : F) :
      traceBinary (t * a + t ^ 2 * c) = traceBinary (t * (a + squareRoot c)) := by
    rw [map_add, trace_square_mul, mul_add, map_add]
  simp_rw [heq]
  rw [trace_mul_vanish_iff, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem dot_add_first_inline_TraceDual (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

def traceDotForm : LinearMap.BilinForm (ZMod 2) (Vec F) where
  toFun z :=
    { toFun := fun y => traceBinary (dot z y)
      map_add' := by
        intro x y
        rw [dot_add_right, map_add]
      map_smul' := by
        intro c y
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hc with rfl | rfl <;> simp }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro y
    change traceBinary (dot (z + w) y) =
      traceBinary (dot z y) + traceBinary (dot w y)
    rw [dot_add_first_inline_TraceDual, map_add]
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext y <;> simp

omit [Finite F] [CharP F 2] in
@[simp] theorem traceDotForm_apply (z y : Vec F) :
    traceDotForm z y = traceBinary (dot z y) := rfl

omit [CharP F 2] in

theorem traceDotForm_nondegenerate :
    (traceDotForm (F := F)).Nondegenerate := by
  constructor
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot z (Pi.single i t) = t * z i := by
      fin_cases i <;> simp [dot, mul_comm]
    simpa only [traceDotForm_apply, hd] using h
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot (Pi.single i t) z = t * z i := by
      fin_cases i <;> simp [dot]
    simpa only [traceDotForm_apply, hd] using h

def traceDualEquiv : Vec F ≃ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  traceDotForm.toDual traceDotForm_nondegenerate

omit [CharP F 2]

@[simp] theorem traceDualEquiv_apply (z y : Vec F) :
    traceDualEquiv z y = traceBinary (dot z y) := rfl

@[simp] theorem traceDualEquiv_symm_apply
    (γ : Vec F →ₗ[ZMod 2] ZMod 2) (y : Vec F) :
    traceBinary (dot (traceDualEquiv.symm γ) y) = γ y := by
  change traceDualEquiv (traceDualEquiv.symm γ) y = γ y
  rw [LinearEquiv.apply_symm_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

def representTraceFamily (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) :
    W →ₗ[ZMod 2] Vec F :=
  traceDualEquiv.symm.toLinearMap.comp γ

theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F]

private theorem dot_sub_right_inline_BlockTrace (v y z : Vec F) :
    dot v (y - z) = dot v y - dot v z := by
  simp [dot]
  ring

private theorem dot_single_inline_BlockTrace (v : Vec F) (i : Fin 3) (a : F) :
    dot v (Pi.single i a) = v i * a := by
  fin_cases i <;> simp [dot]

theorem annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, dot z y = 0) ↔ z ∈ line v := by
  constructor
  · intro hz
    have hv' : ∃ i : Fin 3, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hv'
    apply (mem_line_iff v z).mpr
    refine ⟨z i / v i, ?_⟩
    ext j
    have hy : Pi.single j (1 : F) - (v j / v i) • Pi.single i (1 : F) ∈
        hyperplane v := by
      rw [mem_hyperplane, dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace]
      simp [div_mul_cancel₀ _ hi]
    have hzero := hz _ hy
    rw [dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace,
      mul_one, mul_one, sub_eq_zero] at hzero
    change (z i / v i) * v j = z j
    rw [hzero]
    simp only [div_eq_mul_inv]
    ring
  · intro hz y hy
    obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hz
    rw [dot_smul_left, (mem_hyperplane v y).mp hy, mul_zero]

variable [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in

theorem trace_annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, traceBinary (dot z y) = 0) ↔ z ∈ line v := by
  rw [← annihilator_hyperplane_iff_mem_line hv]
  constructor
  · intro hz y hy
    apply (trace_mul_vanish_iff (dot z y)).mp
    intro t
    have ht := hz (t • y) ((hyperplane v).smul_mem t hy)
    simpa only [dot_smul_right] using ht
  · intro hz y hy
    rw [hz y hy, map_zero]

omit [CharP F 2] in
theorem trace_annihilator_hyperplane (v : Vec F) (hv : v ≠ 0) :
    {z : Vec F | ∀ y ∈ hyperplane v, Algebra.trace (ZMod 2) F (dot z y) = 0} =
      (line v : Set (Vec F)) := by
  ext z
  exact trace_annihilator_hyperplane_iff_mem_line hv

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in

theorem dot_Q_smul (z : Vec F) (t : F) :
    dot z (Q (t • z)) = t ^ 2 * (z 0 * z 1 * z 2) := by
  change z 0 * ((t * z 1) * (t * z 2)) +
      z 1 * ((t * z 0) * (t * z 2)) +
      z 2 * ((t * z 0) * (t * z 1)) = _
  calc
    _ = (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

noncomputable def blockCharacter (g z : Vec F) (p : Vec F × Vec F) : ZMod 2 :=
  traceBinary (dot g p.1 + dot z p.2)

def BlockAnnihilates (g z v : Vec F) : Prop :=
  ∀ p ∈ U v, blockCharacter g z p = 0

omit [Finite F] in
theorem blockCharacter_on_quadratic (g z : Vec F) (t : F) :
    blockCharacter g z (t • z, Q (t • z)) =
      traceBinary (t * dot g z + t ^ 2 * (z 0 * z 1 * z 2)) := by
  simp only [blockCharacter, dot_smul_right, dot_Q_smul]

theorem blockAnnihilates_self_iff (g z : Vec F) :
    BlockAnnihilates g z z ↔ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    apply (trace_quadratic_vanish_iff _ _).mp
    intro t
    have hm : (t • z, Q (t • z)) ∈ U z := by
      simpa only [add_zero] using pair_mem_U z (t • z) 0
        ((mem_line_iff z (t • z)).mpr ⟨t, rfl⟩) (Submodule.zero_mem _)
    simpa only [blockCharacter_on_quadratic] using h _ hm
  · intro h p hp
    obtain ⟨a, ha, w, hw, rfl⟩ := (mem_U_iff_exists z p).mp hp
    obtain ⟨t, rfl⟩ := (mem_line_iff z a).mp ha
    change traceBinary (dot g (t • z) + dot z (Q (t • z) + w)) = 0
    rw [dot_add_right, (mem_hyperplane z w).mp hw, add_zero,
      dot_smul_right, dot_Q_smul]
    exact (trace_quadratic_vanish_iff _ _).mpr h t

omit [Finite F] in

theorem U_smul_ne_zero (v : Vec F) {t : F} (ht : t ≠ 0) : U (t • v) = U v := by
  have hl : line (t • v) = line v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v
  ext p
  simp only [mem_U, hl, dot_smul_left, mul_eq_zero, ht, false_or]

omit [Finite F] in
theorem U_eq_of_nonzero_mem_line {v z : Vec F} (hz : z ≠ 0)
    (hm : z ∈ line v) : U z = U v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hm
  have ht : t ≠ 0 := by
    intro ht
    apply hz
    simp [ht]
  exact U_smul_ne_zero v ht

theorem mem_line_of_blockAnnihilates {g z v : Vec F} (hv : v ≠ 0)
    (h : BlockAnnihilates g z v) : z ∈ line v := by
  apply (trace_annihilator_hyperplane_iff_mem_line hv).mp
  intro y hy
  have hm : (0, y) ∈ U v := by
    simpa only [Q_zero, zero_add] using
      pair_mem_U v 0 y (Submodule.zero_mem _) hy
  simpa only [blockCharacter, dot_zero_right, zero_add] using h _ hm

theorem blockAnnihilates_iff {g z v : Vec F} (hv : v ≠ 0) (hz : z ≠ 0) :
    BlockAnnihilates g z v ↔
      z ∈ line v ∧ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    have hm := mem_line_of_blockAnnihilates hv h
    refine ⟨hm, (blockAnnihilates_self_iff g z).mp ?_⟩
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h
  · rintro ⟨hm, ha⟩
    have h := (blockAnnihilates_self_iff g z).mpr ha
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

theorem dot_lift_eq_alignment_mulVec (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (g : V →ₗ[R] (n → F)) (e : E) :
    (∑ i, z (point e) i * g (point e) i) =
      (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e := by
  have hg : g (point e) = ∑ j, b.repr (point e) j • g (b j) := by
    calc
      g (point e) = g (∑ j, b.repr (point e) j • b j) :=
        congrArg g (b.sum_repr (point e)).symm
      _ = ∑ j, b.repr (point e) j • g (b j) := by simp only [map_sum, map_smul]
  rw [hg]
  simp only [Matrix.mulVec, dotProduct, alignmentMatrix,
    Finset.sum_apply, Algebra.smul_def, Pi.mul_apply,
    Pi.algebraMap_apply, Finset.mul_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem exists_lift_alignment_iff_mem_range (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (c : E → F) :
    (∃ g : V →ₗ[R] (n → F), ∀ e,
      (∑ i, z (point e) i * g (point e) i) = c e) ↔
      c ∈ LinearMap.range (alignmentMatrix b point z).mulVecLin := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun ij => g (b ij.2) ij.1, ?_⟩
    ext e
    change (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e = c e
    rw [← dot_lift_eq_alignment_mulVec]
    exact hg e
  · rintro ⟨u, hu⟩
    let g : V →ₗ[R] (n → F) := b.constr R (fun j i => u (i, j))
    refine ⟨g, ?_⟩
    intro e
    rw [dot_lift_eq_alignment_mulVec b point z g e]
    have hg : (fun ij : n × ι => g (b ij.2) ij.1) = u := by
      funext ij
      exact congrFun (b.constr_basis R (fun j i => u (i, j)) ij.2) ij.1
    rw [hg]
    exact congrFun hu e

theorem finrank_alignment_range_le (b : Basis ι R V)
    (point : E → V) (z : V → n → F) [Fintype E] :
    Module.finrank F (LinearMap.range (alignmentMatrix b point z).mulVecLin) ≤
      Fintype.card n * Fintype.card ι := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
      (LinearMap.finrank_range_le (alignmentMatrix b point z).mulVecLin)

end

end DFVSGames.Quadratic

end OAI
