import Mathlib
import OAI.Computability.MaxCut.Games.Concatenation

namespace OAI

noncomputable section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

section

open scoped BigOperators

namespace MaxCutGames.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Extend the isomorphism taking one specified nonzero vector to another. -/
theorem exists_equiv_map_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton K V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton K V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

theorem nonzero_transitive (x y : {v : V // v ≠ 0}) :
    ∃ a : V ≃ₗ[K] V, a • x = y := by
  obtain ⟨a, ha⟩ := exists_equiv_map_nonzero (K := K) x.val y.val x.property y.property
  exact ⟨a, Subtype.ext ha⟩

/-- A uniform ambient automorphism sends a fixed nonzero symbol uniformly
onto all nonzero symbols. -/
theorem mean_oriented_nonzero [Fintype (V ≃ₗ[K] V)]
    [Fintype {x : V // x ≠ 0}] (x : {v : V // v ≠ 0})
    (f : {v : V // v ≠ 0} → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • x)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ y : {v : V // v ≠ 0}, f y) / Fintype.card {v : V // v ≠ 0} :=
  Orientation.mean_action x (nonzero_transitive x) f

/-- The exact law used after fixing a child line and its nonzero output
difference: averaging over all `J : B ≃ₗ[K] U` is uniform on `U \ {0}`. -/
theorem mean_iso_nonzero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype {u : U // u ≠ 0}] (b : B) (hb : b ≠ 0)
    (f : {u : U // u ≠ 0} → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ u : {u : U // u ≠ 0}, f u) / Fintype.card {u : U // u ≠ 0} := by
  let x : {u : U // u ≠ 0} := ⟨J₀ b, equiv_apply_ne_zero J₀ hb⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • x) := by
    apply Fintype.sum_equiv (Orientation.orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change J b = (J₀.symm.trans J) (J₀ b)
    simp
  rw [hsum, Fintype.card_congr (Orientation.orientationEquiv J₀)]
  exact mean_oriented_nonzero x f

end MaxCutGames.Gadget.OrientationVectors
end

namespace MaxCutGames.Quadratic

section

abbrev Vec (F : Type*) := Fin 3 → F

variable {F : Type*} [Field F]

/-- The three-coordinate quadratic block from equation (2.4). -/
def Q (x : Vec F) : Vec F := ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

/-- Its polar cross-terms.  In characteristic two these equal
`Q (x + a) + Q x + Q a`. -/
def D (x a : Vec F) : Vec F :=
  ![x 1 * a 2 + a 1 * x 2, x 0 * a 2 + a 0 * x 2,
    x 0 * a 1 + a 0 * x 1]

/-- Field dot product, with all three coordinates displayed. -/
def dot (v y : Vec F) : F := v 0 * y 0 + v 1 * y 1 + v 2 * y 2

@[simp] theorem Q_zero : Q (0 : Vec F) = 0 := by
  ext i
  fin_cases i <;> simp [Q]

theorem Q_add (x a : Vec F) : Q (x + a) = Q x + Q a + D x a := by
  ext i
  fin_cases i <;> simp [Q, D] <;> ring

@[simp] theorem D_zero_left (a : Vec F) : D 0 a = 0 := by
  ext i
  fin_cases i <;> simp [D]

@[simp] theorem D_zero_right (x : Vec F) : D x 0 = 0 := by
  ext i
  fin_cases i <;> simp [D]

theorem D_comm (x a : Vec F) : D x a = D a x := by
  ext i
  fin_cases i <;> simp [D, add_comm]

theorem D_add_left (x y a : Vec F) : D (x + y) a = D x a + D y a := by
  ext i
  fin_cases i <;> simp [D] <;> ring

theorem D_add_right (x a b : Vec F) : D x (a + b) = D x a + D x b := by
  rw [D_comm, D_add_left, D_comm a x, D_comm b x]

theorem D_smul_left (t : F) (x a : Vec F) : D (t • x) a = t • D x a := by
  ext i
  fin_cases i <;> simp [D, smul_eq_mul] <;> ring

theorem D_smul_right (t : F) (x a : Vec F) : D x (t • a) = t • D x a := by
  rw [D_comm, D_smul_left, D_comm a x]

@[simp] theorem dot_zero_right (v : Vec F) : dot v 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (y : Vec F) : dot 0 y = 0 := by simp [dot]

theorem dot_add_right (v y z : Vec F) : dot v (y + z) = dot v y + dot v z := by
  simp [dot]
  ring

theorem dot_smul_right (v y : Vec F) (t : F) : dot v (t • y) = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

theorem dot_smul_left (v y : Vec F) (t : F) : dot (t • v) y = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

/-- The field line generated by `v`. -/
def line (v : Vec F) : Submodule F (Vec F) := Submodule.span F {v}

/-- The field hyperplane perpendicular to the generator of the line. -/
def hyperplane (v : Vec F) : Submodule F (Vec F) where
  carrier := {y | dot v y = 0}
  zero_mem' := dot_zero_right v
  add_mem' := by
    intro y z hy hz
    rw [Set.mem_ofPred_eq, dot_add_right, hy, hz, add_zero]
  smul_mem' := by
    intro t y hy
    rw [Set.mem_ofPred_eq, dot_smul_right, hy, mul_zero]

@[simp] theorem mem_hyperplane (v y : Vec F) : y ∈ hyperplane v ↔ dot v y = 0 := Iff.rfl

theorem mem_line_iff (v a : Vec F) : a ∈ line v ↔ ∃ t : F, t • v = a :=
  Submodule.mem_span_singleton

variable [CharP F 2]

@[simp] theorem vec_add_self (x : Vec F) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem D_eq_polar (x a : Vec F) : D x a = Q (x + a) + Q x + Q a := by
  rw [Q_add]
  have h : Q x + Q a + D x a + Q x + Q a =
      D x a + (Q x + Q x) + (Q a + Q a) := by ac_rfl
  rw [h, vec_add_self, vec_add_self, add_zero, add_zero]

private theorem cross_self_zero_inline_Block (u w s t : F) :
    (t * u) * (s * w) + (s * u) * (t * w) = 0 := by
  calc
    _ = (t * s * u * w) + (t * s * u * w) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

/-- The polar expression vanishes on any pair of vectors in the same field line. -/
theorem D_smul_smul_zero (v : Vec F) (t s : F) : D (t • v) (s • v) = 0 := by
  ext i
  fin_cases i <;> simp [D, smul_eq_mul, cross_self_zero_inline_Block]

/-- Every cross-term arising from a shift along `Fv` is perpendicular to `v`. -/
theorem dot_D_smul (v x : Vec F) (t : F) : dot v (D x (t • v)) = 0 := by
  change v 0 * (x 1 * (t * v 2) + (t * v 1) * x 2) +
      v 1 * (x 0 * (t * v 2) + (t * v 0) * x 2) +
      v 2 * (x 0 * (t * v 1) + (t * v 0) * x 1) = 0
  calc
    _ = (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) +
        (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

theorem D_mem_hyperplane (v x a : Vec F) (ha : a ∈ line v) :
    D x a ∈ hyperplane v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  exact dot_D_smul v x t

theorem D_eq_zero_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : D a b = 0 := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  obtain ⟨s, rfl⟩ := (mem_line_iff v b).mp hb
  exact D_smul_smul_zero v t s

/-- The restriction of the quadratic map to one field line is additive. -/
theorem Q_add_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : Q (a + b) = Q a + Q b := by
  rw [Q_add, D_eq_zero_of_mem_line v a b ha hb, add_zero]

variable [Algebra (ZMod 2) F]

/-- The block space `U_A`, as an actual binary submodule.  Membership uses
`y + Q a` because subtraction equals addition in characteristic two. -/
def U (v : Vec F) : Submodule (ZMod 2) (Vec F × Vec F) where
  carrier := {p | p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0}
  zero_mem' := by simp [Q_zero]
  add_mem' := by
    intro p q hp hq
    refine ⟨(line v).add_mem hp.1 hq.1, ?_⟩
    change dot v ((p.2 + q.2) + Q (p.1 + q.1)) = 0
    rw [Q_add_of_mem_line v p.1 q.1 hp.1 hq.1]
    have h : (p.2 + q.2) + (Q p.1 + Q q.1) =
        (p.2 + Q p.1) + (q.2 + Q q.1) := by ac_rfl
    rw [h, dot_add_right, hp.2, hq.2, add_zero]
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp [Q_zero]
    · simpa using hp

@[simp] theorem mem_U (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0 := Iff.rfl

theorem pair_mem_U (v a w : Vec F) (ha : a ∈ line v) (hw : w ∈ hyperplane v) :
    (a, Q a + w) ∈ U v := by
  refine ⟨ha, ?_⟩
  change dot v (Q a + w + Q a) = 0
  have h : Q a + w + Q a = w + (Q a + Q a) := by ac_rfl
  simpa [h] using hw

theorem mem_U_iff_exists (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ ∃ a ∈ line v, ∃ w ∈ hyperplane v, p = (a, Q a + w) := by
  constructor
  · intro hp
    refine ⟨p.1, hp.1, p.2 + Q p.1, hp.2, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = Q p.1 + (p.2 + Q p.1)
      have h : Q p.1 + (p.2 + Q p.1) = p.2 + (Q p.1 + Q p.1) := by ac_rfl
      rw [h, vec_add_self, add_zero]
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact pair_mem_U v a w ha hw

end

/-! Exact field-line count for the quadratic block's erasure probability. -/

section

/-- Actual one-dimensional field directions, with proportional nonzero
vectors identified. -/
abbrev FieldLine (F : Type*) [Field F] := Projectivization F (Vec F)

variable {F : Type*} [Field F]

/-- A chosen nonzero generator, only used with generator-independent data. -/
noncomputable def lineGenerator (A : FieldLine F) : Vec F := A.rep

theorem lineGenerator_ne_zero (A : FieldLine F) : lineGenerator A ≠ 0 :=
  A.rep_nonzero

theorem line_lineGenerator (A : FieldLine F) : line (lineGenerator A) = A.submodule :=
  A.submodule_eq.symm

theorem fieldLine_finrank (A : FieldLine F) : Module.finrank F A.submodule = 1 :=
  A.finrank_submodule

variable [Finite F]

/-- The denominator of the block erasure probability is exactly `q²+q+1`. -/
theorem card_FieldLine : Nat.card (FieldLine F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Vec F) (n := 3)
    (Module.finrank_fin_fun (R := F))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using h

/-- The same count on one-dimensional submodules, rather than representatives. -/
theorem card_fieldLine_submodules :
    Nat.card {A : Submodule F (Vec F) // Module.finrank F A = 1} =
      Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [← Nat.card_congr (Projectivization.equivSubmodule F (Vec F))]
  exact card_FieldLine

theorem card_FieldLine_pos : 0 < Nat.card (FieldLine F) := by
  rw [card_FieldLine]
  exact Nat.succ_pos _

/-- Written over rationals, as needed for the finite rational noise law. -/
theorem reciprocal_card_FieldLine :
    (Nat.card (FieldLine F) : ℚ)⁻¹ =
      ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ := by
  rw [card_FieldLine]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]

end

/-! The binary-linear parametrization and dimension of the quadratic block. -/

section

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev lineBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (line v).restrictScalars (ZMod 2)

abbrev hyperplaneBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (hyperplane v).restrictScalars (ZMod 2)

omit [Algebra (ZMod 2) F] in
private theorem Q_cancel_inline_BlockDimension (a w : Vec F) : Q a + (w + Q a) = w := by
  calc
    _ = w + (Q a + Q a) := by ac_rfl
    _ = w := by rw [vec_add_self, add_zero]

/-- The parametrization `(a,w) ↦ (a,Q(a)+w)` is a binary-linear bijection.
It is not asserted to be field-linear: squaring along a field line is only
binary-linear. -/
def blockParametrization (v : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ₗ[ZMod 2] U v where
  toFun p := ⟨((p.1 : Vec F), Q (p.1 : Vec F) + (p.2 : Vec F)),
    pair_mem_U v p.1 p.2 p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 + Q p.1.1, p.2.2⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) = p.2
      have h : Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) =
          Q (p.1 : Vec F) + ((p.2 : Vec F) + Q (p.1 : Vec F)) := by rw [add_assoc]
      rw [h, Q_cancel_inline_BlockDimension]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Q_cancel_inline_BlockDimension p.1.1 p.1.2
  map_add' := by
    intro p q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Q ((p.1 : Vec F) + (q.1 : Vec F)) + ((p.2 : Vec F) + (q.2 : Vec F)) =
        (Q (p.1 : Vec F) + (p.2 : Vec F)) + (Q (q.1 : Vec F) + (q.2 : Vec F))
      rw [Q_add_of_mem_line v p.1 q.1 p.1.2 q.1.2]
      ac_rfl
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [Q_zero]
    · simp

/-- The dot-product functional over the large field. -/
def dotLinear (v : Vec F) : Vec F →ₗ[F] F where
  toFun := dot v
  map_add' := dot_add_right v
  map_smul' := by intro t y; exact dot_smul_right v y t

omit [CharP F 2] [Algebra (ZMod 2) F] in
@[simp] theorem dotLinear_apply (v y : Vec F) : dotLinear v y = dot v y := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_ker (v : Vec F) : LinearMap.ker (dotLinear v) = hyperplane v := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_surjective (v : Vec F) (hv : v ≠ 0) :
    Function.Surjective (dotLinear v) := by
  classical
  have hi : ∃ i : Fin 3, v i ≠ 0 := by
    by_cases h : ∀ i, v i = 0
    · exact False.elim (hv (funext h))
    · exact not_forall.mp h
  obtain ⟨i, hi⟩ := hi
  intro z
  refine ⟨Pi.single i (z / v i), ?_⟩
  have hsingle (j : Fin 3) (a : F) : dot v (Pi.single j a) = v j * a := by
    fin_cases j <;> simp [dot]
  change dot v (Pi.single i (z / v i)) = z
  rw [hsingle]
  calc
    v i * (z / v i) = (v i * (v i)⁻¹) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hi, one_mul]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (hyperplane v) = 2 := by
  have h := (dotLinear v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotLinear_surjective v hv),
    finrank_top, Module.finrank_self, dotLinear_ker,
    Module.finrank_fin_fun] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_line (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (line v) = 1 :=
  finrank_span_singleton hv

variable [FiniteDimensional (ZMod 2) F]

omit [CharP F 2] in
theorem finrank_lineBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (lineBinary v) = Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (lineBinary v),
    ((line v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_line v hv, mul_one]

omit [CharP F 2] in
theorem finrank_hyperplaneBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (hyperplaneBinary v) = 2 * Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (hyperplaneBinary v),
    ((hyperplane v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_hyperplane v hv,
    mul_comm]

/-- If the field has binary dimension `d`, every nonzero-generator block has
binary dimension `3d`, the dimension of its input/output alphabet. -/
theorem finrank_U (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = 3 * Module.finrank (ZMod 2) F := by
  rw [← (blockParametrization v).finrank_eq, Module.finrank_prod,
    finrank_lineBinary v hv, finrank_hyperplaneBinary v hv]
  omega

theorem finrank_U_eq_finrank_vec (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = Module.finrank (ZMod 2) (Vec F) := by
  rw [finrank_U v hv, ← Module.finrank_mul_finrank (ZMod 2) F (Vec F),
    Module.finrank_fin_fun, mul_comm]

end

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- An orientation identifies the common binary alphabet with a line's block. -/
abbrev BlockOrientation (A : FieldLine F) :=
  Vec F ≃ₗ[ZMod 2] U (lineGenerator A)

noncomputable instance fieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _

instance finiteBlockOrientation (A : FieldLine F) : Finite (BlockOrientation A) :=
  DFunLike.finite _

noncomputable instance blockOrientationFintype (A : FieldLine F) :
    Fintype (BlockOrientation A) := Fintype.ofFinite _

/-- Existence uses the proved dimension of the actual quadratic block. -/
noncomputable def chosenBlockOrientation (A : FieldLine F) : BlockOrientation A :=
  LinearEquiv.ofFinrankEq (Vec F) (U (lineGenerator A))
    (finrank_U_eq_finrank_vec (lineGenerator A) (lineGenerator_ne_zero A)).symm

/-- Composing with one fixed orientation identifies all orientations with
automorphisms of the common binary alphabet. -/
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

end

/-!
# Exact nonlinear change count for a quadratic block

For every fixed input, a shear of the line/hyperplane parametrization makes
the output difference the hyperplane coordinate. This proves the uniform
change count before any recursion or random orientation is introduced.
-/

section

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

/-- Exact numerator for the uniform nonzero-perturbation change probability.
Zero never changes the observable, so no exclusion correction is needed. -/
theorem natCard_block_changes (v : Vec F) (hv : v ≠ 0) (p : Vec F × Vec F) :
    Nat.card {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (changedCoordinatesEquiv v p), Nat.card_prod, natCard_ne_zero_inline_BlockNoise]
  change Nat.card (line v) * (Nat.card (hyperplane v) - 1) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]

/-- Exact denominator when the perturbation is conditioned to be nonzero. -/
theorem natCard_nonzero_U (v : Vec F) (hv : v ≠ 0) :
    Nat.card {u : U v // u ≠ 0} = Nat.card F ^ 3 - 1 := by
  rw [natCard_ne_zero_inline_BlockNoise, natCard_U v hv]

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
  field_simp [hc, hd] ; ring

end

/-! Exact rational expectation for the quadratic block's conditioned noise. -/

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The uniform noise space after conditioning the perturbation to be nonzero. -/
abbrev NonzeroBlock (v : Vec F) := {u : U v // u ≠ 0}

/-- Exact uniform expectation of the nonlinear-change indicator. -/
def nonzeroBlockChangeProbability (v : Vec F) (p : Vec F × Vec F) : ℚ := by
  classical
  exact Finset.univ.expect fun u : NonzeroBlock v =>
    if blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p then 1 else 0

/-- The zero perturbation is never a changed perturbation, so conditioning
does not remove any element from the change event. -/
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

/-- The one-level change probability is exactly `1-θ`, for every fixed input.
Here `θ = 1/(q²+q+1)` and `q` is the actual finite-field cardinality. -/
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

end MaxCutGames.Quadratic

end

end OAI
