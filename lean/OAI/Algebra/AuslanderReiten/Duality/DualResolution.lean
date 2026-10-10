import OAI.Algebra.AuslanderReiten.Algebras.SimpleModule
import Mathlib.Algebra.Module.Opposite

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def fixedLeft (p : C) : Submodule Cᵐᵒᵖ C where
  carrier := {a | p * a = a}
  zero_mem' := mul_zero p
  add_mem' := by
    intro a b ha hb
    change p * a = a at ha
    change p * b = b at hb
    change p * (a + b) = a + b
    rw [mul_add, ha, hb]
  smul_mem' := by
    intro c a ha
    change p * a = a at ha
    change p * (a * MulOpposite.unop c) = a * MulOpposite.unop c
    rw [← mul_assoc, ha]

abbrev rightE : Submodule Cᵐᵒᵖ C := fixedLeft q (basisVector q e)
abbrev rightF : Submodule Cᵐᵒᵖ C := fixedLeft q (basisVector q f)

def evaluateE (g : E q →ₗ[C] C) : rightE q := ⟨g (vertexE q), by
  change basisVector q e * g (vertexE q) = g (vertexE q)
  calc
    _ = g (basisVector q e • vertexE q) := (g.map_smul _ _).symm
    _ = _ := congrArg g (e_smul_vertexE q)⟩

def fromRightE (a : rightE q) : E q →ₗ[C] C where
  toFun b := (b : C) * a
  map_add' b c := add_mul (b : C) c a
  map_smul' c b := mul_assoc c (b : C) a

@[simp] theorem fromRightE_apply (a : rightE q) (b : E q) :
    fromRightE q a b = (b : C) * a := rfl

@[simp] theorem evaluateE_fromRightE (a : rightE q) : evaluateE q (fromRightE q a) = a := by
  apply Subtype.ext
  exact a.property

@[simp] theorem fromRightE_evaluateE (g : E q →ₗ[C] C) : fromRightE q (evaluateE q g) = g := by
  apply LinearMap.ext
  intro a
  change (a : C) • g (vertexE q) = g a
  rw [← g.map_smul, smul_vertexE]

def homEEquiv : (E q →ₗ[C] C) ≃ rightE q where
  toFun := evaluateE q
  invFun := fromRightE q
  left_inv := fromRightE_evaluateE q
  right_inv := evaluateE_fromRightE q

def homERightLinearEquiv : (E q →ₗ[C] C) ≃ₗ[Cᵐᵒᵖ] rightE q where
  __ := homEEquiv q
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem rightE_coeff_zero (a : rightE q) (i : Letter)
    (hi : i = t ∨ i = j ∨ i = f ∨ i = n) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem rightE_coeff_t (a : rightE q) : (a : C).coeff t = 0 :=
  rightE_coeff_zero q a t (by simp)
@[simp] theorem rightE_coeff_j (a : rightE q) : (a : C).coeff j = 0 :=
  rightE_coeff_zero q a j (by simp)
@[simp] theorem rightE_coeff_f (a : rightE q) : (a : C).coeff f = 0 :=
  rightE_coeff_zero q a f (by simp)
@[simp] theorem rightE_coeff_n (a : rightE q) : (a : C).coeff n = 0 :=
  rightE_coeff_zero q a n (by simp)

theorem rightE_expand (a : rightE q) : (a : C) =
    (a : C).coeff e • basisVector q e + (a : C).coeff x • basisVector q x +
    (a : C).coeff y • basisVector q y + (a : C).coeff z • basisVector q z +
    (a : C).coeff u • basisVector q u + (a : C).coeff v • basisVector q v := by
  ext i
  cases i <;> simp

def leftEll (r : k) : rightE q →ₗ[Cᵐᵒᵖ] rightE q where
  toFun a := ⟨ell q r * a, by
    change basisVector q e * (ell q r * a) = ell q r * a
    rw [← mul_assoc]
    congr 1
    ext i
    cases i <;> simp [ell, product]⟩
  map_add' a b := Subtype.ext (mul_add (ell q r) a b)
  map_smul' c a := Subtype.ext (mul_assoc (ell q r) a (MulOpposite.unop c)).symm

@[simp] theorem coe_leftEll (r : k) (a : rightE q) :
    (leftEll q r a : C) = ell q r * a := rfl

theorem evaluateE_precompose (r : k) (g : E q →ₗ[C] C) :
    evaluateE q (g.comp (dEll q r)) = leftEll q r (evaluateE q g) := by
  apply Subtype.ext
  change g (dEll q r (vertexE q)) = ell q r * g (vertexE q)
  have hd : dEll q r (vertexE q) = ell q r • vertexE q := by
    apply Subtype.ext
    change basisVector q e * ell q r = ell q r * basisVector q e
    rw [ell_right_e]
    ext i
    cases i <;> simp [ell, product]
  rw [hd, g.map_smul]
  rfl

theorem ell_mul_formula (r : k) (a : C) :
    ell q r * a = a.coeff e • ell q r +
      (r * a.coeff x + q * a.coeff y) • basisVector q z +
      ((1 + r) * a.coeff u) • basisVector q v := by
  ext i
  cases i <;> simp [ell, product] <;> ring

theorem smul_vertexF (a : F q) : (a : C) • vertexF q = a := by
  apply Subtype.ext
  exact a.property

def evaluateF (g : F q →ₗ[C] C) : rightF q := ⟨g (vertexF q), by
  change basisVector q f • g (vertexF q) = g (vertexF q)
  rw [← g.map_smul]
  congr 1
  exact smul_vertexF q (vertexF q)⟩

def fromRightF (a : rightF q) : F q →ₗ[C] C where
  toFun b := (b : C) * a
  map_add' b c := add_mul (b : C) c a
  map_smul' c b := mul_assoc c (b : C) a

@[simp] theorem evaluateF_fromRightF (a : rightF q) : evaluateF q (fromRightF q a) = a := by
  apply Subtype.ext
  exact a.property

@[simp] theorem fromRightF_evaluateF (g : F q →ₗ[C] C) : fromRightF q (evaluateF q g) = g := by
  apply LinearMap.ext
  intro a
  change (a : C) • g (vertexF q) = g a
  rw [← g.map_smul, smul_vertexF]

def homFEquiv : (F q →ₗ[C] C) ≃ rightF q where
  toFun := evaluateF q
  invFun := fromRightF q
  left_inv := fromRightF_evaluateF q
  right_inv := evaluateF_fromRightF q

def homFRightLinearEquiv : (F q →ₗ[C] C) ≃ₗ[Cᵐᵒᵖ] rightF q where
  __ := homFEquiv q
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem rightF_coeff_zero (a : rightF q) (i : Letter)
    (hi : i = e ∨ i = x ∨ i = y ∨ i = z ∨ i = u ∨ i = v) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem rightF_coeff_e (a : rightF q) : (a : C).coeff e = 0 :=
  rightF_coeff_zero q a e (by simp)
@[simp] theorem rightF_coeff_x (a : rightF q) : (a : C).coeff x = 0 :=
  rightF_coeff_zero q a x (by simp)
@[simp] theorem rightF_coeff_y (a : rightF q) : (a : C).coeff y = 0 :=
  rightF_coeff_zero q a y (by simp)
@[simp] theorem rightF_coeff_z (a : rightF q) : (a : C).coeff z = 0 :=
  rightF_coeff_zero q a z (by simp)
@[simp] theorem rightF_coeff_u (a : rightF q) : (a : C).coeff u = 0 :=
  rightF_coeff_zero q a u (by simp)
@[simp] theorem rightF_coeff_v (a : rightF q) : (a : C).coeff v = 0 :=
  rightF_coeff_zero q a v (by simp)

theorem rightF_expand (a : rightF q) : (a : C) =
    (a : C).coeff f • basisVector q f + (a : C).coeff t • basisVector q t +
    (a : C).coeff j • basisVector q j + (a : C).coeff n • basisVector q n := by
  ext i
  cases i <;> simp

def leftU : rightF q →ₗ[Cᵐᵒᵖ] rightE q where
  toFun a := ⟨basisVector q u * a, by
    change basisVector q e * (basisVector q u * a) = basisVector q u * a
    rw [← mul_assoc, basis_mul]
    simp [multiplicationTable]⟩
  map_add' a b := Subtype.ext (mul_add (basisVector q u) a b)
  map_smul' c a := Subtype.ext (mul_assoc (basisVector q u) a (MulOpposite.unop c)).symm

@[simp] theorem coe_leftU (a : rightF q) : (leftU q a : C) = basisVector q u * a := rfl

theorem evaluate_precompose_dU (g : F q →ₗ[C] C) :
    evaluateE q (g.comp (dU q)) = leftU q (evaluateF q g) := by
  apply Subtype.ext
  change g (dU q (vertexE q)) = basisVector q u * g (vertexF q)
  have hd : dU q (vertexE q) = basisVector q u • vertexF q := by
    apply Subtype.ext
    change basisVector q e * basisVector q u = basisVector q u * basisVector q f
    simp [basis_mul, multiplicationTable]
  rw [hd, g.map_smul]
  rfl

theorem u_mul_formula (a : C) : basisVector q u * a =
    a.coeff f • basisVector q u + a.coeff t • (q • basisVector q x + basisVector q y) +
    a.coeff j • basisVector q z + a.coeff n • basisVector q v := by
  ext i
  cases i <;> simp [product]
  ring

theorem leftU_injective : Function.Injective (leftU q) := by
  apply (injective_iff_map_eq_zero (leftU q)).mpr
  intro a ha
  have hu := congrArg (fun b : rightE q => (b : C).coeff u) ha
  have hy := congrArg (fun b : rightE q => (b : C).coeff y) ha
  have hz := congrArg (fun b : rightE q => (b : C).coeff z) ha
  have hv := congrArg (fun b : rightE q => (b : C).coeff v) ha
  simp [product] at hu hy hz hv
  apply Subtype.ext
  rw [rightF_expand q a]
  simp [hu, hy, hz, hv]

def leftUPreimage (α β γ δ : k) : rightF q :=
  ⟨α • basisVector q f + β • basisVector q t + γ • basisVector q j + δ • basisVector q n, by
    change basisVector q f * _ = _
    simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

theorem leftUPreimage_spec (α β γ δ : k) :
    (leftU q (leftUPreimage q α β γ δ) : C) =
      α • basisVector q u + β • (q • basisVector q x + basisVector q y) +
      γ • basisVector q z + δ • basisVector q v := by
  rw [coe_leftU, u_mul_formula]
  simp [leftUPreimage]

variable [CharP k 2]

theorem ell_mul_eq_zero_iff (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0) (a : C) :
    ell q r * a = 0 ↔ a.coeff e = 0 ∧ a.coeff u = 0 ∧
      a.coeff y = r / q * a.coeff x := by
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff x) h
    have hz := congrArg (fun b : C => b.coeff z) h
    have hv := congrArg (fun b : C => b.coeff v) h
    simp [ell, product] at he hz hv
    have hu : (1 + r) * a.coeff u = 0 := by
      calc
        _ = a.coeff u + r * a.coeff u := by ring
        _ = 0 := hv
    refine ⟨he, (mul_eq_zero.mp hu).resolve_left hr, ?_⟩
    have hy : r * a.coeff x = q * a.coeff y := (CharTwo.add_eq_zero.mp hz).symm
    apply (mul_left_cancel₀ hq)
    calc
      q * a.coeff y = r * a.coeff x := hy.symm
      _ = q * (r / q * a.coeff x) := by field_simp
  · rintro ⟨he, hu, hy⟩
    rw [ell_mul_formula, he, hu, hy]
    have hcancel : r * a.coeff x + q * (r / q * a.coeff x) = 0 := by
      have hd : q * (r / q * a.coeff x) = r * a.coeff x := by field_simp
      rw [hd, CharTwo.add_self_eq_zero]
    simp [hcancel]

def leftEllPreimage (r α β γ : k) : rightE q :=
  ⟨α • basisVector q e + (β / q) • basisVector q y +
    (γ / (1 + r)) • basisVector q u, by
      change basisVector q e * _ = _
      simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem leftEllPreimage_spec (r α β γ : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0) :
    (leftEll q r (leftEllPreimage q r α β γ) : C) =
      α • ell q r + β • basisVector q z + γ • basisVector q v := by
  rw [coe_leftEll, ell_mul_formula]
  have hβ : q * (β / q) = β := by rw [mul_comm, div_mul_cancel₀ _ hq]
  have hγ : (1 + r) * (γ / (1 + r)) = γ := by rw [mul_comm, div_mul_cancel₀ _ hr]
  simp [leftEllPreimage, hβ, hγ]

theorem leftEll_kernel_expand (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0)
    (a : rightE q) (ha : leftEll q r a = 0) :
    (a : C) = (a : C).coeff x • ell q (r / q) +
      (a : C).coeff z • basisVector q z + (a : C).coeff v • basisVector q v := by
  have hh : ell q r * (a : C) = 0 := congrArg Subtype.val ha
  obtain ⟨he, hu, hy⟩ := (ell_mul_eq_zero_iff q r hq hr (a : C)).mp hh
  rw [rightE_expand q a]
  simp [he, hu, hy, ell, smul_add, smul_smul, mul_comm]

theorem leftEll_exact (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0)
    (hqr : 1 + q * r ≠ 0) : Function.Exact (leftEll q r) (leftEll q (q * r)) := by
  intro a
  constructor
  · intro ha
    refine ⟨leftEllPreimage q r ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff v), ?_⟩
    apply Subtype.ext
    rw [leftEllPreimage_spec q r _ _ _ hq hr]
    have hh := leftEll_kernel_expand q (q * r) hq hqr a ha
    have hd : q * r / q = r := by field_simp
    simpa only [hd] using hh.symm
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    change ell q (q * r) * (ell q r * (b : C)) = 0
    rw [← mul_assoc]
    have hz : ell q (q * r) * ell q r = 0 := ell_successor_mul q r
    rw [hz, zero_mul]

theorem leftEll_one_kernel_expand (a : rightE q) (ha : leftEll q 1 a = 0) :
    (a : C) = (a : C).coeff y • (q • basisVector q x + basisVector q y) +
      (a : C).coeff z • basisVector q z + (a : C).coeff u • basisVector q u +
      (a : C).coeff v • basisVector q v := by
  have he := congrArg (fun b : rightE q => (b : C).coeff x) ha
  have hz := congrArg (fun b : rightE q => (b : C).coeff z) ha
  simp [ell, product] at he hz
  have hx : (a : C).coeff x = q * (a : C).coeff y := (CharTwo.add_eq_zero.mp hz).symm
  rw [rightE_expand q a]
  simp [he, hx, smul_add, smul_smul, mul_comm]

theorem leftU_exact : Function.Exact (leftU q) (leftEll q 1) := by
  intro a
  constructor
  · intro ha
    refine ⟨leftUPreimage q ((a : C).coeff u) ((a : C).coeff y)
      ((a : C).coeff z) ((a : C).coeff v), ?_⟩
    apply Subtype.ext
    rw [leftUPreimage_spec]
    conv_rhs => rw [leftEll_one_kernel_expand q a ha]
    abel
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    change ell q 1 * (basisVector q u * (b : C)) = 0
    rw [← mul_assoc, ell_one_mul_u, zero_mul]

def exceptionalBoundaryPreimage (α β : k) : rightE q :=
  ⟨α • basisVector q e + (β / q) • basisVector q y, by
    change basisVector q e * _ = _
    simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem exceptionalBoundaryPreimage_spec (α β : k) (hq : q ≠ 0) :
    (leftEll q 1 (exceptionalBoundaryPreimage q α β) : C) =
      α • ell q 1 + β • basisVector q z := by
  rw [coe_leftEll, ell_mul_formula]
  have hβ : q * (β / q) = β := by rw [mul_comm, div_mul_cancel₀ _ hq]
  simp [exceptionalBoundaryPreimage, hβ]

theorem exceptional_boundary_iff (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (a : rightE q) (ha : leftEll q q a = 0) :
    (∃ b, leftEll q 1 b = a) ↔ (a : C).coeff v = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp [ell, product, CharTwo.add_self_eq_zero]
  · intro hv
    refine ⟨exceptionalBoundaryPreimage q ((a : C).coeff x) ((a : C).coeff z), ?_⟩
    apply Subtype.ext
    rw [exceptionalBoundaryPreimage_spec q _ _ hq]
    have hh := leftEll_kernel_expand q q hq hq1 a ha
    simpa [div_self hq, hv] using hh.symm

def exceptionalCycle : rightE q := ⟨basisVector q v, by
  change basisVector q e * basisVector q v = basisVector q v
  simp [basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem exceptionalCycle_closed (r : k) : leftEll q r (exceptionalCycle q) = 0 := by
  apply Subtype.ext
  change ell q r * basisVector q v = 0
  rw [ell_mul_formula]
  simp

theorem exceptionalCycle_not_boundary (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ¬ ∃ b, leftEll q 1 b = exceptionalCycle q := by
  rw [exceptional_boundary_iff q hq hq1 _ (exceptionalCycle_closed q q)]
  simp [exceptionalCycle]

theorem exceptional_right_action (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (a : rightE q) (ha : leftEll q q a = 0) (b : C) :
    ((a : C) * b).coeff v = (a : C).coeff v * b.coeff f := by
  have hh : ell q q * (a : C) = 0 := congrArg Subtype.val ha
  obtain ⟨he, hu, hy⟩ := (ell_mul_eq_zero_iff q q hq hq1 (a : C)).mp hh
  simp only [div_self hq, one_mul] at hy
  simp [product, he, hu, hy, CharTwo.add_self_eq_zero, add_assoc]

end ArExplicit.Resolution

end

end OAI
