import OAI.Analysis.RotationWeights.Model

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
namespace ContinuousCircleWeight

def lpPermute {ι : Type uι} (e : Equiv.Perm ι) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => f (e.symm i), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun f := ⟨fun i => f (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem lpPermute_apply {ι : Type uι} (e : Equiv.Perm ι)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPermute e f i = f (e.symm i) := rfl

@[simp] theorem lpPermute_one {ι : Type uι} : lpPermute (1 : Equiv.Perm ι) = 1 := by
  ext f i
  rfl

@[simp] theorem lpPermute_mul {ι : Type uι} (e d : Equiv.Perm ι) :
    lpPermute (e * d) = lpPermute e * lpPermute d := by
  ext f i
  rfl

def lpPermuteHom {ι : Type uι} : Equiv.Perm ι →* (lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : ι => ℂ) 2) where
  toFun := lpPermute
  map_one' := lpPermute_one
  map_mul' := lpPermute_mul

def lpPhase {ι : Type uι} (u : ι → unitary ℂ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => (u i : ℂ) * f i, by
    apply memℓp_gen
    simpa only [norm_mul, CStarRing.norm_coe_unitary, one_mul] using
      (lp.memℓp f).summable (by norm_num)⟩
  invFun f := ⟨fun i => (↑(u i)⁻¹ : ℂ) * f i, by
    apply memℓp_gen
    simpa only [norm_mul, CStarRing.norm_coe_unitary, one_mul] using
      (lp.memℓp f).summable (by norm_num)⟩
  left_inv f := by ext i; simp [← mul_assoc, ← Submonoid.coe_mul]
  right_inv f := by ext i; simp [← mul_assoc, ← Submonoid.coe_mul]
  map_add' f g := by ext i; exact mul_add _ _ _
  map_smul' c f := by ext i; exact mul_left_comm _ _ _
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' i, ‖(u i : ℂ) * f i‖ ^ _) = _
    simp only [norm_mul, CStarRing.norm_coe_unitary, one_mul]

@[simp] theorem lpPhase_apply {ι : Type uι} (u : ι → unitary ℂ)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPhase u f i = (u i : ℂ) * f i := rfl

def rotationScalar (θ : ℝ) : unitary ℂ :=
  ⟨Complex.exp (2 * Real.pi * θ * Complex.I), by
    have hn : ‖Complex.exp (2 * Real.pi * θ * Complex.I)‖ = 1 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        Complex.norm_exp_ofReal_mul_I (2 * Real.pi * θ)
    have hs := Complex.sq_norm (Complex.exp (2 * Real.pi * θ * Complex.I))
    rw [hn, one_pow] at hs
    rw [Unitary.mem_iff]
    constructor
    · rw [mul_comm]
      simp only [RCLike.star_def, Complex.mul_conj, ← hs, Complex.ofReal_one]
    · simp only [RCLike.star_def, Complex.mul_conj, ← hs, Complex.ofReal_one]⟩

abbrev RegularHilbert := lp (fun _ : ℤ × ℤ => ℂ) 2
abbrev RegularOperator := RegularHilbert →L[ℂ] RegularHilbert

def regularShift (m : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPermute (Equiv.addLeft (m, 0))

@[simp] theorem regularShift_apply (m : ℤ) (f : RegularHilbert) (a b : ℤ) :
    regularShift m f (a,b) = f (a - m,b) := by
  change f (-m + a, 0 + b) = _
  apply congrArg f
  ext <;> dsimp <;> omega

def regularMagnetic (u : unitary ℂ) (n : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPhase (fun i : ℤ × ℤ => u ^ (n * i.1)) * lpPermute (Equiv.addLeft (0,n))

@[simp] theorem regularMagnetic_apply (u : unitary ℂ) (n : ℤ)
    (f : RegularHilbert) (a b : ℤ) :
    regularMagnetic u n f (a,b) = (↑(u ^ (n * a)) : ℂ) * f (a,b-n) := by
  change _ * f (0 + a, -n + b) = _
  rw [zero_add, show -n + b = b - n by omega]

@[simp] theorem regularShift_zero : regularShift 0 = 1 := by
  ext f ⟨a,b⟩
  simp

@[simp] theorem regularShift_add (m n : ℤ) :
    regularShift (m+n) = regularShift m * regularShift n := by
  ext f ⟨a,b⟩
  change regularShift (m+n) f (a,b) = regularShift m (regularShift n f) (a,b)
  simp only [regularShift_apply]
  apply congrArg f
  ext <;> dsimp; omega

@[simp] theorem regularMagnetic_zero (u : unitary ℂ) : regularMagnetic u 0 = 1 := by
  ext f ⟨a,b⟩
  simp

@[simp] theorem regularMagnetic_add (u : unitary ℂ) (m n : ℤ) :
    regularMagnetic u (m+n) = regularMagnetic u m * regularMagnetic u n := by
  ext f ⟨a,b⟩
  change regularMagnetic u (m+n) f (a,b) = regularMagnetic u m (regularMagnetic u n f) (a,b)
  simp only [regularMagnetic_apply, add_mul, zpow_add, Submonoid.coe_mul, mul_assoc]
  rw [show b - (m+n) = b-m-n by omega]

def regularShiftHom : Multiplicative ℤ →* (RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert) where
  toFun m := regularShift m.toAdd
  map_one' := regularShift_zero
  map_mul' m n := regularShift_add m.toAdd n.toAdd

def regularMagneticHom (u : unitary ℂ) :
    Multiplicative ℤ →* (RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert) where
  toFun n := regularMagnetic u n.toAdd
  map_one' := regularMagnetic_zero u
  map_mul' m n := regularMagnetic_add u m.toAdd n.toAdd

@[simp] theorem regularShift_zpow (m : ℤ) : regularShift 1 ^ m = regularShift m := by
  symm
  simpa only [regularShiftHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_zpow,
    toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one] using
    map_zpow regularShiftHom (Multiplicative.ofAdd 1) m

@[simp] theorem regularMagnetic_zpow (u : unitary ℂ) (n : ℤ) :
    regularMagnetic u 1 ^ n = regularMagnetic u n := by
  symm
  simpa only [regularMagneticHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_zpow,
    toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one] using
    map_zpow (regularMagneticHom u) (Multiplicative.ofAdd 1) n

def regularU : unitary RegularOperator :=
  Unitary.linearIsometryEquiv.symm (regularShift 1)

def regularV (u : unitary ℂ) : unitary RegularOperator :=
  Unitary.linearIsometryEquiv.symm (regularMagnetic u 1)

@[simp] theorem regularU_zpow_apply (m : ℤ) (f : RegularHilbert) (a b : ℤ) :
    ((regularU ^ m : unitary RegularOperator) : RegularOperator) f (a,b) = f (a-m,b) := by
  rw [regularU, ← map_zpow, regularShift_zpow]
  exact regularShift_apply m f a b

@[simp] theorem regularV_zpow_apply (u : unitary ℂ) (n : ℤ)
    (f : RegularHilbert) (a b : ℤ) :
    ((regularV u ^ n : unitary RegularOperator) : RegularOperator) f (a,b) =
      (↑(u ^ (n*a)) : ℂ) * f (a,b-n) := by
  rw [regularV, ← map_zpow, regularMagnetic_zpow]
  exact regularMagnetic_apply u n f a b

@[simp] theorem regularU_apply (f : RegularHilbert) (a b : ℤ) :
    (regularU : RegularOperator) f (a,b) = f (a-1,b) := by
  exact regularShift_apply 1 f a b

@[simp] theorem regularV_apply (u : unitary ℂ) (f : RegularHilbert) (a b : ℤ) :
    (regularV u : RegularOperator) f (a,b) = (↑(u ^ a) : ℂ) * f (a,b-1) := by
  change regularMagnetic u 1 f (a,b) = _
  simpa only [one_mul] using regularMagnetic_apply u 1 f a b

theorem regular_relation (u : unitary ℂ) :
    (regularV u : RegularOperator) * (regularU : RegularOperator) =
      (u : ℂ) • ((regularU : RegularOperator) * (regularV u : RegularOperator)) := by
  ext f ⟨a,b⟩
  change (regularV u : RegularOperator) ((regularU : RegularOperator) f) (a,b) =
    (u : ℂ) * ((regularU : RegularOperator) ((regularV u : RegularOperator) f) (a,b))
  simp only [regularV_apply, regularU_apply, ← mul_assoc]
  congr 1
  change (↑(u ^ a) : ℂ) = ↑(u * u ^ (a-1))
  congr 1
  calc u ^ a = u ^ (1 + (a-1)) := by congr 1; omega
    _ = u * u ^ (a-1) := by rw [zpow_add, zpow_one]

def regularVacuum : RegularHilbert := lp.single 2 (0,0) 1

theorem regular_monomial (u : unitary ℂ) (m n : ℤ) :
    ((regularU ^ m * regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum =
      lp.single 2 (m,n) 1 := by
  ext ⟨a,b⟩
  change ((regularU ^ m : unitary RegularOperator) : RegularOperator)
    (((regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum) (a,b) = _
  simp only [regularU_zpow_apply, regularV_zpow_apply, regularVacuum, lp.single_apply]
  by_cases ha : a=m
  · subst a
    by_cases hb : b=n
    · subst b; simp
    · simp [hb, sub_eq_zero, Prod.mk.injEq]
  · have ham : a-m ≠ 0 := sub_ne_zero.mpr ha
    simp [ham, Prod.mk.injEq, Ne.symm ha]

theorem regular_moments (u : unitary ℂ) (m n : ℤ) :
    inner ℂ regularVacuum
      (((regularU ^ m * regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum) =
      if m=0 ∧ n=0 then 1 else 0 := by
  rw [regular_monomial, regularVacuum, lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq, eq_comm]

theorem regular_cyclic (u : unitary ℂ) :
    (Submodule.span ℂ (Set.range (fun mn : ℤ × ℤ =>
      ((regularU ^ mn.1 * regularV u ^ mn.2 : unitary RegularOperator) : RegularOperator)
        regularVacuum))).topologicalClosure = ⊤ := by
  simp_rw [regular_monomial]
  have heq : (fun mn : ℤ × ℤ => lp.single 2 (mn.1,mn.2) (1 : ℂ)) =
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert) : ℤ × ℤ → RegularHilbert) := by
    funext mn
    rw [← (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).repr_symm_single mn]
    ext i
    simp [LinearIsometryEquiv.symm, LinearIsometryEquiv.refl, lp.single_apply]
  rw [heq]
  exact (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).dense_span

end ContinuousCircleWeight

end

end OAI
