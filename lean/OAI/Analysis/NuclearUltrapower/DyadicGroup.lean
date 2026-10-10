import OAI.Analysis.NuclearUltrapower.Model

namespace OAI

section

noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter

namespace NuclearUltrapower

@[simp] theorem dyadicTwo_val : (dyadicTwo : Dyadic) = 2 := by
  simp [dyadicTwo, IsUnit.unit_spec]

/-! The exact integral subgroup and dilation in the tensor-norm formulation. -/

abbrev IntegralVector3 := Fin 3 → ℤ

def integralAction : SL3Z →* MulAut (Multiplicative IntegralVector3) where
  toFun M := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' M).toAddEquiv
  map_one' := by ext v i; simp
  map_mul' M N := by ext v i; simp [map_mul]

abbrev IntegralGroup := SemidirectProduct (Multiplicative IntegralVector3) SL3Z integralAction

def integralTranslation (v : IntegralVector3) : IntegralGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd v)

def integralTheta : Monoid.End IntegralGroup where
  toFun g := ⟨Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd), g.right⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ((2 : ℤ) • (g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right h.left.toAdd)) =
        Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right ((2 : ℤ) • h.left.toAdd))
      simp only [smul_add, map_smul]
    · rfl

@[simp] theorem integralTheta_left (g : IntegralGroup) :
    (integralTheta g).left.toAdd = (2 : ℤ) • g.left.toAdd := rfl

@[simp] theorem integralTheta_right (g : IntegralGroup) :
    (integralTheta g).right = g.right := rfl

theorem integralTheta_injective : Function.Injective integralTheta := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : IntegralGroup => x.left.toAdd i) he
    change 2 * g.left.toAdd i = 2 * h.left.toAdd i at hi
    omega
  · simpa only [integralTheta_right] using congrArg (fun x : IntegralGroup => x.right) he

@[simp] theorem integralTheta_translation (v : IntegralVector3) :
    integralTheta (integralTranslation v) = integralTranslation ((2 : ℤ) • v) := rfl

@[simp] theorem integralTheta_pow_translation (n : ℕ) (v : IntegralVector3) :
    (integralTheta ^ n) (integralTranslation v) = integralTranslation ((2 : ℤ) ^ n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Monoid.End.coe_mul, Function.comp_apply, ih, integralTheta_translation]
      congr 1
      simp only [pow_succ', mul_smul]

/-- The inclusion is literally integer coordinate inclusion into Z[1/2]. -/
def integralInclusion : IntegralGroup →* G where
  toFun g := ⟨Multiplicative.ofAdd (fun i => (g.left.toAdd i : Dyadic)), (g.right, 1)⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change ((g.left.toAdd i + (Matrix.SpecialLinearGroup.toLin' g.right) h.left.toAdd i : ℤ) : Dyadic) =
        (g.left.toAdd i : Dyadic) + (dilationAction (g.right, 1)) (fun j => (h.left.toAdd j : Dyadic)) i
      simp [dilationAction, matrixAction, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.mulVec, dotProduct, LinearEquiv.smulOfUnit]
    · rfl

/-- The stable letter t=(0,I,1). -/
def stableLetter : G :=
  SemidirectProduct.inr (1, Multiplicative.ofAdd (1 : ℤ))

/-- The source group law implements exactly multiplication of translations by two. -/
theorem stableLetter_conjugation (g : IntegralGroup) :
    stableLetter * integralInclusion g * stableLetter⁻¹ = integralInclusion (integralTheta g) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    change 0 + ((dilationAction (1, Multiplicative.ofAdd (1 : ℤ)))
      (fun j => (g.left.toAdd j : Dyadic))) i =
      ((2 * g.left.toAdd i : ℤ) : Dyadic) +
      (dilationAction (g.right, 1) (0 : Vector3)) i
    simp [dilationAction, matrixAction, LinearEquiv.smulOfUnit, Units.smul_def]
  · change (1, Multiplicative.ofAdd (1 : ℤ)) * (g.right, 1) =
      (g.right, 1) * (1, Multiplicative.ofAdd (1 : ℤ))
    simp

/-- The integral copy is genuinely a subgroup, not merely a homomorphic image. -/
theorem integralInclusion_injective : Function.Injective integralInclusion := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : G => x.left.toAdd i) he
    change (g.left.toAdd i : Dyadic) = (h.left.toAdd i : Dyadic) at hi
    apply IsLocalization.injective (S := Dyadic)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (by norm_num : (2 : ℤ) ≠ 0)))
    simpa only [eq_intCast] using hi
  · exact congrArg (fun x : G => x.right.1) he

abbrev Residue3 := Fin 3 → ZMod 2

def residue (g : IntegralGroup) : Residue3 := fun i => (g.left.toAdd i : ZMod 2)

def residueMatrix (M : SL3Z) : Residue3 ≃ₗ[ZMod 2] Residue3 :=
  Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) M)

theorem residue_mul (g h : IntegralGroup) :
    residue (g * h) = residue g + residueMatrix g.right (residue h) := by
  funext i
  simp [residue, integralAction, residueMatrix, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.mulVec, dotProduct]

@[simp] theorem residue_one : residue 1 = 0 := by ext; simp [residue]

@[simp] theorem residue_theta (g : IntegralGroup) : residue (integralTheta g) = 0 := by
  ext i
  change ((2 * g.left.toAdd i : ℤ) : ZMod 2) = 0
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [htwo]

theorem mem_theta_range_iff (g : IntegralGroup) :
    g ∈ integralTheta.range ↔ residue g = 0 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact residue_theta h
  · intro hg
    have hd (i : Fin 3) : (2 : ℤ) ∣ g.left.toAdd i := by
      have hi := congrFun hg i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
    refine ⟨⟨Multiplicative.ofAdd (fun i => g.left.toAdd i / 2), g.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change 2 * (g.left.toAdd i / 2) = g.left.toAdd i
      exact Int.mul_ediv_cancel' (hd i)
    · rfl

theorem leftRel_theta_iff (g h : IntegralGroup) :
    QuotientGroup.leftRel integralTheta.range g h ↔ residue g = residue h := by
  rw [QuotientGroup.leftRel_apply, mem_theta_range_iff]
  have he : residue (g⁻¹) + residueMatrix (g⁻¹).right (residue g) = 0 := by
    rw [← residue_mul, inv_mul_cancel, residue_one]
  rw [residue_mul]
  constructor
  · intro hz
    have hi := add_left_cancel (hz.trans he.symm)
    exact (residueMatrix (g⁻¹).right).injective hi |>.symm
  · intro hgh
    rwa [← hgh]

/-- The eight left cosets are precisely the three translation residues. -/
def thetaCosetEquiv : (IntegralGroup ⧸ integralTheta.range) ≃ Residue3 where
  toFun := Quotient.lift residue (fun g h hgh => (leftRel_theta_iff g h).mp hgh)
  invFun a := Quotient.mk'' (integralTranslation (fun i => (a i).val))
  left_inv q := by
    induction q using Quotient.inductionOn with | h g =>
      apply Quotient.sound
      apply (leftRel_theta_iff _ _).mpr
      ext i
      simp [residue, integralTranslation]
  right_inv a := by
    ext i
    simp [residue, integralTranslation]

theorem integralTheta_index : integralTheta.range.index = 8 := by
  rw [Subgroup.index_eq_card, Nat.card_congr thetaCosetEquiv]
  simp [Residue3, Nat.card_eq_fintype_card]

instance : integralTheta.range.FiniteIndex := ⟨by rw [integralTheta_index]; norm_num⟩

end NuclearUltrapower

end
end

end OAI
