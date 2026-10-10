import OAI.Analysis.CharacterCriterion.Pauli

namespace OAI


noncomputable section
open scoped TensorProduct

namespace KirchbergRordam.GenericRW
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionStar : Star (Completion R) := ⟨Completion.map (star : R → R)⟩

@[simp]
lemma star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe star_isometry.uniformContinuous x

instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map

instance completionStarRing : StarRing (Completion R) where
  star_involutive x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_star.comp continuous_star) continuous_id
    | ih x => simp only [star_coe, star_star]
  star_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_mul, star_coe, star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_add, star_coe, star_add]

instance completionNormedStarGroup : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simp only [star_coe, Completion.norm_coe, norm_star, le_refl]

variable [NormedAlgebra ℂ R] [StarModule ℂ R]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le

instance completionStarModule : StarModule ℂ (Completion R) where
  star_smul z x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (continuous_star.comp (continuous_const_smul z))
        ((continuous_const_smul (star z)).comp continuous_star)
    | ih x =>
      rw [← Completion.coe_smul, star_coe, star_smul, Completion.coe_smul, star_coe]

end StarCompletion

namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


structure CrossSeminorm extends Seminorm ℂ (A ⊗[ℂ] B) where
  mul_le : ∀ x y, toSeminorm (x * y) ≤ toSeminorm x * toSeminorm y
  star_eq : ∀ x, toSeminorm (star x) = toSeminorm x
  cstar_eq : ∀ x, toSeminorm (star x * x) = toSeminorm x * toSeminorm x
  tmul_le : ∀ a b, toSeminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖

instance : Inhabited (CrossSeminorm A B) := ⟨{
  toSeminorm := 0
  mul_le := by simp
  star_eq := by simp
  cstar_eq := by simp
  tmul_le := by intro a b; simp only [zero_apply]; positivity }⟩

variable {A B}

lemma bounded_at (x : A ⊗[ℂ] B) :
    ∃ C : ℝ, ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact ⟨‖a‖ * ‖b‖, fun p => p.tmul_le a b⟩
  | add x y hx hy =>
      obtain ⟨C, hC⟩ := hx
      obtain ⟨D, hD⟩ := hy
      exact ⟨C + D, fun p => (map_add_le_add p.toSeminorm x y).trans
        (add_le_add (hC p) (hD p))⟩

lemma bounded : BddAbove (Set.range (CrossSeminorm.toSeminorm (A := A) (B := B))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C, hC⟩ := bounded_at x
  exact ⟨C, by rintro _ ⟨p, rfl⟩; exact hC p⟩


def seminorm : Seminorm ℂ (A ⊗[ℂ] B) := ⨆ p : CrossSeminorm A B, p.toSeminorm

lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x = ⨆ p : CrossSeminorm A B, p.toSeminorm x :=
  Seminorm.iSup_apply bounded

lemma le_seminorm (p : CrossSeminorm A B) (x : A ⊗[ℂ] B) :
    p.toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  exact le_ciSup (by obtain ⟨C, hC⟩ := bounded_at x; exact ⟨C, by
    rintro _ ⟨p, rfl⟩; exact hC p⟩) p

lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C) : seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h

lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    seminorm (x * y) ≤ seminorm x * seminorm y := by
  apply seminorm_le
  intro p
  exact (p.mul_le x y).trans (mul_le_mul (le_seminorm p x) (le_seminorm p y)
    (apply_nonneg p.toSeminorm y) (apply_nonneg seminorm x))

lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x) = seminorm x := by
  rw [seminorm_apply, seminorm_apply]
  congr 1
  funext p
  exact p.star_eq x

lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x * x) = seminorm x * seminorm x := by
  apply le_antisymm
  · simpa only [seminorm_star] using seminorm_mul_le (star x) x
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x * x)) := by
      apply seminorm_le
      intro p
      apply (Real.le_sqrt (apply_nonneg p.toSeminorm x) (apply_nonneg seminorm _)).mpr
      simpa only [← p.cstar_eq x, pow_two] using le_seminorm p (star x * x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this

lemma seminorm_tmul_le (a : A) (b : B) : seminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ :=
  seminorm_le fun p => p.tmul_le a b


def Raw (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] := A ⊗[ℂ] B

instance : Ring (Raw A B) := inferInstanceAs (Ring (A ⊗[ℂ] B))
instance : Algebra ℂ (Raw A B) := inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))
instance : StarRing (Raw A B) := inferInstanceAs (StarRing (A ⊗[ℂ] B))
instance : StarModule ℂ (Raw A B) := inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))

def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)

def rawRingSeminorm : RingSeminorm (Raw A B) where
  __ := (seminorm (A := A) (B := B)).toAddGroupSeminorm
  mul_le' := seminorm_mul_le

instance : SeminormedRing (Raw A B) := rawRingSeminorm.toSeminormedRing

instance : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le

instance : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le

@[simp]
lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl


abbrev Algebra (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] :=
  UniformSpace.Completion (Raw A B)

instance : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge

instance : CStarAlgebra (Algebra A B) where


def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm

@[simp]
lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x


def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })

def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })

lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {C : Type*} [CStarAlgebra C]


def liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Raw A B →⋆ₐ[ℂ] C where
  toAlgHom := _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h
  map_star' x := by
    change _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h (star x) =
      star (_root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [star_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change φ (star a) * ψ (star b) = star (φ a * ψ b)
      rw [star_mul, ← map_star, ← map_star]
      exact h (star a) (star b)

@[simp]
lemma liftRaw_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl


def representationSeminorm (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : CrossSeminorm A B where
  toSeminorm := (normSeminorm ℂ C).comp (liftRaw φ ψ h).toLinearMap
  mul_le x y := by
    change ‖liftRaw φ ψ h (rawEquiv x * rawEquiv y)‖ ≤
      ‖liftRaw φ ψ h (rawEquiv x)‖ * ‖liftRaw φ ψ h (rawEquiv y)‖
    rw [map_mul]
    exact norm_mul_le _ _
  star_eq x := by
    change ‖liftRaw φ ψ h (star (rawEquiv x))‖ = ‖liftRaw φ ψ h (rawEquiv x)‖
    rw [map_star, norm_star]
  cstar_eq x := by
    change ‖liftRaw φ ψ h (star (rawEquiv x) * rawEquiv x)‖ =
      ‖liftRaw φ ψ h (rawEquiv x)‖ * ‖liftRaw φ ψ h (rawEquiv x)‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]
  tmul_le a b := by
    change ‖liftRaw φ ψ h (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖
    rw [liftRaw_tmul]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (NonUnitalStarAlgHom.norm_apply_le φ a) (NonUnitalStarAlgHom.norm_apply_le ψ b)
      (norm_nonneg _) (norm_nonneg _))

lemma norm_liftRaw_le (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    ‖liftRaw φ ψ h x‖ ≤ ‖x‖ :=
  le_seminorm (representationSeminorm φ ψ h) x

lemma continuous_liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Continuous (liftRaw φ ψ h) := by
  exact ((liftRaw φ ψ h).toLinearMap.mkContinuous 1
    (fun x => by change ‖liftRaw φ ψ h x‖ ≤ 1 * ‖x‖
                 simpa only [one_mul] using norm_liftRaw_le φ ψ h x)).continuous


def lift (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Algebra A B →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
      (continuous_liftRaw φ ψ h) (algebraMap ℂ (Raw A B) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (liftRaw φ ψ h).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
        (continuous_liftRaw φ ψ h) (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
          (continuous_liftRaw φ ψ h) (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (liftRaw φ ψ h) x

@[simp]
lemma lift_of (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    lift φ ψ h (of x) = liftRaw φ ψ h x :=
  UniformSpace.Completion.extensionHom_coe (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h) x

@[simp]
lemma lift_of_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    lift φ ψ h (of (a ⊗ₜ[ℂ] b)) = φ a * ψ b :=
  (lift_of φ ψ h (rawEquiv (a ⊗ₜ[ℂ] b))).trans (liftRaw_tmul φ ψ h a b)


open scoped CStarAlgebra

@[simp]
lemma of_tmul (a : A) (b : B) :
    of (a ⊗ₜ[ℂ] b) = includeLeft (B := B) a * includeRight (A := A) b := by
  change of (rawEquiv (a ⊗ₜ[ℂ] b)) =
    of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))
  rw [← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


@[ext]
theorem hom_ext {f g : Algebra A B →⋆ₐ[ℂ] C}
    (hL : f.comp includeLeft = g.comp includeLeft)
    (hR : f.comp includeRight = g.comp includeRight) : f = g := by
  apply DFunLike.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (map_continuous f) (map_continuous g)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B, f (of (rawEquiv tensor)) = g (of (rawEquiv tensor))
      from this x
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change f (of (a ⊗ₜ[ℂ] b)) = g (of (a ⊗ₜ[ℂ] b))
      rw [of_tmul, map_mul, map_mul]
      exact congrArg₂ (· * ·) (DFunLike.congr_fun hL a) (DFunLike.congr_fun hR b)

@[simp]
lemma lift_includeLeft (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeLeft = φ := by
  ext a
  change lift φ ψ h (of (a ⊗ₜ[ℂ] (1 : B))) = φ a
  rw [lift_of_tmul, map_one, mul_one]

@[simp]
lemma lift_includeRight (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeRight = ψ := by
  ext b
  change lift φ ψ h (of ((1 : A) ⊗ₜ[ℂ] b)) = ψ b
  rw [lift_of_tmul, map_one, one_mul]


theorem existsUnique_lift (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) :
    ∃! f : Algebra A B →⋆ₐ[ℂ] C, f.comp includeLeft = φ ∧ f.comp includeRight = ψ := by
  refine ⟨lift φ ψ h, ⟨lift_includeLeft _ _ _, lift_includeRight _ _ _⟩, ?_⟩
  intro f hf
  exact hom_ext (hf.1.trans (lift_includeLeft _ _ _).symm)
    (hf.2.trans (lift_includeRight _ _ _).symm)


universe u


structure CStarPack where
  carrier : Type u
  inst : CStarAlgebra carrier

attribute [instance] CStarPack.inst
instance : CoeSort CStarPack (Type u) := ⟨CStarPack.carrier⟩


def powerPack (D : Type u) [CStarAlgebra D] : ℕ → CStarPack.{u}
  | 0 => ⟨D, inferInstance⟩
  | n + 1 => ⟨Algebra D (powerPack D n), inferInstance⟩


abbrev Power (D : Type u) [CStarAlgebra D] (m : ℕ+) : Type u :=
  powerPack D (m.val - 1)

end MaxTensor
end KirchbergRordam.GenericRW
end

end OAI
