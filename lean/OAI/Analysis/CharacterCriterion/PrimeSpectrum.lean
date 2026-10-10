import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.RepresentationTheory

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam
namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


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


instance : StarModule ℂ (Raw A B) := inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))


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


@[simp]
lemma liftRaw_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl


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
end KirchbergRordam
namespace KirchbergRordam.ScalarCenter
variable {E B : Type*} [CStarAlgebra E] [CStarAlgebra B] [Nontrivial B]

theorem exists_character (φ : E →⋆ₐ[ℂ] B)
    (hφ : ∀ x, ∃ z : ℂ, φ x = algebraMap ℂ B z) :
    ∃ χ : E →ₐ[ℂ] ℂ, ∀ x, φ x = algebraMap ℂ B (χ x) := by
  classical
  choose χ hχ using hφ
  have inj := FaithfulSMul.algebraMap_injective ℂ B
  let f : E →ₐ[ℂ] ℂ := {
    toFun := χ
    map_zero' := inj (by rw [← hχ,map_zero,map_zero])
    map_one' := inj (by rw [← hχ,map_one,map_one])
    map_add' := fun x y => inj (by rw [← hχ,map_add,map_add,← hχ,← hχ])
    map_mul' := fun x y => inj (by rw [← hχ,map_mul,map_mul,← hχ,← hχ])
    commutes' := fun z => inj (by rw [← hχ]; exact φ.commutes z) }
  exact ⟨f,hχ⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
theorem exists_evaluation (φ : C(X,ℂ) →⋆ₐ[ℂ] B)
    (hφ : ∀ f, ∃ z : ℂ, φ f = algebraMap ℂ B z) :
    ∃ t : X, ∀ f, φ f = algebraMap ℂ B (f t) := by
  obtain ⟨χ,hχ⟩ := exists_character φ hφ
  obtain ⟨t,ht⟩ := (WeakDual.CharacterSpace.continuousMapEval_bijective X ℂ).surjective
    (WeakDual.CharacterSpace.equivAlgHom.symm χ)
  refine ⟨t, fun f => ?_⟩
  have hf : f t = χ f := congrArg (fun g : WeakDual.characterSpace ℂ C(X,ℂ) => g f) ht
  rw [hχ,hf]
end KirchbergRordam.ScalarCenter
namespace KirchbergRordam.PrimeDimensionDrop
open scoped CStarAlgebra ComplexOrder
variable {p q : ℕ}
lemma scalar_commute (f : C(unitInterval,ℂ)) (a : Algebra p q) :
    Commute (scalar p q f) a := by
  change scalar p q f*a=a*scalar p q f
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change ((f t) • (1 : Fiber p q)) * a.val t = a.val t * ((f t) • (1 : Fiber p q))
  simpa only [_root_.Algebra.algebraMap_eq_smul_one] using _root_.Algebra.commutes (f t) ((a : C(unitInterval,Fiber p q)) t)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

theorem scalar_evaluation (π : Algebra p q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ z : ℂ, T=z • 1) :
    ∃ t : unitInterval, ∀ f, π (scalar p q f)=algebraMap ℂ (H →L[ℂ] H) (f t) := by
  apply ScalarCenter.exists_evaluation (π.comp (scalar p q))
  intro f
  obtain ⟨z,hz⟩ := hπ (π (scalar p q f)) (fun a => (scalar_commute f a).map π)
  exact ⟨z,hz.trans (_root_.Algebra.algebraMap_eq_smul_one z).symm⟩

omit [Nontrivial H] in


theorem kills_evaluation_kernel (π : Algebra p q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (t : unitInterval) (hπ : ∀ f, π (scalar p q f)=algebraMap ℂ (H →L[ℂ] H) (f t))
    (a : Algebra p q) (ha : (a : C(unitInterval,Fiber p q)) t=0) : π a=0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let f : C(unitInterval,ℂ) := ⟨fun s => (↑(ε/(ε+‖(a : C(unitInterval,Fiber p q)) s‖)) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.add (map_continuous (a : C(unitInterval,Fiber p q))).norm)
      (fun s => ne_of_gt (add_pos_of_pos_of_nonneg hε (norm_nonneg _))))⟩
  have hft : f t=1 := by simp [f,ha,ne_of_gt hε]
  have hfix : π (scalar p q f*a)=π a := by
    rw [map_mul,hπ,hft,map_one,one_mul]
  have hn : ‖scalar p q f*a‖≤ε := by
    change ‖((scalar p q f*a : Algebra p q) : C(unitInterval,Fiber p q))‖≤ε
    apply (ContinuousMap.norm_le _ hε.le).mpr
    intro s
    change ‖((f s) • (1 : Fiber p q))*(a : C(unitInterval,Fiber p q)) s‖≤ε
    rw [smul_mul_assoc,one_mul,norm_smul]
    change ‖((ε/(ε+‖(a : C(unitInterval,Fiber p q)) s‖) : ℝ) : ℂ)‖*‖(a : C(unitInterval,Fiber p q)) s‖≤ε
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hε
      (add_pos_of_pos_of_nonneg hε (norm_nonneg _)))]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hε (norm_nonneg _))).mpr
    nlinarith [sq_nonneg ε]
  have := (NonUnitalStarAlgHom.norm_apply_le π (scalar p q f*a)).trans hn
  simpa only [zero_add,hfix] using this
end KirchbergRordam.PrimeDimensionDrop
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct Matrix Kronecker CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def unit (i : ι) (j : ι) : Mat ι := CStarMatrix.ofMatrix (Matrix.single i j 1)
lemma decompose (a : Mat ι) : (∑ ij : ι×ι, a ij.1 ij.2 • unit ij.1 ij.2)=a := by
  change (∑ ij : ι×ι, a ij.1 ij.2 • Matrix.single ij.1 ij.2 1)=a
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
  simp [← Finset.univ_product_univ,Finset.sum_product,ite_and]

def kroneckerRaw : (Mat ι ⊗[ℂ] Mat κ) →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.liftRaw (MatrixTensor.leftMatrix (ι:=ι) (κ:=κ)) (MatrixTensor.rightMatrix (ι:=ι) (κ:=κ)) (fun a b => legs_commute a b)
@[simp] lemma kroneckerRaw_tmul (a : Mat ι) (b : Mat κ) :
    kroneckerRaw (a ⊗ₜ[ℂ] b)=CStarMatrix.ofMatrix (Matrix.kronecker a b) := legs_product a b

def kroneckerInverse : Mat (ι×κ) →ₗ[ℂ] (Mat ι ⊗[ℂ] Mat κ) where
  toFun c := ∑ ij : ι×ι, ∑ kl : κ×κ,
    c (ij.1,kl.1) (ij.2,kl.2) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2)
  map_add' a b := by simp [Finset.sum_add_distrib,add_smul]
  map_smul' z a := by simp [Finset.smul_sum,mul_smul]

lemma kroneckerInverse_tmul (a : Mat ι) (b : Mat κ) :
    kroneckerInverse (kroneckerRaw (a ⊗ₜ[ℂ] b))=a ⊗ₜ[ℂ] b := by
  rw [kroneckerRaw_tmul]
  let ca : ι×ι → ℂ := fun ij => a ij.1 ij.2
  let cb : κ×κ → ℂ := fun kl => b kl.1 kl.2
  change (∑ ij : ι×ι, ∑ kl : κ×κ,
    (ca ij * cb kl) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2))=_
  have he (ij : ι×ι) (kl : κ×κ) :
      (ca ij * cb kl) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2) =
        (ca ij • unit ij.1 ij.2) ⊗ₜ[ℂ] (cb kl • unit kl.1 kl.2) := by
    exact (TensorProduct.smul_tmul_smul _ _ _ _).symm
  simp_rw [he,← TensorProduct.tmul_sum]
  rw [← TensorProduct.sum_tmul]
  exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (decompose a) (decompose b)

lemma kroneckerRaw_injective : Function.Injective (kroneckerRaw (ι:=ι) (κ:=κ)) := by
  apply Function.LeftInverse.injective (g:=kroneckerInverse)
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => exact kroneckerInverse_tmul a b
end KirchbergRordam.MatrixTensor
namespace KirchbergRordam.StarRangeFactor
variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
  [StarRing A] [StarRing B] [StarRing C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
  [instStarModuleℂA : StarModule ℂ A] [instStarModuleℂB : StarModule ℂ B] [StarModule ℂ C]

def descend (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] B)
    (hk : ∀ a, f a=0 → g a=0) : f.range →⋆ₐ[ℂ] B := by
  classical
  let r : f.range → A := fun y => y.property.choose
  have hr (y : f.range) : f (r y)=y.val := y.property.choose_spec
  have he (a : A) (y : f.range) (h : f a=y.val) : g a=g (r y) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hk
    rw [map_sub,h,hr,sub_self]
  exact {
    toFun := fun y => g (r y)
    map_zero' := (he 0 0 (map_zero f)).symm.trans (map_zero g)
    map_one' := (he 1 1 (map_one f)).symm.trans (map_one g)
    map_add' := fun x y => (he (r x+r y) (x+y) (by rw [map_add,hr,hr]; rfl)).symm.trans (map_add g _ _)
    map_mul' := fun x y => (he (r x*r y) (x*y) (by rw [map_mul,hr,hr]; rfl)).symm.trans (map_mul g _ _)
    commutes' := fun z => (he (algebraMap ℂ A z) (algebraMap ℂ f.range z) (f.commutes z)).symm.trans (g.commutes z)
    map_star' := fun x => (he (star (r x)) (star x) (by rw [map_star,hr]; rfl)).symm.trans (map_star g _) }

omit instStarModuleℂA instStarModuleℂB in
@[simp] lemma descend_apply.{contextLevel1, contextLevel2, contextLevel3}
    {A : Type contextLevel1}
    {B : Type contextLevel2}
    {C : Type contextLevel3}
    [Ring A]
    [Ring B]
    [Ring C]
    [StarRing A]
    [StarRing B]
    [StarRing C]
    [Algebra ℂ A]
    [Algebra ℂ B]
    [Algebra ℂ C]
    [StarModule ℂ A]
    [StarModule ℂ B]
    [StarModule ℂ C]
    (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] B)
    (hk : ∀ a, f a=0 → g a=0) (a : A) :
    descend f g hk ⟨f a,⟨a,rfl⟩⟩=g a := by
  dsimp [descend]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hk
  rw [map_sub]
  exact sub_eq_zero.mpr (Exists.choose_spec (show ∃ x, f x=f a from ⟨a,rfl⟩))
end KirchbergRordam.StarRangeFactor
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
instance matrixFinite : FiniteDimensional ℂ (Mat ι) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix ι ι ℂ))
instance subClosed (S : StarSubalgebra ℂ (Mat ι)) : IsClosed (S : Set (Mat ι)) :=
  S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
instance subCStar (S : StarSubalgebra ℂ (Mat ι)) : CStarAlgebra S :=
  StarSubalgebra.cstarAlgebra S

def subKronecker (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ)) :
    (S ⊗[ℂ] T) →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.liftRaw (MatrixTensor.leftMatrix.comp S.subtype) (MatrixTensor.rightMatrix.comp T.subtype)
    (fun a b => legs_commute a.val b.val)

lemma subKronecker_eq (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    (x : S ⊗[ℂ] T) : subKronecker S T x=
      kroneckerRaw (TensorProduct.map S.subtype.toLinearMap T.subtype.toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => rw [TensorProduct.map_tmul]; rfl

lemma subKronecker_injective (S : StarSubalgebra ℂ (Mat ι))
    (T : StarSubalgebra ℂ (Mat κ)) : Function.Injective (subKronecker S T) := by
  intro x y h
  rw [subKronecker_eq,subKronecker_eq] at h
  exact TensorProduct.map_injective_of_flat_flat S.subtype.toLinearMap T.subtype.toLinearMap
    Subtype.val_injective Subtype.val_injective (kroneckerRaw_injective h)


theorem norm_liftRaw_sub_le (S : StarSubalgebra ℂ (Mat ι))
    (T : StarSubalgebra ℂ (Mat κ)) {B : Type*} [CStarAlgebra B]
    (φ : S →⋆ₐ[ℂ] B) (ψ : T →⋆ₐ[ℂ] B)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (x : S ⊗[ℂ] T) :
    ‖MaxTensor.liftRaw φ ψ hc (MaxTensor.rawEquiv x)‖ ≤ ‖subKronecker S T x‖ := by
  let f := subKronecker S T
  let g := (MaxTensor.liftRaw φ ψ hc).comp MaxTensor.rawEquiv.toStarAlgHom
  have hk (a : S ⊗[ℂ] T) (ha : f a=0) : g a=0 := by
    have hz : a=0 := subKronecker_injective S T (ha.trans (map_zero f).symm)
    rw [hz,map_zero]
  let d := StarRangeFactor.descend f g hk
  have hn := NonUnitalStarAlgHom.norm_apply_le d ⟨f x,⟨x,rfl⟩⟩
  change ‖d ⟨f x,⟨x,rfl⟩⟩‖ ≤ ‖f x‖ at hn
  rw [StarRangeFactor.descend_apply] at hn
  exact hn
end KirchbergRordam.MatrixTensor
namespace KirchbergRordam.StarRangeFactor
variable {A B C D E : Type*} [Ring A] [Ring B] [Ring C] [Ring D] [Ring E]
  [StarRing A] [StarRing B] [StarRing C] [StarRing D] [StarRing E]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] [Algebra ℂ D] [Algebra ℂ E]
  [instStarModuleℂA : StarModule ℂ A] [instStarModuleℂB : StarModule ℂ B] [StarModule ℂ C] [StarModule ℂ D] [StarModule ℂ E]
lemma descend_commute (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] E)
    (h : B →⋆ₐ[ℂ] D) (j : B →⋆ₐ[ℂ] E)
    (hk : ∀ a, f a=0 → g a=0) (hl : ∀ b, h b=0 → j b=0)
    (hc : ∀ a b, Commute (g a) (j b))
    (a : f.range) (b : h.range) : Commute (descend f g hk a) (descend h j hl b) := by
  obtain ⟨a',ha⟩ := a.property
  obtain ⟨b',hb⟩ := b.property
  have heL : (⟨f a',⟨a',rfl⟩⟩:f.range)=a := Subtype.ext ha
  have heR : (⟨h b',⟨b',rfl⟩⟩:h.range)=b := Subtype.ext hb
  rw [← heL,← heR,descend_apply,descend_apply]
  exact hc a' b'
end KirchbergRordam.StarRangeFactor

namespace KirchbergRordam.MatrixTensor
open scoped CStarAlgebra ComplexOrder TensorProduct
variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def fiberMap (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ) :
    MaxTensor.Algebra A B →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.lift (MatrixTensor.leftMatrix.comp eL) (MatrixTensor.rightMatrix.comp eR)
    (fun a b => legs_commute (eL a) (eR b))
@[simp] lemma fiberMap_tmul (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ) (a : A) (b : B) :
    fiberMap eL eR (MaxTensor.of (a ⊗ₜ[ℂ] b))=MatrixTensor.leftMatrix (eL a)*MatrixTensor.rightMatrix (eR b) :=
  MaxTensor.lift_of_tmul _ _ _ _ _


theorem representation_bound
    (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ)
    (π : MaxTensor.Algebra A B →⋆ₐ[ℂ] R)
    (hkL : ∀ a, eL a=0 → π (MaxTensor.includeLeft a)=0)
    (hkR : ∀ b, eR b=0 → π (MaxTensor.includeRight b)=0) :
    ∀ x, ‖π x‖≤‖fiberMap eL eR x‖ := by
  let πL := π.comp MaxTensor.includeLeft
  let πR := π.comp MaxTensor.includeRight
  let dL := StarRangeFactor.descend eL πL hkL
  let dR := StarRangeFactor.descend eR πR hkR
  have hd : ∀ a b, Commute (dL a) (dR b) :=
    StarRangeFactor.descend_commute eL πL eR πR hkL hkR
      (fun a b => (MaxTensor.legs_commute a b).map π)
  let E := TensorProduct.map eL.rangeRestrict.toLinearMap eR.rangeRestrict.toLinearMap
  have hdL (a : A) : dL (eL.rangeRestrict a)=πL a := StarRangeFactor.descend_apply eL πL hkL a
  have hdR (b : B) : dR (eR.rangeRestrict b)=πR b := StarRangeFactor.descend_apply eR πR hkR b
  have hπ (x : A ⊗[ℂ] B) :
      MaxTensor.liftRaw dL dR hd (MaxTensor.rawEquiv (E x)) =
        π (MaxTensor.of (MaxTensor.rawEquiv x)) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a b =>
      change dL (eL.rangeRestrict a) * dR (eR.rangeRestrict b) =
        π (MaxTensor.of (a ⊗ₜ[ℂ] b))
      rw [hdL,hdR]
      rw [MaxTensor.of_tmul,map_mul]
      rfl
  have he (x : A ⊗[ℂ] B) : subKronecker eL.range eR.range (E x)=
      fiberMap eL eR (MaxTensor.of (MaxTensor.rawEquiv x)) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul a b =>
      change subKronecker eL.range eR.range (E (a ⊗ₜ[ℂ] b)) =
        fiberMap eL eR (MaxTensor.of (a ⊗ₜ[ℂ] b))
      rw [fiberMap_tmul]
      rfl
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (map_continuous π).norm (map_continuous (fiberMap eL eR)).norm
  | ih x =>
    change ‖π (MaxTensor.of (MaxTensor.rawEquiv (MaxTensor.rawEquiv.symm x)))‖ ≤
      ‖fiberMap eL eR (MaxTensor.of (MaxTensor.rawEquiv (MaxTensor.rawEquiv.symm x)))‖
    rw [← hπ,← he]
    exact norm_liftRaw_sub_le eL.range eR.range dL dR hd (E (MaxTensor.rawEquiv.symm x))
end KirchbergRordam.MatrixTensor

namespace KirchbergRordam
open scoped CStarAlgebra
lemma irreducible_central_evaluation {A : Type*} [CStarAlgebra A]
    (π : IrreducibleRepresentation A) (φ : C(unitInterval,ℂ) →⋆ₐ[ℂ] A)
    (hc : ∀ f a, Commute (φ f) a) :
    ∃ t, ∀ f, π.representation (φ f)=algebraMap ℂ _ (f t) := by
  apply ScalarCenter.exists_evaluation (π.representation.comp φ)
  intro f
  obtain ⟨z,hz⟩ := π.scalar_commutant (π.representation (φ f))
    (fun a => (hc f a).map π.representation)
  exact ⟨z,hz.trans (_root_.Algebra.algebraMap_eq_smul_one z).symm⟩
end KirchbergRordam
namespace KirchbergRordam.MaxTensor
open scoped CStarAlgebra
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

lemma commute_of_legs (π : Algebra A B →⋆ₐ[ℂ] C) (T : C)
    (hL : ∀ a, Commute T (π (includeLeft a)))
    (hR : ∀ b, Commute T (π (includeRight b))) :
    ∀ x, Commute T (π x) := by
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    change IsClosed {x | T * π x = π x * T}
    exact isClosed_eq (continuous_const.mul (map_continuous π))
      ((map_continuous π).mul continuous_const)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B,
        Commute T (π (of (rawEquiv tensor))) from this x
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
    | tmul a b =>
      change Commute T (π (of (a ⊗ₜ[ℂ] b)))
      rw [of_tmul, map_mul]
      exact (hL a).mul_right (hR b)
end KirchbergRordam.MaxTensor

end

end OAI
