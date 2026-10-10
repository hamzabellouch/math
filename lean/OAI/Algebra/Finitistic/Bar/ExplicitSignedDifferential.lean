import OAI.Algebra.Finitistic.Bar.MultibarSigns

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
local notation "A" => TrivSqZeroExt D X

/-- The parity operator is +1 on a D slot and -1 on an X slot. -/
def slotParity : Module.End k A := baseProjection k D X - idealProjection k D X

@[simp] theorem slotParity_base (d : D) : slotParity k D X (inl d) = inl d := by
  simp [slotParity]

@[simp] theorem slotParity_ideal (x : X) : slotParity k D X (inr x) = -inr x := by
  simp [slotParity]

/-- Explicit bar faces with a sign change on crossing a D slot and no sign
change on crossing an X slot. This is defined independently of count transport. -/
def multibarAugmentedDifferential : (n : ℕ) → term k A N (n+1) →ₗ[k] term k A N n
  | 0 => ((action k A N).restrictScalars k).comp
      (TensorProduct.map (slotParity k D X) LinearMap.id)
  | n+1 => (((action k A (term k A N (n+1))).restrictScalars k) -
      TensorProduct.map LinearMap.id (multibarAugmentedDifferential n)).comp
        (TensorProduct.map (slotParity k D X) LinearMap.id)

@[simp] theorem multibarAugmentedDifferential_zero (a : A) (v : N) :
    multibarAugmentedDifferential k D X N 0 (a ⊗ₜ[k] v) = slotParity k D X a • v := rfl

theorem multibarAugmentedDifferential_succ (n : ℕ) (a : A) (v : term k A N (n+1)) :
    multibarAugmentedDifferential k D X N (n+1) (a ⊗ₜ[k] v) =
      slotParity k D X a • v -
        slotParity k D X a ⊗ₜ[k] multibarAugmentedDifferential k D X N n v := rfl

/-- The independent two-sided differential. The first face uses D's right
A-action by projection. All remaining faces use the explicit slot parity recursion. -/
def multibarTwoSidedDifferential (n : ℕ) :
    D ⊗[k] term k A N (n+1) →ₗ[D] D ⊗[k] term k A N n :=
  (action k D (D ⊗[k] term k A N n)).comp
    (AlgebraTensorModule.lTensor D D
      (FreeBaseChange.coefficient (fstHom k D X) (term k A N n))) -
    AlgebraTensorModule.lTensor D D (multibarAugmentedDifferential k D X N n)

/-- Literal endpoint-minus-tail formula; no signed assembly occurs in the definition. -/
theorem multibarTwoSidedDifferential_tmul (n : ℕ) (d : D) (v : term k A N (n+1)) :
    multibarTwoSidedDifferential k D X N n (d ⊗ₜ[k] v) =
      d • FreeBaseChange.coefficient (fstHom k D X) (term k A N n) v -
        d ⊗ₜ[k] multibarAugmentedDifferential k D X N n v := rfl


/-- A zero-length internal D block has no multiplication face: X squared is zero.
The displayed surviving term consists only of the later blocks' faces. -/
theorem multibarAugmented_empty_block (n : ℕ) (x y : X) (v : term k A N n) :
    multibarAugmentedDifferential k D X N (n+1)
      ((inr x : A) ⊗ₜ[k] ((inr y : A) ⊗ₜ[k] v)) =
    (inr x : A) ⊗ₜ[k] multibarAugmentedDifferential k D X N n
      ((inr y : A) ⊗ₜ[k] v) := by
  rw [multibarAugmentedDifferential_succ, slotParity_ideal]
  have ha : (-inr x : A) • ((inr y : A) ⊗ₜ[k] v) = 0 := by
    change ((-inr x : A) * inr y) ⊗ₜ[k] v = 0
    simp only [neg_mul, inr_mul_inr, neg_zero, TensorProduct.zero_tmul]
  rw [ha, zero_sub, TensorProduct.neg_tmul, neg_neg]

/-- At the inflated module endpoint, an X action vanishes. -/
theorem multibarAugmented_ideal_endpoint
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (x : X) (v : N) :
    multibarAugmentedDifferential k D X N 0 ((inr x : A) ⊗ₜ[k] v) = 0 := by
  rw [multibarAugmentedDifferential_zero, slotParity_ideal, _root_.neg_smul, hN, neg_zero]

omit [IsScalarTower k A N] in
/-- Rescaling commutes with the D-action on each word. -/
theorem signedProjection_base_action_word {n r : ℕ} {v : term k A N n}
    (hv : Word k D X N n r v) (d : D) :
    signedProjection k D X N n r ((inl d : A) • v) =
      (inl d : A) • signedProjection k D X N n r v := by
  cases hv with
  | nil v => rfl
  | @base n r v b hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inl,
      signedProjection_base, signedProjection_base]
    have ha : (inl d : A) • ((inl b : A) ⊗ₜ[k] signedProjection k D X N n r v) =
        (inl (d*b) : A) ⊗ₜ[k] signedProjection k D X N n r v := by
      change ((inl d : A) * inl b) ⊗ₜ[k] _ = _
      rw [inl_mul_inl]
    rw [smul_comm (inl d : A) ((-1 : k)^r), ha]
  | @ideal n r v x hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inr,
      signedProjection_ideal_succ, signedProjection_ideal_succ,
      TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inr]

omit [IsScalarTower k A N] in
/-- Multiplying a D slot by X removes its r inversions with the remaining X slots. -/
theorem signedProjection_ideal_action_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N)) {n r : ℕ} {v : term k A N n}
    (hv : Word k D X N n r v) (x : X) :
    signedProjection k D X N n (r+1) ((inr x : A) • v) =
      (-1 : k)^r • ((inr x : A) • signedProjection k D X N n r v) := by
  cases hv with
  | nil v => simp [signedProjection, hN]
  | @base n r v d hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inl,
      signedProjection_ideal_succ, signedProjection_base,
      smul_comm (inr x : A) ((-1 : k)^r), smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inl]
  | @ideal n r v y hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inr, TensorProduct.zero_tmul,
      map_zero, signedProjection_ideal_succ, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inr, TensorProduct.zero_tmul, smul_zero]

/-- Exact sign identity between the literal augmented faces and the ordinary bar
on every homogeneous word. The differential was defined independently above. -/
theorem multibarAugmented_sign_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N)) (n r : ℕ) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    multibarAugmentedDifferential k D X N n (signedProjection k D X N (n+1) r v) =
      (-1 : k)^r • signedProjection k D X N n r (differential k A N n v) := by
  induction n generalizing r with
  | zero =>
    cases hv with
    | base d hv =>
      cases hv
      simp [signedProjection, multibarAugmentedDifferential,
        slotParity_base, differential]
    | ideal x hv =>
      cases hv
      simp [signedProjection, multibarAugmentedDifferential,
        slotParity_ideal, differential, hN]
  | succ n ih =>
    cases hv with
    | @base m r v d hv =>
      rw [signedProjection_base, map_smul, multibarAugmentedDifferential_succ,
        slotParity_base, ih r v hv, differential_succ_tmul, map_sub,
        signedProjection_base_action_word k D X N hv d, signedProjection_base,
        TensorProduct.tmul_smul]
    | @ideal m r v x hv =>
      rw [signedProjection_ideal_succ, multibarAugmentedDifferential_succ,
        slotParity_ideal, ih r v hv, differential_succ_tmul, map_sub,
        signedProjection_ideal_action_word k D X N hN hv x, signedProjection_ideal_succ]
      simp only [TensorProduct.neg_tmul, TensorProduct.tmul_smul, smul_sub, smul_smul]
      rw [← pow_add, show r+1+r=2*r+1 by omega, pow_add, pow_mul]
      simp [pow_succ]
      exact _root_.neg_smul (inr x : A) (signedProjection k D X N (n+1) r v)


omit [Module A N] [IsScalarTower k A N] in
/-- The leading endpoint has the same prescribed rescaling. -/
theorem coefficient_signed_word (n r : ℕ) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N n)
        (signedProjection k D X N (n+1) r v) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (FreeBaseChange.coefficient (fstHom k D X) (term k A N n) v) := by
  cases hv with
  | base d hv =>
    rw [signedProjection_base, map_smul, FreeBaseChange.coefficient_tmul,
      FreeBaseChange.coefficient_tmul]
    rfl
  | ideal x hv =>
    rw [signedProjection_ideal_succ, FreeBaseChange.coefficient_tmul,
      FreeBaseChange.coefficient_tmul]
    simp

/-- Equality of the independently defined two-sided faces and the shifted signed
ordinary bar differential, on every homogeneous pure tensor. -/
theorem multibarTwoSided_sign_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (n r : ℕ) (d : D) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    multibarTwoSidedDifferential k D X N n
        (twoSidedSignedProjection k D X N (n+1) r (d ⊗ₜ[k] v)) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n (d ⊗ₜ[k] v)) := by
  change multibarTwoSidedDifferential k D X N n
      (d ⊗ₜ[k] signedProjection k D X N (n+1) r v) = _
  rw [multibarTwoSidedDifferential_tmul, coefficient_signed_word k D X N n r v hv,
    multibarAugmented_sign_word k D X N hN n r v hv, twoSidedDifferential_tmul,
    map_sub, map_smul, smul_sub, TensorProduct.tmul_smul,
    smul_comm d ((-1 : k)^r)]
  rfl

/-- The sign comparison extends to the whole count submodule by linearity. -/
theorem multibarTwoSided_sign
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (n r : ℕ) {z : D ⊗[k] term k A N (n+1)}
    (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n (twoSidedSignedProjection k D X N (n+1) r z) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n z) := by
  have h : twoSidedWeight k D X N (n+1) r ≤
      ((multibarTwoSidedDifferential k D X N n).comp
          (twoSidedSignedProjection k D X N (n+1) r) -
        (-1 : k)^r • (twoSidedSignedProjection k D X N n r).comp
          (twoSidedDifferential k A D N (fstHom k D X) n)).ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨d,v,hv,rfl⟩
    exact sub_eq_zero.mpr (multibarTwoSided_sign_word k D X N hN n r d v hv)
  exact sub_eq_zero.mp (h hz)
end DerivedBar.SquareZero

end

end OAI
