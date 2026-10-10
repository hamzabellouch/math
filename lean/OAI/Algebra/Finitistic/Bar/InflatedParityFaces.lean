import OAI.Algebra.Finitistic.Bar.ExplicitSignedDifferential
import OAI.Algebra.Finitistic.Bimodule.BimoduleBar

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X

/-- The original D module is inflated by the actual projection, without a new action hypothesis. -/
@[instance_reducible] def inflatedModule : Module A N := Module.compHom N
  { toFun := fun a => a.fst
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
section Compatible
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hbase : ∀ (d : D) (v : N), (inl d : TrivSqZeroExt D X) • v = d • v)

/-- Literal insertion of D slots into square-zero-extension slots. -/
def baseEmbed : (n : ℕ) → term k D N n →ₗ[k] term k A N n
  | 0 => LinearMap.id
  | n+1 => TensorProduct.map (inlAlgHom k D X).toLinearMap (baseEmbed n)

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
@[simp] theorem baseEmbed_tmul (n : ℕ) (d : D) (v : term k D N n) :
    baseEmbed k D X N (n+1) (d ⊗ₜ[k] v) = (inl d : A) ⊗ₜ[k] baseEmbed k D X N n v := rfl

include hbase in
omit [IsScalarTower k D N] [IsScalarTower k A N] in
/-- D-equivariance of insertion, including the inflated module endpoint. -/
theorem baseEmbed_smul (n : ℕ) (d : D) (v : term k D N n) :
    baseEmbed k D X N n (d • v) = (inl d : A) • baseEmbed k D X N n v := by
  cases n with
  | zero => exact (hbase d v).symm
  | succ n =>
    induction v using TensorProduct.inductionOn with
    | tmul b v =>
      change (inl (d*b) : A) ⊗ₜ[k] baseEmbed k D X N n v =
        ((inl d : A)*inl b) ⊗ₜ[k] baseEmbed k D X N n v
      rw [inl_mul_inl]
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]

include hbase in
/-- All-D faces in the independently defined parity recursion are exactly
ordinary D-bar faces. This is an equality of actual maps on tensors. -/
theorem parity_baseEmbed (n : ℕ) (v : term k D N (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N n (baseEmbed k D X N (n+1) v) =
      baseEmbed k D X N n (DerivedBar.differential k D N n v) := by
  induction n with
  | zero =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [baseEmbed_tmul, SquareZero.multibarAugmentedDifferential_zero,
        SquareZero.slotParity_base]
      exact hbase d v
    | add v w hv hw => simp only [map_add, hv, hw]
  | succ n ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [baseEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
        SquareZero.slotParity_base, ih, DerivedBar.differential_succ_tmul,
        map_sub, baseEmbed_smul k D X N hbase, baseEmbed_tmul]
    | add v w hv hw => simp only [map_add, hv, hw]

/-- Literal insertion of a leading X and its following D block. -/
def idealEmbed (n : ℕ) : X ⊗[k] term k D N n →ₗ[k] term k A N (n+1) :=
  TensorProduct.map ((inrHom D X).restrictScalars k) (baseEmbed k D X N n)

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
@[simp] theorem idealEmbed_tmul (n : ℕ) (x : X) (v : term k D N n) :
    idealEmbed k D X N n (x ⊗ₜ[k] v) = (inr x : A) ⊗ₜ[k] baseEmbed k D X N n v := rfl

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
/-- The D action on a leading X is its original left bimodule action. -/
theorem idealEmbed_base_smul (n : ℕ) (d : D) (v : X ⊗[k] term k D N n) :
    idealEmbed k D X N n (d • v) = (inl d : A) • idealEmbed k D X N n v := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    change (inr (d • x) : A) ⊗ₜ[k] baseEmbed k D X N n v =
      ((inl d : A) * inr x) ⊗ₜ[k] baseEmbed k D X N n v
    rw [inl_mul_inr]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
/-- An inner bar beginning with X is annihilated by the square-zero ideal.
This is the boundary fact needed when the following D block has length zero. -/
theorem idealEmbed_ideal_smul (n : ℕ) (x : X) (v : X ⊗[k] term k D N n) :
    (inr x : A) • idealEmbed k D X N n v = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul y v =>
    change ((inr x : A) * inr y) ⊗ₜ[k] baseEmbed k D X N n v = 0
    rw [inr_mul_inr, TensorProduct.zero_tmul]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
/-- Multiplying X by the first D entry is precisely the original right
D action used by the two-sided bar collapse map. -/
theorem ideal_action_baseEmbed (n : ℕ) (x : X) (v : term k D N (n+1)) :
    (inr x : A) • baseEmbed k D X N (n+1) v =
      idealEmbed k D X N n
        (BimoduleTensor.collapse k D X (term k D N n) (x ⊗ₜ[k] v)) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [baseEmbed_tmul, BimoduleTensor.collapse_tmul, idealEmbed_tmul]
    change ((inr x : A) * inl d) ⊗ₜ[k] baseEmbed k D X N n v =
      (inr (MulOpposite.op d • x) : A) ⊗ₜ[k] baseEmbed k D X N n v
    rw [inr_mul_inl]
  | add v w hv hw => simp only [map_add, smul_add, TensorProduct.tmul_add, hv, hw]

include hbase in
/-- The inner X bar is minus the augmented slot-parity recursion. The leading
D two-sided differential contributes the other minus sign in the full multibar. -/
theorem parity_idealEmbed (n : ℕ) (v : X ⊗[k] term k D N (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (n+1) (idealEmbed k D X N (n+1) v) =
      -idealEmbed k D X N n (BimoduleTensor.barDifferential k D X N n v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    rw [idealEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal, parity_baseEmbed k D X N hbase,
      BimoduleTensor.barDifferential_tmul, map_sub, idealEmbed_tmul]
    have hneg : (-inr x : A) • baseEmbed k D X N (n+1) v =
        -((inr x : A) • baseEmbed k D X N (n+1) v) :=
      _root_.neg_smul (inr x : A) (baseEmbed k D X N (n+1) v)
    rw [hneg, ideal_action_baseEmbed, TensorProduct.neg_tmul, sub_neg_eq_add, neg_sub]
    exact add_comm _ _
  | add v w hv hw => simp only [map_add, hv, hw, neg_add]

omit [Module D N] [IsScalarTower k D N] in
/-- The missing outgoing face at the module end of an empty X bar is zero. -/
theorem parity_idealEmbed_zero
    (hN : ∀ (x : X) (v : N), (inr x : A) • v = 0) (v : X ⊗[k] N) :
    SquareZero.multibarAugmentedDifferential k D X N 0 (idealEmbed k D X N 0 v) = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    exact SquareZero.multibarAugmented_ideal_endpoint k D X N
      hN x v
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

end Compatible

/-- Direct specialization to the original module inflated along A -> D.
The inflation is a local instance for this N, never a blanket action on bar terms. -/
theorem inflated_parity_idealEmbed (n : ℕ) (v : X ⊗[k] term k D N (n+1)) :
    letI : Module A N := inflatedModule D X N
    letI : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
      (fun a v => IsScalarTower.algebraMap_smul D a v)
    SquareZero.multibarAugmentedDifferential k D X N (n+1) (idealEmbed k D X N (n+1) v) =
      -idealEmbed k D X N n (BimoduleTensor.barDifferential k D X N n v) := by
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact parity_idealEmbed k D X N (fun _ _ => rfl) n v

theorem inflated_parity_baseEmbed (n : ℕ) (v : term k D N (n+1)) :
    letI : Module A N := inflatedModule D X N
    letI : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
      (fun a v => IsScalarTower.algebraMap_smul D a v)
    SquareZero.multibarAugmentedDifferential k D X N n (baseEmbed k D X N (n+1) v) =
      baseEmbed k D X N n (DerivedBar.differential k D N n v) := by
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact parity_baseEmbed k D X N (fun _ _ => rfl) n v

theorem inflated_parity_idealEmbed_zero (v : X ⊗[k] N) :
    letI : Module A N := inflatedModule D X N
    letI : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
      (fun a v => IsScalarTower.algebraMap_smul D a v)
    SquareZero.multibarAugmentedDifferential k D X N 0 (idealEmbed k D X N 0 v) = 0 := by
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact parity_idealEmbed_zero k D X N (fun _ v => zero_smul D v) v
end DerivedBar.ParityBridge

end

end OAI
