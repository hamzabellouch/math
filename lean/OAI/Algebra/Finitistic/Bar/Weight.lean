import OAI.Algebra.Finitistic.Bar.TwoSided
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
namespace SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- (TrivSqZeroExt D X) pure bar word with precisely r factors in the square-zero ideal. -/
inductive Word : (n r : ℕ) → term k (TrivSqZeroExt D X) N n → Prop
  | nil (v : N) : Word 0 0 v
  | base {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (d : D) (h : Word n r v) :
      Word (n+1) r ((inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v)
  | ideal {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (x : X) (h : Word n r v) :
      Word (n+1) (r+1) ((inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v)

/-- The homogeneous subspace, defined by actual tensors rather than formal signs. -/
def weight (n r : ℕ) : Submodule k (term k (TrivSqZeroExt D X) N n) :=
  Submodule.span k {v | Word k D X N n r v}

private theorem map_span_mem {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (s : Set V) (t : Submodule k W)
    (h : ∀ v ∈ s, g v ∈ t) {v : V} (hv : v ∈ Submodule.span k s) : g v ∈ t := by
  have hle : Submodule.span k s ≤ t.comap g := Submodule.span_le.mpr h
  exact hle hv

variable {k D X N}

theorem base_tmul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) r :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inl d)) _ _
    (fun _ h => Submodule.subset_span (Word.base d h)) hv

theorem ideal_tmul_mem {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) (r+1) :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inr x)) _ _
    (fun _ h => Submodule.subset_span (Word.ideal x h)) hv

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- Degree-zero multiplication preserves the number of ideal factors. -/
theorem base_smul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) • v ∈ weight k D X N n r := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inl d)) _ _ _ hv
  intro v h
  cases h with
  | nil v => exact Submodule.subset_span (Word.nil _)
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inl, weight]
    exact Submodule.subset_span (Word.base (d*b) hb)
  | ideal x hx =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inr, weight]
    exact Submodule.subset_span (Word.ideal (d • x) hx)

/-- Degree-one multiplication raises the count, with square-zero products vanishing. -/
theorem ideal_smul_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) • v ∈ weight k D X N n (r+1) := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inr x)) _ _ _ hv
  intro v h
  cases h with
  | nil v =>
    simp only [Algebra.lsmul_coe, hN]

    exact Submodule.zero_mem _
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inl, weight]
    exact Submodule.subset_span (Word.ideal (MulOpposite.op b • x) hb)
  | ideal y hy =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inr, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

/-- Every face of the augmented algebra bar differential preserves the X-count. -/
theorem differential_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    (n r : ℕ) {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    differential k (TrivSqZeroExt D X) N n v ∈ weight k D X N n r := by
  induction n generalizing r with
  | zero =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N 0).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      cases h with
      | nil v =>
        exact Submodule.subset_span (Word.nil _)
    | ideal x h =>
      cases h with
      | nil v =>
        simp only [LinearMap.coe_restrictScalars,
          differential_zero_tmul k (TrivSqZeroExt D X) N, hN]
        exact Submodule.zero_mem _
  | succ n ih =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N (n+1)).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (base_smul_mem d (Submodule.subset_span h))
        (base_tmul_mem d (ih _ (Submodule.subset_span h)))
    | ideal x h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (ideal_smul_mem hN x (Submodule.subset_span h))
        (ideal_tmul_mem x (ih _ (Submodule.subset_span h)))

variable (k D X N)

/-- The actual complex formed by the fixed-count homogeneous bar subspaces. -/
def weightComplex (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0) (r : ℕ) :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (weight k D X N n r))
    (fun n => ModuleCat.ofHom
      (((differential k (TrivSqZeroExt D X) N n).restrictScalars k).restrict
        (fun v hv => differential_mem hN n r hv)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (differential_sq k (TrivSqZeroExt D X) N n) v)
end SquareZero
end DerivedBar

end

end OAI
