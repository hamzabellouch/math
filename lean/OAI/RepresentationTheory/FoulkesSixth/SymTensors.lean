import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.Diagonal

namespace OAI

noncomputable section

open scoped TensorProduct
namespace Foulkes
universe u v w

def symmetricTensors (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule ℂ (⨂[ℂ] (_ : Fin n), V) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin n),
    PiTensorProduct.reindex ℂ (fun _ : Fin n => V) σ x = x}
  zero_mem' := by intro σ; simp
  add_mem' := by intro x y hx hy σ; simp only [map_add, hx σ, hy σ]
  smul_mem' := by intro c x hx σ; simp only [map_smul, hx σ]

abbrev Sym (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :=
  symmetricTensors n V

def symMap (n : ℕ) {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) : Sym n V →ₗ[ℂ] Sym n W :=
  (PiTensorProduct.map (fun _ : Fin n => f)).restrict fun x hx σ => by
    rw [← PiTensorProduct.map_reindex]
    rw [hx σ]

namespace SymmetricTensor

variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

abbrev T := ⨂[ℂ] (_ : Fin n), V

def perm (σ : Equiv.Perm (Fin n)) : T n V ≃ₗ[ℂ] T n V :=
  PiTensorProduct.reindex ℂ (fun _ : Fin n => V) σ

lemma perm_mul (σ τ : Equiv.Perm (Fin n)) (x : T n V) :
    perm n V σ (perm n V τ x) = perm n V (σ * τ) x := by
  exact PiTensorProduct.reindex_reindex _ _ _

def average : T n V →ₗ[ℂ] T n V :=
  (n.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin n), (perm n V σ).toLinearMap

lemma average_apply (x : T n V) :
    average n V x = (n.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin n), perm n V σ x := by
  simp [average]

lemma average_invariant (x : T n V) : average n V x ∈ Sym n V := by
  intro τ
  change perm n V τ (average n V x) = average n V x
  simp only [average_apply, map_smul, map_sum, perm_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => perm n V σ x)

lemma average_perm (σ : Equiv.Perm (Fin n)) (x : T n V) :
    average n V (perm n V σ x) = average n V x := by
  simp only [average_apply, perm_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ) (fun τ => perm n V τ x)

lemma average_eq {x : T n V} (hx : x ∈ Sym n V) : average n V x = x := by
  change ∀ σ : Equiv.Perm (Fin n), perm n V σ x = x at hx
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [average_apply, hx, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]

def project : T n V →ₗ[ℂ] Sym n V :=
  (average n V).codRestrict _ (average_invariant n V)

@[simp] lemma project_coe (x : Sym n V) : project n V x = x := by
  apply Subtype.ext
  exact average_eq n V x.property

@[simp] lemma project_perm (σ : Equiv.Perm (Fin n)) (x : T n V) :
    project n V (perm n V σ x) = project n V x := by
  apply Subtype.ext
  exact average_perm n V σ x

def power (v : V) : Sym n V :=
  ⟨PiTensorProduct.tprod ℂ (fun _ : Fin n => v), by intro σ; simp⟩

@[simp] lemma coe_power (v : V) :
    (power n V v : T n V) = PiTensorProduct.tprod ℂ (fun _ : Fin n => v) := rfl

@[simp] lemma project_power (v : V) :
    project n V (PiTensorProduct.tprod ℂ (fun _ : Fin n => v)) = power n V v :=
  project_coe n V (power n V v)

theorem span_power : Submodule.span ℂ (Set.range (power n V)) = ⊤ := by
  apply top_unique
  intro x hx
  by_contra hnot
  obtain ⟨l, hne, hl⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hlpower (v : V) : l (power n V v) = 0 := by
    have hh : l (power n V v) ∈ (Submodule.span ℂ (Set.range (power n V))).map l :=
      Submodule.mem_map.mpr ⟨_, Submodule.subset_span ⟨v, rfl⟩, rfl⟩
    rwa [hl, Submodule.mem_bot] at hh
  let F : MultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
    (l.comp (project n V)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hF : F = 0 := by
    apply Diagonal.eq_zero_of_symmetric_of_diagonal
    · intro σ v
      change l (project n V (PiTensorProduct.tprod ℂ (fun i => v (σ i)))) =
        l (project n V (PiTensorProduct.tprod ℂ v))
      simpa [perm] using congrArg l
        (project_perm n V σ.symm (PiTensorProduct.tprod ℂ v))
    · intro v
      change l (project n V (PiTensorProduct.tprod ℂ (fun _ : Fin n => v))) = 0
      rw [project_power, hlpower]
  have hlin : l.comp (project n V) = 0 := by
    apply PiTensorProduct.ext
    exact hF
  exact hne (by have hh := DFunLike.congr_fun hlin (x : T n V); simpa using hh)

end SymmetricTensor

@[simp] lemma symMap_power (n : ℕ) {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (v : V) :
    symMap n f (SymmetricTensor.power n V v) = SymmetricTensor.power n W (f v) := by
  apply Subtype.ext
  exact PiTensorProduct.map_tprod _ _

lemma symMap_ext (n : ℕ) {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {f g : Sym n V →ₗ[ℂ] W}
    (h : ∀ v : V, f (SymmetricTensor.power n V v) = g (SymmetricTensor.power n V v)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ (SymmetricTensor.span_power n V)).mpr
  rintro ⟨_, ⟨v, rfl⟩⟩
  exact h v

@[simp] lemma symMap_comp (n : ℕ) {V : Type u} {W : Type v} {U : Type w}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    symMap n (g.comp f) = (symMap n g).comp (symMap n f) := by
  apply symMap_ext
  intro v
  simp

@[simp] lemma symMap_id (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    symMap n (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  apply symMap_ext
  intro v
  simp

end Foulkes

end

end OAI
