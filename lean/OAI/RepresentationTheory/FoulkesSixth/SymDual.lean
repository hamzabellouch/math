import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.SymTensors

namespace OAI

noncomputable section

namespace Foulkes.SymmetricTensor
universe u v
open scoped TensorProduct
open Module
variable (n : ℕ) {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma pair_perm (σ : Equiv.Perm (Fin n)) (d : T n (Dual ℂ V)) (x : T n V) :
    PiTensorProduct.dualDistrib (perm n (Dual ℂ V) σ d) x =
    PiTensorProduct.dualDistrib d (perm n V σ.symm x) := by
  have h : (PiTensorProduct.dualDistrib (R := ℂ) (M := fun _ : Fin n => V)).comp
      (perm n (Dual ℂ V) σ).toLinearMap =
      (perm n V σ.symm).toLinearMap.dualMap.comp PiTensorProduct.dualDistrib := by
    ext f x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, perm,
      PiTensorProduct.reindex_tprod, PiTensorProduct.dualDistrib_apply,
      LinearMap.dualMap_apply, Equiv.symm_symm]
    have hp := Equiv.prod_comp σ.symm (fun i => f i (x (σ i)))
    convert hp using 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [σ.apply_symm_apply]
  exact DFunLike.congr_fun (DFunLike.congr_fun h d) x

lemma pair_map (f : V →ₗ[ℂ] W) (d : T n (Dual ℂ W)) (x : T n V) :
    PiTensorProduct.dualDistrib (PiTensorProduct.map (fun _ : Fin n => f.dualMap) d) x =
    PiTensorProduct.dualDistrib d (PiTensorProduct.map (fun _ : Fin n => f) x) := by
  have h : (PiTensorProduct.dualDistrib (R := ℂ) (M := fun _ : Fin n => V)).comp
      (PiTensorProduct.map (fun _ : Fin n => f.dualMap)) =
      (PiTensorProduct.map (fun _ : Fin n => f)).dualMap.comp PiTensorProduct.dualDistrib := by
    ext d x
    simp
  exact DFunLike.congr_fun (DFunLike.congr_fun h d) x

def pairing : Sym n (Dual ℂ V) →ₗ[ℂ] Dual ℂ (Sym n V) :=
  (symmetricTensors n V).subtype.dualMap.comp
    (PiTensorProduct.dualDistrib.comp (symmetricTensors n (Dual ℂ V)).subtype)

@[simp] lemma pairing_apply (d : Sym n (Dual ℂ V)) (x : Sym n V) :
    pairing n d x = PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) (x : T n V) := rfl

@[simp] lemma pairing_power (d : Dual ℂ V) (v : V) :
    pairing n (power n (Dual ℂ V) d) (power n V v) = d v ^ n := by
  simp [pairing_apply, PiTensorProduct.dualDistrib_apply]

lemma pairing_map (f : V →ₗ[ℂ] W) (d : Sym n (Dual ℂ W)) (x : Sym n V) :
    pairing n (symMap n f.dualMap d) x = pairing n d (symMap n f x) :=
  pair_map n f d x

variable [FiniteDimensional ℂ V]

def pairingInv (l : Dual ℂ (Sym n V)) : Sym n (Dual ℂ V) :=
  ⟨PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V)), by
    intro σ
    apply PiTensorProduct.dualDistribEquiv.injective
    apply LinearMap.ext
    intro x
    change PiTensorProduct.dualDistrib
      (perm n (Dual ℂ V) σ (PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V)))) x =
      PiTensorProduct.dualDistrib
        (PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V))) x
    rw [pair_perm]
    change PiTensorProduct.dualDistribEquiv
      (PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V))) (perm n V σ.symm x) =
      PiTensorProduct.dualDistribEquiv
        (PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V))) x
    simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, project_perm]⟩

lemma pairing_pairingInv (l : Dual ℂ (Sym n V)) : pairing n (pairingInv n l) = l := by
  ext x
  change PiTensorProduct.dualDistribEquiv
    (PiTensorProduct.dualDistribEquiv.symm (l.comp (project n V))) (x : T n V) = l x
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg l (project_coe n V x)

omit [FiniteDimensional ℂ V] in
lemma pair_project (d : Sym n (Dual ℂ V)) (x : T n V) :
    pairing n d (project n V x) = PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) x := by
  have hinv (σ : Equiv.Perm (Fin n)) :
      PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) (perm n V σ x) =
      PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) x := by
    have hh := pair_perm n σ.symm (d : T n (Dual ℂ V)) x
    rw [show perm n (Dual ℂ V) σ.symm d = d from d.property σ.symm] at hh
    simpa using hh.symm
  change PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) (average n V x) = _
  rw [average_apply, map_smul, map_sum]
  simp only [hinv, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma pairing_injective : Function.Injective (pairing n (V := V)) := by
  intro d e h
  apply Subtype.ext
  apply PiTensorProduct.dualDistribEquiv.injective
  apply LinearMap.ext
  intro x
  have hh := DFunLike.congr_fun h (project n V x)
  change PiTensorProduct.dualDistrib (d : T n (Dual ℂ V)) x =
    PiTensorProduct.dualDistrib (e : T n (Dual ℂ V)) x
  simpa only [pair_project] using hh

def dualEquiv : Sym n (Dual ℂ V) ≃ₗ[ℂ] Dual ℂ (Sym n V) :=
  LinearEquiv.ofBijective (pairing n) ⟨pairing_injective n,
    fun l => ⟨pairingInv n l, pairing_pairingInv n l⟩⟩

@[simp] lemma dualEquiv_apply (d : Sym n (Dual ℂ V)) (x : Sym n V) :
    dualEquiv n d x = pairing n d x := rfl

end Foulkes.SymmetricTensor

end

end OAI
