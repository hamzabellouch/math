import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.InvariantPolarization
import OAI.RepresentationTheory.FoulkesSixth.SymPolynomial

namespace OAI

noncomputable section

namespace Foulkes.Rows
universe u
open Module MvPolynomial SymmetricTensor Polarization
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {n : ℕ} (B : Basis (Fin n) ℂ V) (a b : ℕ)

def row {a n : ℕ} (i : Fin a) : SymPolynomial.Poly n →ₐ[ℂ] P a n :=
  rename (fun k => (i,k))

@[simp] lemma row_linear (i : Fin a) (v : V) :
    row i (SymPolynomial.linearPolynomial B v) = rowForm i (B.equivFun v) := by
  simp [row, SymPolynomial.linearPolynomial, rowForm]

@[simp] lemma renameRow_row (σ : Equiv.Perm (Fin a)) (i : Fin a) (p : SymPolynomial.Poly n) :
    renameRow σ (row i p) = row (σ i) p := by
  simp [row, renameRow, rename_rename, Function.comp_def]

def tensorMap : T a (Sym b V) →ₗ[ℂ] P a n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin a) (P a n)).compLinearMap
    (fun i => (row i).toLinearMap.comp (SymPolynomial.polynomial B b)))

@[simp] lemma tensorMap_tprod (v : Fin a → Sym b V) :
    tensorMap B a b (PiTensorProduct.tprod ℂ v) =
      ∏ i, row i (SymPolynomial.polynomial B b (v i)) := by
  simp [tensorMap]

@[simp] lemma tensorMap_powers (v : Fin a → V) :
    tensorMap B a b (PiTensorProduct.tprod ℂ (fun i => power b V (v i))) =
      pureRows b (fun i => B.equivFun (v i)) := by
  simp only [tensorMap_tprod, SymPolynomial.polynomial_power, map_pow, row_linear, pureRows]

def evaluation (w : Fin n → ℂ) : Dual ℂ (Sym b V) :=
  (aeval w).toLinearMap.comp (SymPolynomial.polynomial B b)

@[simp] lemma evaluation_apply (w : Fin n → ℂ) (v : Sym b V) :
    evaluation B b w v = eval w (SymPolynomial.polynomial B b v) := rfl

variable [FiniteDimensional ℂ V]

lemma evaluation_span : Submodule.span ℂ (Set.range (evaluation B b)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  by_contra! h
  have hp : SymPolynomial.polynomial B b v = 0 := by
    apply MvPolynomial.funext
    intro w
    simpa using h (evaluation B b w) ⟨w, rfl⟩
  exact hv ((SymPolynomial.polynomial_injective B b) (hp.trans (map_zero _).symm))

omit [FiniteDimensional ℂ V] in
lemma eval_tensorMap (w : Fin a × Fin n → ℂ) (x : T a (Sym b V)) :
    eval w (tensorMap B a b x) =
      PiTensorProduct.dualDistrib
        (PiTensorProduct.tprod ℂ (fun i : Fin a => evaluation B b (fun k => w (i,k)))) x := by
  have h : (aeval w).toLinearMap.comp (tensorMap B a b) =
      PiTensorProduct.dualDistrib
        (PiTensorProduct.tprod ℂ (fun i : Fin a => evaluation B b (fun k => w (i,k)))) := by
    ext v
    simp [row, MvPolynomial.eval_rename, Function.comp_def]
  exact DFunLike.congr_fun h x

lemma tensorMap_injective : Function.Injective (tensorMap B a b) := by
  refine (LinearMap.ker_eq_bot (R := ℂ) (R₂ := ℂ) (M := T a (Sym b V)) (M₂ := P a n)
    (f := tensorMap B a b)).mp ?_
  refine (LinearMap.ker_eq_bot' (R := ℂ) (R₂ := ℂ) (M := T a (Sym b V)) (M₂ := P a n)
    (f := tensorMap B a b)).mpr ?_
  intro x hx
  have hzero : (LinearMap.applyₗ x).comp
      (PiTensorProduct.dualDistrib (R := ℂ) (M := fun _ : Fin a => Sym b V)) = 0 := by
    apply PiTensorProduct.ext_of_span_eq_top
      (g := fun {_ : Fin a} w => evaluation B b w) (fun _ => evaluation_span B b)
    intro w
    change PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ
      (fun i => evaluation B b (w i))) x = 0
    rw [← eval_tensorMap B a b (fun ik => w ik.1 ik.2), hx, map_zero]
  let : Module.Free ℂ (T a (Sym b V)) := Module.Free.of_basis
    (Basis.piTensorProduct (fun _ : Fin a => Module.Free.chooseBasis ℂ (Sym b V)))
  refine (Module.forall_dual_apply_eq_zero_iff ℂ x).mp ?_
  intro l
  obtain ⟨d, hd⟩ := (PiTensorProduct.dualDistribEquiv (R := ℂ)
      (M := fun _ : Fin a => Sym b V)).surjective l
  have hh := DFunLike.congr_fun hzero d
  change (PiTensorProduct.dualDistribEquiv d) x = 0 at hh
  rwa [hd] at hh

omit [FiniteDimensional ℂ V] in
lemma tensorMap_range : (tensorMap B a b).range = W a n b := by
  have hspan : Submodule.span ℂ (Set.range (fun v : Fin a → V =>
      PiTensorProduct.tprod ℂ (fun i => power b V (v i)))) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (g := fun {_ : Fin a} v => power b V v)
      (fun _ => span_power b V)
  rw [← Submodule.map_top, ← hspan, LinearMap.map_span, W_eq_span_pureRows]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨fun i => B.equivFun (v i), (tensorMap_powers B a b v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨PiTensorProduct.tprod ℂ (fun i => power b V (B.equivFun.symm (v i))),
      ⟨fun i => B.equivFun.symm (v i), rfl⟩, ?_⟩
    simp only [tensorMap_powers, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℂ V] in
lemma tensorMap_perm (σ : Equiv.Perm (Fin a)) (x : T a (Sym b V)) :
    tensorMap B a b (perm a (Sym b V) σ x) = renameRow σ (tensorMap B a b x) := by
  have h : (tensorMap B a b).comp (perm a (Sym b V) σ).toLinearMap =
      (renameRow σ).toLinearMap.comp (tensorMap B a b) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      perm, PiTensorProduct.reindex_tprod, tensorMap_tprod, AlgHom.toLinearMap_apply,
      map_prod, renameRow_row]
    apply Fintype.prod_equiv σ.symm
    intro i
    simp
  exact DFunLike.congr_fun h x

def invariantMap : Sym a (Sym b V) →ₗ[ℂ] P a n :=
  (tensorMap B a b).comp (symmetricTensors a (Sym b V)).subtype

lemma invariantMap_injective : Function.Injective (invariantMap B a b) :=
  (tensorMap_injective B a b).comp Subtype.val_injective

lemma invariantMap_range : (invariantMap B a b).range = R a n b := by
  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    constructor
    · rw [← tensorMap_range B a b]
      exact ⟨x, rfl⟩
    · intro σ
      change renameRow σ (tensorMap B a b x) = tensorMap B a b x
      rw [← tensorMap_perm]
      exact congrArg (tensorMap B a b) (x.property σ)
  · intro p hp
    have hW : p ∈ (tensorMap B a b).range := by rw [tensorMap_range]; exact hp.1
    obtain ⟨x, hx⟩ := hW
    have hs : x ∈ Sym a (Sym b V) := by
      intro σ
      apply tensorMap_injective B a b
      change tensorMap B a b (perm a (Sym b V) σ x) = tensorMap B a b x
      rw [tensorMap_perm, hx]
      exact hp.2 σ
    exact ⟨⟨x, hs⟩, hx⟩

def equiv : Sym a (Sym b V) ≃ₗ[ℂ] R a n b :=
  (LinearEquiv.ofInjective (invariantMap B a b) (invariantMap_injective B a b)).trans
    (LinearEquiv.ofEq _ _ (invariantMap_range B a b))

@[simp] lemma equiv_coe (x : Sym a (Sym b V)) :
    (equiv B a b x : P a n) = invariantMap B a b x := rfl

end Foulkes.Rows

end

end OAI
