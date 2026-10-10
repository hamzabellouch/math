import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Module

namespace Problem346
namespace SymmetricLift

variable {κ : Type*} {n : ℕ}

private def tupleExponent (f : Fin n → κ) : κ →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private lemma tupleExponent_apply (f : Fin n → κ) (k : κ) :
    tupleExponent f k = Fintype.card {i // f i = k} := by
  classical
  rw [Fintype.card_subtype]
  simp only [tupleExponent, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id]

private lemma exists_perm_of_exponent_eq (f g : Fin n → κ)
    (h : tupleExponent f = tupleExponent g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g (σ i) = f i := by
  classical
  have hc (k : κ) : Fintype.card {i // f i = k} = Fintype.card {i // g i = k} := by
    simpa only [tupleExponent_apply] using congrArg (fun d : κ →₀ ℕ => d k) h
  let e (k : κ) : {i // f i = k} ≃ {i // g i = k} :=
    Fintype.equivOfCardEq (hc k)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

private def liftValues (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W) (d : κ →₀ ℕ) : W :=
  if h : ∃ f : Fin n → κ, tupleExponent f = d then
    T (fun i => b (Classical.choose h i)) else 0

private lemma liftValues_tuple (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (f : Fin n → κ) : liftValues b T (tupleExponent f) = T (fun i => b (f i)) := by
  let h : ∃ g : Fin n → κ, tupleExponent g = tupleExponent f := ⟨f, rfl⟩
  rw [liftValues, dite_eq_left h]
  obtain ⟨σ, hσ⟩ := exists_perm_of_exponent_eq (Classical.choose h) f (Classical.choose_spec h)
  convert hT σ (fun i => b (f i)) using 1
  congr 1
  funext i
  rw [hσ]

private def liftOnAlgebra (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W) :
    SymmetricAlgebra ℂ V →ₗ[ℂ] W :=
  ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T)).comp
    (SymmetricAlgebra.equivMvPolynomial b).toLinearMap

private lemma liftOnAlgebra_basis (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (f : Fin n → κ) :
    liftOnAlgebra b T (symMonomialRaw n V (fun i => b (f i))) = T (fun i => b (f i)) := by
  have hp : (∏ i, MvPolynomial.X (f i) : MvPolynomial κ ℂ) =
      MvPolynomial.monomial (tupleExponent f) 1 := by
    simp only [tupleExponent, MvPolynomial.monomial_sum_one, MvPolynomial.X]
  change ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T))
    ((SymmetricAlgebra.equivMvPolynomial b) (∏ i, SymmetricAlgebra.ι ℂ V (b (f i)))) = _
  rw [map_prod]
  simp only [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [hp]
  change ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T))
    ((MvPolynomial.basisMonomials κ ℂ) (tupleExponent f)) = _
  rw [Basis.constr_basis, liftValues_tuple b T hT]

private lemma liftOnAlgebra_monomial (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (v : Fin n → V) :
    liftOnAlgebra b T (symMonomialRaw n V v) = T v := by
  let M : MultilinearMap ℂ (fun _ : Fin n => V) (SymmetricAlgebra ℂ V) :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
      (fun _ => SymmetricAlgebra.ι ℂ V)
  have h : (liftOnAlgebra b T).compMultilinearMap M = T := by
    apply Basis.ext_multilinear (fun _ => b)
    intro f
    exact liftOnAlgebra_basis b T hT f
  exact congrArg (fun S : MultilinearMap ℂ (fun _ : Fin n => V) W => S v) h

end SymmetricLift

/-- A symmetric multilinear map descends to the homogeneous symmetric-power submodule. -/
theorem exists_symPow_lift {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v) :
    ∃ L : SymPow n V →ₗ[ℂ] W, ∀ v, L (symMonomial n V v) = T v := by
  let b := Module.Free.chooseBasis ℂ V
  refine ⟨(SymmetricLift.liftOnAlgebra b T).domRestrict (symPowSubmodule n V), ?_⟩
  intro v
  exact SymmetricLift.liftOnAlgebra_monomial b T hT v

/-- A chosen linear descent of a symmetric multilinear map. -/
def symPowLift {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v) :
    SymPow n V →ₗ[ℂ] W :=
  Classical.choose (exists_symPow_lift T hT)

@[simp] theorem symPowLift_symMonomial {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (v : Fin n → V) : symPowLift T hT (symMonomial n V v) = T v :=
  Classical.choose_spec (exists_symPow_lift T hT) v

namespace SymmetricLift

/-- Linear maps out of a symmetric power are determined by products. -/
theorem linearMap_ext {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {f g : SymPow n V →ₗ[ℂ] W}
    (h : ∀ v, f (symMonomial n V v) = g (symMonomial n V v)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_eq_span f g rfl).2
  rintro ⟨x, ⟨v, rfl⟩⟩
  exact h v

end SymmetricLift

/-- The submodule of multilinear maps invariant under permutations of their arguments. -/
def symmetricMultilinearSubmodule (n : ℕ) (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    Submodule ℂ (MultilinearMap ℂ (fun _ : Fin n => V) W) where
  carrier := {T | ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V),
    T (fun i => v (σ i)) = T v}
  zero_mem' := by simp
  add_mem' := by
    intro T U hT hU σ v
    simp only [add_apply, hT σ v, hU σ v]
  smul_mem' := by
    intro c T hT σ v
    simp only [smul_apply, hT σ v]

/-- Descent from symmetric multilinear maps is linear in the map being descended. -/
def symPowLiftLinear (n : ℕ) (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    symmetricMultilinearSubmodule n V W →ₗ[ℂ] (SymPow n V →ₗ[ℂ] W) where
  toFun T := symPowLift T.val T.property
  map_add' T U := by
    apply SymmetricLift.linearMap_ext
    intro v
    exact (symPowLift_symMonomial (T + U).val (T + U).property v).trans
      (congrArg₂ (fun left right : W => left + right)
        (symPowLift_symMonomial T.val T.property v).symm
        (symPowLift_symMonomial U.val U.property v).symm)
  map_smul' c T := by
    apply SymmetricLift.linearMap_ext
    intro v
    exact (symPowLift_symMonomial (c • T).val (c • T).property v).trans
      (congrArg (c • ·) (symPowLift_symMonomial T.val T.property v).symm)

@[simp] theorem symPowLiftLinear_symMonomial {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : symmetricMultilinearSubmodule n V W) (v : Fin n → V) :
    symPowLiftLinear n V W T (symMonomial n V v) = T.val v :=
  symPowLift_symMonomial T.val T.property v

end Problem346

end

end OAI
