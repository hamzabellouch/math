import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuotientAlg

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def crossDifference (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  ∏ i, ∏ x : Fin (d i), ∏ y : Fin (e i),
    (X (Sum.inl ⟨i,x⟩) - X (Sum.inr ⟨i,y⟩))

lemma prod_sub_perm {α β R : Type*} [Fintype α] [Fintype β] [CommRing R]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (l : α → R) (r : β → R) :
    (∏ x : α, (∏ y : β, (l (σ x) - r (τ y)))) = ∏ x : α, (∏ y : β, (l x - r y)) := by
  calc
    _ = ∏ x : α, (∏ y : β, (l (σ x) - r y)) := by
      apply Finset.prod_congr rfl
      intro x hx
      exact Equiv.prod_comp τ (fun y => l (σ x) - r y)
    _ = _ := Equiv.prod_comp σ (fun x => ∏ y : β, (l x - r y))

omit [DecidableEq I] in
lemma rename_crossDifference (d e : I → ℕ)
    (h : ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) → ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i)))) :
    rename h (crossDifference d e) =
      ∏ i,∏ x : Fin (d i),∏ y : Fin (e i), (X (h (Sum.inl ⟨i,x⟩))-X (h (Sum.inr ⟨i,y⟩))) := by
  simp only [crossDifference,map_prod,map_sub,rename_X]

omit [DecidableEq I] in
lemma crossDifference_symmetric (d e : I → ℕ) (σ : (∀ i,Equiv.Perm (Fin (d i))) ×
    (∀ i,Equiv.Perm (Fin (e i)))) :
    rename (sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i))) σ)
      (crossDifference d e) = crossDifference d e := by
  refine (rename_crossDifference d e _).trans ?_
  exact Finset.prod_congr rfl (fun i hi =>
    prod_sub_perm (R := MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ)
      (σ.1 i) (σ.2 i) (fun x => X (Sum.inl ⟨i,x⟩)) (fun y => X (Sum.inr ⟨i,y⟩)))

noncomputable def crossTensor (d e : I → ℕ) : S d ⊗[ℚ] S e :=
  separateTensor d e (crossDifference d e)

@[simp] lemma tensorValue_crossTensor (d e : I → ℕ) :
    tensorValue d e (crossTensor d e) = crossDifference d e :=
  tensorValue_separateTensor d e _ (crossDifference_symmetric d e)

noncomputable def relativeRaw (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ) :=
  aeval (Sum.elim (fun x => Polynomial.C (X (Sum.inl x)) + Polynomial.X)
    (fun y => Polynomial.C (X (Sum.inr y))))

omit [Fintype I] [DecidableEq I] in
lemma relativeRaw_left (d e : I → ℕ) (f : MvPolynomial (Σi,Fin (d i)) ℚ) :
    relativeRaw d e (rename Sum.inl f) =
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [relativeRaw]
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,taylor_X,Polynomial.map_mul,hf]
    congr 1
    simp [relativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma relativeRaw_right (d e : I → ℕ) (f : MvPolynomial (Σi,Fin (e i)) ℚ) :
    relativeRaw d e (rename Sum.inr f) = Polynomial.C (rename Sum.inr f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [relativeRaw]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,hf]
    congr 1
    simp [relativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma map_taylorS_left (d e : I → ℕ) (f : S d) :
    Polynomial.map (tensorValueAlg d e).toRingHom
      (Polynomial.map (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e).toRingHom
        (taylorS d f)) =
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f.val) := by
  rw [← map_taylorS d f,Polynomial.map_map,Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro g
  change tensorValue d e (g ⊗ₜ[ℚ] 1) = rename Sum.inl g.val
  simp

omit [Fintype I] [DecidableEq I] in
lemma map_relativeTaylor (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    Polynomial.map (tensorValueAlg d e).toRingHom (relativeTaylor d e f) =
      relativeRaw d e (tensorValue d e f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,Polynomial.map_mul,map_taylorS_left,
      Polynomial.map_C,tensorValue_tmul,map_mul,relativeRaw_left,relativeRaw_right]
    congr 1
    change Polynomial.C (tensorValue d e (1 ⊗ₜ[ℚ] g)) = _
    simp
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]

omit [DecidableEq I] in
lemma relativeRaw_crossDifference (d e : I → ℕ) :
    relativeRaw d e (crossDifference d e) =
      ∏ i, ∏ x : Fin (d i), ∏ y : Fin (e i),
        (Polynomial.X + Polynomial.C (X (Sum.inl ⟨i,x⟩) - X (Sum.inr ⟨i,y⟩))) := by
  simp only [crossDifference,map_prod,map_sub]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  simp [relativeRaw]
  ring

omit [DecidableEq I] in
lemma relativeRaw_crossDifference_monic (d e : I → ℕ) :
    (relativeRaw d e (crossDifference d e)).Monic := by
  rw [relativeRaw_crossDifference]
  apply Polynomial.monic_prod_of_monic
  intro i hi
  apply Polynomial.monic_prod_of_monic
  intro x hx
  apply Polynomial.monic_prod_of_monic
  intro y hy
  exact Polynomial.monic_X_add_C _

lemma relativeTaylor_crossTensor_monic (d e : I → ℕ) :
    (relativeTaylor d e (crossTensor d e)).Monic := by
  apply Polynomial.monic_of_injective (f := (tensorValueAlg d e).toRingHom) (tensorValue_injective d e)
  rw [map_relativeTaylor,tensorValue_crossTensor]
  exact relativeRaw_crossDifference_monic d e

noncomputable def crossClearing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
  Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e (crossTensor d e))

lemma crossClearing_monic (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (crossClearing a μ d e).Monic :=
  (relativeTaylor_crossTensor_monic d e).map _

lemma crossClearing_cancel (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : Polynomial (B a μ d ⊗[ℚ] B a μ e)) :
    crossClearing a μ d e * f = 0 ↔ f = 0 :=
  (crossClearing_monic a μ d e).mul_right_eq_zero_iff

end ElementaryPositivity.RawShuffle

end

end OAI
