import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ReynoldsS
import OAI.Combinatorics.Chromatic.Walls.Taylor

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable instance quotientCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    CommRing (B a μ d) := inferInstanceAs (CommRing (S d ⧸ destabilizingIdeal a μ d))
noncomputable instance quotientAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Algebra ℚ (B a μ d) := inferInstanceAs (Algebra ℚ (S d ⧸ destabilizingIdeal a μ d))

noncomputable def quotientAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    S d →ₐ[ℚ] B a μ d := Ideal.Quotient.mkₐ ℚ (destabilizingIdeal a μ d)

@[simp] lemma quotientAlg_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    quotientAlg a μ d f = (destabilizingSpace a μ d).mkQ f := rfl

noncomputable def tensorValueAlg (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map (symmetricSpace d).val (symmetricSpace e).val)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValueAlg_apply (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    tensorValueAlg d e f = tensorValue d e f := rfl

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_mul (d e : I → ℕ) (f g : S d ⊗[ℚ] S e) :
    tensorValue d e (f*g) = tensorValue d e f * tensorValue d e g :=
  (tensorValueAlg d e).map_mul f g

noncomputable def restrictTensorAlg {d e : I → ℕ} (A : Cut d e) : S (d+e) →ₐ[ℚ] S d ⊗[ℚ] S e where
  toFun := restrictTensor A
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor]
    change rename (cutSplit A).symm 1 = tensorValueAlg d e 1
    exact (map_one (rename (R:=ℚ) (cutSplit A).symm)).trans
      (map_one (tensorValueAlg d e)).symm
  map_mul' f g := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor,tensorValue_mul,tensorValue_restrictTensor,tensorValue_restrictTensor]
    exact map_mul _ _ _
  commutes' q := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor]
    change rename (cutSplit A).symm (algebraMap ℚ _ q) =
      tensorValueAlg d e (algebraMap ℚ _ q)
    rw [(tensorValueAlg d e).commutes,(rename (cutSplit A).symm).commutes]

omit [Fintype I] [DecidableEq I] in
lemma taylorS_exists (d : I → ℕ) (f : S d) :
    ∃ q : Polynomial (S d), Polynomial.map (symmetricSpace d).val.toRingHom q = taylor f.val := by
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro n
  have h : (taylor f.val).coeff n ∈ (symmetricSpace d).toSubmodule := by
    apply polynomial_coeff_mem (symmetricSpace d).toSubmodule (taylor f.val)
    intro t
    change (taylor f.val).eval (C t) ∈ (symmetricSpace d).toSubmodule
    rw [taylor_eval]
    exact translation_symmetric t f.val f.property
  exact ⟨⟨_,h⟩,rfl⟩

noncomputable def taylorSValue (d : I → ℕ) (f : S d) : Polynomial (S d) :=
  (taylorS_exists d f).choose

omit [Fintype I] [DecidableEq I] in
@[simp] lemma map_taylorSValue (d : I → ℕ) (f : S d) :
    Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) = taylor f.val :=
  (taylorS_exists d f).choose_spec

omit [Fintype I] [DecidableEq I] in
lemma polynomial_symmetric_injective (d : I → ℕ) :
    Function.Injective (Polynomial.map (symmetricSpace d).val.toRingHom) :=
  Polynomial.map_injective _ Subtype.val_injective

noncomputable def taylorS (d : I → ℕ) : S d →ₐ[ℚ] Polynomial (S d) where
  toFun := taylorSValue d
  map_zero' := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d 0) =
      Polynomial.map (symmetricSpace d).val.toRingHom 0
    exact (map_taylorSValue d 0).trans (by simp)
  map_one' := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d 1) =
      Polynomial.map (symmetricSpace d).val.toRingHom 1
    exact (map_taylorSValue d 1).trans (by simp)
  map_add' f g := by
    apply polynomial_symmetric_injective d
    rw [Polynomial.map_add]
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d (f+g)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) +
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d g)
    rw [map_taylorSValue,map_taylorSValue,map_taylorSValue]
    exact map_add _ _ _
  map_mul' f g := by
    apply polynomial_symmetric_injective d
    rw [Polynomial.map_mul]
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d (f*g)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) *
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d g)
    rw [map_taylorSValue,map_taylorSValue,map_taylorSValue]
    exact map_mul _ _ _
  commutes' q := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom
      (taylorSValue d (algebraMap ℚ (S d) q)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (Polynomial.C (algebraMap ℚ (S d) q))
    rw [map_taylorSValue,Polynomial.map_C]
    change taylor (C q : MvPolynomial (Σi,Fin (d i)) ℚ) = Polynomial.C (C q)
    exact taylor_C q

omit [Fintype I] [DecidableEq I] in
@[simp] lemma map_taylorS (d : I → ℕ) (f : S d) :
    Polynomial.map (symmetricSpace d).val.toRingHom (taylorS d f) = taylor f.val :=
  map_taylorSValue d f

omit [Fintype I] [DecidableEq I] in
lemma taylorS_eval (d : I → ℕ) (f : S d) (t : ℚ) :
    (taylorS d f).eval (algebraMap ℚ (S d) t) = translationS d t f := by
  apply Subtype.ext
  have h := congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ) =>
    p.eval (C t)) (map_taylorS d f)
  rw [taylor_eval] at h
  change (symmetricSpace d).val ((taylorS d f).eval (algebraMap ℚ (S d) t)) =
    translation t f.val
  calc
    _ = (Polynomial.map (symmetricSpace d).val.toRingHom (taylorS d f)).eval (C t) := by
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply (symmetricSpace d).val.toRingHom (algebraMap ℚ (S d) t)).symm
    _ = translation t f.val := h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma taylorS_coeff_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) {f : S d} (hf : f ∈ destabilizingSpace a μ d) (n : ℕ) :
    (taylorS d f).coeff n ∈ destabilizingSpace a μ d := by
  apply polynomial_coeff_mem (destabilizingSpace a μ d) (taylorS d f)
  intro t
  rw [taylorS_eval]
  exact translation_destabilizing a μ d t hf

noncomputable def taylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    B a μ d →ₐ[ℚ] Polynomial (B a μ d) :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a μ d)
    ((Polynomial.mapAlgHom (quotientAlg a μ d)).comp (taylorS d)) (by
      intro f hf
      apply Polynomial.ext
      intro n
      change (Polynomial.map (quotientAlg a μ d).toRingHom (taylorS d f)).coeff n = (0 : Polynomial (B a μ d)).coeff n
      rw [Polynomial.coeff_map,Polynomial.coeff_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (taylorS_coeff_destabilizing a μ d hf n))

@[simp] lemma taylorB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    taylorB a μ d (quotientAlg a μ d f) = Polynomial.map (quotientAlg a μ d).toRingHom (taylorS d f) := rfl

lemma eval_map_rat {R T : Type*} [Semiring R] [Semiring T] [Algebra ℚ R] [Algebra ℚ T]
    (φ : R →ₐ[ℚ] T) (p : Polynomial R) (t : ℚ) :
    (Polynomial.map φ.toRingHom p).eval (algebraMap ℚ T t) =
      φ (p.eval (algebraMap ℚ R t)) := by
  rw [Polynomial.eval_map]
  calc
    _ = Polynomial.eval₂ φ.toRingHom (φ (algebraMap ℚ R t)) p :=
      congrArg (fun x => Polynomial.eval₂ φ.toRingHom x p) (φ.commutes t).symm
    _ = _ := Polynomial.eval₂_at_apply φ.toRingHom (algebraMap ℚ R t)

noncomputable def relativeTaylor (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
  let L : S d →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e)).comp (taylorS d)
  let R : S e →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
    Polynomial.CAlgHom.comp (Algebra.TensorProduct.includeRight : S e →ₐ[ℚ] S d ⊗[ℚ] S e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => (mul_comm (L x) (R y)))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma relativeTaylor_tmul (d e : I → ℕ) (f : S d) (g : S e) :
    relativeTaylor d e (f ⊗ₜ[ℚ] g) =
      Polynomial.map (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e).toRingHom (taylorS d f) *
      Polynomial.C ((1 : S d) ⊗ₜ[ℚ] g) := by
  simp only [relativeTaylor]
  rfl

noncomputable def quotientTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e :=
  Algebra.TensorProduct.map (quotientAlg a μ d) (quotientAlg a μ e)

noncomputable def restrictRelative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (A : Cut d e) :
    S (d+e) →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
  (Polynomial.mapAlgHom (quotientTensor a μ d e)).comp
    ((relativeTaylor d e).comp (restrictTensorAlg A))

omit [Fintype I] [DecidableEq I] in
lemma relativeTaylor_eval (d e : I → ℕ) (f : S d ⊗[ℚ] S e) (t : ℚ) :
    (relativeTaylor d e f).eval (algebraMap ℚ (S d ⊗[ℚ] S e) t) =
      TensorProduct.map (translationS d t) (LinearMap.id : S e →ₗ[ℚ] S e) f := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,Polynomial.eval_mul,Polynomial.eval_C,
      eval_map_rat (R := S d) (T := S d ⊗[ℚ] S e) (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e),taylorS_eval]
    simp
  | add f g hf hg => rw [map_add,Polynomial.eval_add,map_add,hf,hg]

lemma restrictRelative_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (A : Cut d e) (f : S (d+e)) (t : ℚ) :
    (restrictRelative a μ A f).eval (algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e) t) =
      restrictQuotientAt a μ A t 0 f := by
  change (Polynomial.map (quotientTensor a μ d e).toRingHom
    (relativeTaylor d e (restrictTensor A f))).eval _ = _
  rw [eval_map_rat (R := S d ⊗[ℚ] S e) (T := B a μ d ⊗[ℚ] B a μ e) (quotientTensor a μ d e),relativeTaylor_eval]
  change quotientTensor a μ d e (TensorProduct.map (translationS d t) LinearMap.id (restrictTensor A f)) =
    TensorProduct.map
      ((destabilizingSpace a μ d).mkQ ∘ₗ translationS d t)
      ((destabilizingSpace a μ e).mkQ ∘ₗ translationS e 0) (restrictTensor A f)
  generalize restrictTensor A f = x
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [quotientTensor]
  | add x y hx hy => simp_all

end ElementaryPositivity.RawShuffle

end

end OAI
