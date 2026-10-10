import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry4
import OAI.Analysis.Commutator.FreeSymmetry5

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert UniformSpace

open scoped TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

lemma wordLeft_inner (a : A) (n : ℕ)
    (x y : wordSpace (fullSpace τ) (zeroSpace τ) n) :
    inner ℂ (wordLeft τ a n x) y = inner ℂ x (wordLeft τ (star a) n y) := by
  apply HilbertTensor.inner_map_left_adjoint
  intro x y
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right (τ.gnsStarAlgHom a) x y).symm

lemma wordLeft_word (a d : A) (n : ℕ) (x : Fin n → zeroSpace τ) :
    wordLeft τ a n (word (fullSpace τ) (zeroSpace τ) n (algebraVector τ d) x) =
      word (fullSpace τ) (zeroSpace τ) n (algebraVector τ (a*d)) x := by
  simp only [wordLeft, word, HilbertTensor.map_coe_tmul, one_apply_eq_self,
    algebraVector_apply, left_coe]

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

lemma word_inner_move_endpoint
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (d c : A) (x : Fin k → zeroSpace τ) (y : Fin l → zeroSpace τ) :
    inner ℂ (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ c) y)
      (Y (word (fullSpace τ) (zeroSpace τ) k (algebraVector τ d) x)) =
      inner ℂ (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ (star d * c)) y)
        (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) := by
  have hd : word (fullSpace τ) (zeroSpace τ) k (algebraVector τ d) x =
      wordLeft τ d k (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x) := by
    have hv : algebraVector τ (1 : A) = vacuum τ := rfl
    simpa only [mul_one, hv] using (wordLeft_word τ d 1 k x).symm
  have hy : Y (wordLeft τ d k (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) =
      wordLeft τ d l (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) :=
    congrArg (fun T : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) l =>
        T (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) (hleft d)
  have hm := wordLeft_inner τ (star d) l
    (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ c) y)
    (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x))
  rw [wordLeft_word, star_star] at hm
  rw [hd, hy]
  exact hm.symm

omit [Nonempty I] in
lemma word_inner_stageCoefficient (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (d c : Matrix I I ℂ) (x : Fin k → Matrix I I ℂ) (y : Fin l → Matrix I I ℂ) :
    inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ φ c)
      (fun j => centeredStageVector τ φ (y j)))
      (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ φ d)
        (fun i => centeredStageVector τ φ (x i)))) =
      stageCoefficient τ Y φ (fun o : Option (Fin k ⊕ Fin l) =>
        o.elim (star c * d) (Sum.elim x (fun j => star (y j)))) := by
  have h := word_inner_move_endpoint τ Y hleft (φ d) (φ c)
    (fun i => centeredStageVector τ φ (x i)) (fun j => centeredStageVector τ φ (y j))
  simp only [stageCoefficient, coefficientMultilinear, MultilinearMap.coe_mk]
  simp only [coefficient, Option.elim_none, Option.elim_some, Sum.elim_inl,
    Sum.elim_inr, star_mul, star_star]
  have ha : stageVector τ φ (star d * c) = algebraVector τ (star (φ d) * φ c) := by
    change algebraVector τ (φ (star d * c)) = _
    rw [map_mul, map_star]
  rw [ha]
  exact h

include hτ h1 in
lemma centeredStageVector_of_trace_zero (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a : Matrix I I ℂ) (ha : a.trace = 0) :
    (centeredStageVector τ φ a : τ.GNS) = stageVector τ φ a := by
  rw [stage_centered τ hτ h1, ha, mul_zero, zero_smul, sub_zero]

include hτ h1 in
lemma centeredStageVector_inner (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a b : Matrix I I ℂ) (ha : a.trace = 0) (hb : b.trace = 0) :
    inner ℂ (centeredStageVector τ φ a) (centeredStageVector τ φ b) =
      (Fintype.card I : ℂ)⁻¹ * Matrix.trace (b * star a) := by
  change inner ℂ (centeredStageVector τ φ a : τ.GNS)
    (centeredStageVector τ φ b : τ.GNS) = _
  rw [centeredStageVector_of_trace_zero τ hτ h1 φ a ha,
    centeredStageVector_of_trace_zero τ hτ h1 φ b hb, stage_inner τ hτ h1]
  rw [Matrix.trace_mul_comm]

include hτ h1 in
theorem stageWord_inner_classification (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c₀ : (Fin k ≃ Fin l) → ℂ, ∀ n (d c : Matrix (I n) (I n) ℂ)
      (x : Fin k → Matrix (I n) (I n) ℂ) (y : Fin l → Matrix (I n) (I n) ℂ),
      (∀ i, Matrix.trace (x i) = 0) → (∀ j, Matrix.trace (y j) = 0) →
      inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ (φ n) c)
        (fun j => centeredStageVector τ (φ n) (y j)))
        (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ (φ n) d)
          (fun i => centeredStageVector τ (φ n) (x i)))) =
      inner ℂ (stageVector τ (φ n) c) (stageVector τ (φ n) d) *
        ∑ b : Fin k ≃ Fin l, c₀ b * ∏ i,
          inner ℂ (centeredStageVector τ (φ n) (y (b i)))
            (centeredStageVector τ (φ n) (x i)) := by
  classical
  obtain ⟨c₀, hc₀⟩ := stageCoefficient_crossing τ hτ h1 Y I φ e he hsize hY hleft
  refine ⟨c₀, ?_⟩
  intro n d c x y hx hy
  rw [word_inner_stageCoefficient τ Y (φ n) hleft]
  let v : TailSlots k l → Matrix (I n) (I n) ℂ := Sum.elim x (fun j => star (y j))
  have hv (j : TailSlots k l) : (v j).trace = 0 := by
    cases j with
    | inl i => exact hx i
    | inr j => simp only [v, Sum.elim_inr, Matrix.star_eq_conjTranspose,
        Matrix.trace_conjTranspose, hy j, star_zero]
  have h := hc₀ n (star c * d) v hv
  change stageCoefficient τ Y (φ n)
    (fun o : Option (TailSlots k l) => o.elim (star c * d) v) = _
  refine h.trans ?_
  rw [stage_inner τ hτ h1]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (centeredStageVector_inner τ hτ h1 (φ n) (y (b i)) (x i) (hy _) (hx _)).symm

end Kadison.TracialGNS
end

end OAI
