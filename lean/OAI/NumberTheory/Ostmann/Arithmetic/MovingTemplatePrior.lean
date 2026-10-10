import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTemplate
import OAI.NumberTheory.Ostmann.Construction.SelectedPrimeFubini
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleCoordinates

namespace OAI

/-! # The unchanged independent prime law under one template restoration -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRestoreSample {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    MovingRegularSlot n (4 + r) m → A :=
  Sum.elim u y ∘ (movingReverseTemplate n r m).symm

@[simp] theorem movingRestoreSample_compensation {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (i : TreeLeafIndex n × Fin 4) :
    movingRestoreSample n r m u y (i.1, .inl (Fin.castAdd r i.2)) = u i := by
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem movingRestoreSample_small {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (j : TreeLeafIndex n) (i : Fin r) :
    movingRestoreSample n r m u y (j, .inl (Fin.natAdd 4 i)) = y (j, .inl i) := by
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inr (j, .inl i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem movingRestoreSample_bulk {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (i : TreeLeafIndex n × Fin m) :
    movingRestoreSample n r m u y (movingTemplateBulk n (4 + r) m i) =
      y (movingTemplateBulk n r m i) := by
  rw [← movingReverseTemplate_bulk n r m i]
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inr (movingTemplateBulk n r m i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- This is literal finite Fubini; neither distinctness nor any history
support is conditioned into the prime law. -/
theorem movingReverseTemplate_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A,
        ((∏ i, ν (movingReverseTemplate n r m (.inl i)) (u i) : ℝ) : ℂ) *
        ∑ y : MovingRegularSlot n r m → A,
          ((∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i) : ℝ) : ℂ) *
          F (movingRestoreSample n r m u y) := by
  have hr := finite_prior_reindex (movingReverseTemplate n r m) ν F
  simp only [finite_univ_canonical] at hr ⊢
  rw [← hr]
  let e := Equiv.sumArrowEquivProdArrow (TreeLeafIndex n × Fin 4) (MovingRegularSlot n r m) A
  have he := e.symm.sum_comp (fun x =>
    ((∏ i, ν (movingReverseTemplate n r m i) (x i) : ℝ) : ℂ) *
      F (x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  have hs := Fintype.sum_prod_type (fun x :
      (TreeLeafIndex n × Fin 4 → A) × (MovingRegularSlot n r m → A) =>
    ((∏ i, ν (movingReverseTemplate n r m i) (e.symm x i) : ℝ) : ℂ) *
      F (e.symm x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hp := Fintype.prod_sum_type (fun i :
      (TreeLeafIndex n × Fin 4) ⊕ MovingRegularSlot n r m =>
    ν (movingReverseTemplate n r m i) (e.symm (u, y) i))
  simp only [finite_univ_canonical] at hp
  rw [hp]
  simp only [e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  change _ * F (movingRestoreSample n r m u y) = _
  ring

/-- The compensation block is sampled once, in precisely the coordinates
of `movingCompensationPrior`; the two child histories will share this block. -/
def movingTemplateCompensationEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple (Fin 4 → A) n ≃ (TreeLeafIndex n × Fin 4 → A) :=
  (treeLeafTupleEquiv (Fin 4 → A) n).trans (Equiv.curry (TreeLeafIndex n) (Fin 4) A).symm

theorem movingTemplateCompensationEquiv_prior {A : Type*}
    (μ : A → ℝ) (n : ℕ) (a : TreeLeafTuple (Fin 4 → A) n) :
    (∏ i, μ (movingTemplateCompensationEquiv A n a i)) = movingCompensationPrior μ n a := by
  rw [movingCompensationPrior_indexed, Fintype.prod_prod_type]
  rfl

theorem movingReverseTemplate_compensation_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ) (μ : A → ℝ)
    (hμ : ∀ i a, ν (movingReverseTemplate n r m (.inl i)) a = μ a)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ a : TreeLeafTuple (Fin 4 → A) n, (movingCompensationPrior μ n a : ℂ) *
        ∑ y : MovingRegularSlot n r m → A,
          ((∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i) : ℝ) : ℂ) *
            F (movingRestoreSample n r m (movingTemplateCompensationEquiv A n a) y) := by
  rw [movingReverseTemplate_average]
  simp_rw [hμ]
  have he := (movingTemplateCompensationEquiv A n).sum_comp (fun u =>
    ((∏ i, μ (u i) : ℝ) : ℂ) *
      ∑ y : MovingRegularSlot n r m → A,
        ((∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i) : ℝ) : ℂ) *
          F (movingRestoreSample n r m u y))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  have hp := movingTemplateCompensationEquiv_prior μ n a
  simp only [finite_univ_canonical] at hp
  rw [hp]

end Ostmann

end OAI
