import Mathlib
import OAI.Probability.BinarySweep.Processes.IndependentHistory
import OAI.Probability.BinarySweep.Representations.IrrepSupport
import OAI.Probability.BinarySweep.FiniteLaws.SumDite

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

instance oneAxisOutsideEmpty : IsEmpty {i : Fin 1 // i ≠ 0} :=
  ⟨fun i => i.property (Subsingleton.elim _ _)⟩

noncomputable def oneAxisSlotEquiv (bits : Fin 1 → ℕ) : GridSlot bits ≃ Slot (bits 0) :=
  Equiv.piUnique _
noncomputable def oneAxisChoiceEquiv (bits : Fin 1 → ℕ) :
    GridChoices bits ≃ Equiv.Perm (Slot (bits 0)) :=
  (Equiv.piUnique _).trans (Equiv.funUnique _ _)
noncomputable def oneAxisSweepEquiv (bits : Fin 1 → ℕ) :
    GridChoices bits ≃ Equiv.Perm (GridSlot bits) :=
  (oneAxisChoiceEquiv bits).trans ((oneAxisSlotEquiv bits).symm.permCongr)

lemma oneAxisSweepEquiv_apply (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    oneAxisSweepEquiv bits g = gridSweep bits g := by
  apply Equiv.ext
  intro x
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [gridSweep, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  change _ = gridLayer bits g 0 x 0
  simp only [oneAxisSweepEquiv, oneAxisChoiceEquiv, oneAxisSlotEquiv, Equiv.trans_apply,
    Equiv.permCongr_apply, Equiv.piUnique_apply,
    Equiv.funUnique_apply, gridLayer, Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply,
    Equiv.piSplitAt_symm_apply, dite_true, eq_self]
  simp only [Equiv.symm_symm, Equiv.piUnique_symm_apply, Equiv.piUnique_apply]
  have aux (y : GridOutside bits default) (i : Fin 1) :
      uniqueElim (α := fun j => Slot (bits j)) ((g default y) (x default)) i =
      (g i (fun j => x j.val)) (x i) := by
    obtain rfl := Unique.eq_default i
    rw [uniqueElim_default]
    apply congrArg (fun y : GridOutside bits default => g default y (x default))
    funext j
    exact (j.property (Subsingleton.elim _ _)).elim
  exact aux _ 0

lemma oneAxis_pathEvent_iff {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ k, gridSweep bits g (H.position 0 k) = H.position (Fin.last 1) k := by
  constructor
  · exact fun hg k => gridSweep_path H g hg k
  · intro hg j k
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [gridSweep, List.ofFn_succ] using hg k

def assignmentResidualEquiv {X I : Type*} [Fintype X] [Fintype I]
    (A B : I ↪ X) (c : {x : X // x ∉ Set.range A} ≃ {x : X // x ∉ Set.range B}) :
    {σ : Equiv.Perm X // Assigns A B σ} ≃ Equiv.Perm {x : X // x ∉ Set.range A} := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro hs x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using hs i
      · intro hs i
        simpa [e₀, eA, eB] using hs (eA i))
  exact (e.trans (Equiv.Set.compl e₀)).trans (Equiv.equivCongr (Equiv.refl _) c.symm)

lemma assignmentResidualEquiv_apply {X I : Type*} [Fintype X] [Fintype I]
    (A B : I ↪ X) (c : {x : X // x ∉ Set.range A} ≃ {x : X // x ∉ Set.range B})
    (σ : {σ : Equiv.Perm X // Assigns A B σ}) (x : {x : X // x ∉ Set.range A}) :
    (c (assignmentResidualEquiv A B c σ x)).val = σ.val x := by
  simp [assignmentResidualEquiv, Equiv.equivCongr, Equiv.Set.compl]
  rfl

def oneAxisRemainingEquiv {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h) :
    {g : GridChoices bits // pathEvent H g} ≃ Equiv.Perm (FreeSlot H 0) := by
  let A : Fin h ↪ GridSlot bits := ⟨H.position 0, H.disjoint 0⟩
  let B : Fin h ↪ GridSlot bits := ⟨H.position (Fin.last 1), H.disjoint _⟩
  exact (Equiv.subtypeEquiv (oneAxisSweepEquiv bits) (by
    intro g
    simpa only [Assigns, oneAxisSweepEquiv_apply, A, B, Function.Embedding.coeFn_mk] using oneAxis_pathEvent_iff H g)).trans
      (assignmentResidualEquiv A B (freeIdentification H))

lemma oneAxisRemainingEquiv_apply {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h)
    (g : {g : GridChoices bits // pathEvent H g}) :
    oneAxisRemainingEquiv H g = remainingPerm H g.val g.property := by
  apply Equiv.ext
  intro x
  apply (freeIdentification H).injective
  apply Subtype.ext
  have he := assignmentResidualEquiv_apply
    (⟨H.position 0, H.disjoint 0⟩ : Fin h ↪ GridSlot bits)
    (⟨H.position (Fin.last 1), H.disjoint _⟩ : Fin h ↪ GridSlot bits)
    (freeIdentification H)
    ((Equiv.subtypeEquiv (oneAxisSweepEquiv bits) (by
      intro g
      simpa only [Assigns, oneAxisSweepEquiv_apply, Function.Embedding.coeFn_mk] using oneAxis_pathEvent_iff H g)) g) x
  simpa only [oneAxisRemainingEquiv, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    oneAxisSweepEquiv_apply, remainingPerm, Equiv.apply_symm_apply, remainingBijection,
    Equiv.coe_fn_mk] using he

lemma oneAxis_gridWeight (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = lineLaw (bits 0) z (oneAxisChoiceEquiv bits g) := by
  simp [gridWeight, oneAxisChoiceEquiv, Equiv.piUnique, Equiv.funUnique]

lemma oneAxis_gridWeight_zero (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    gridWeight bits 0 g = (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by
  rw [oneAxis_gridWeight]
  simp only [lineLaw, sub_zero, one_mul, zero_mul, add_zero, uniformLaw]
  congr 2
  exact Fintype.card_congr (oneAxisSlotEquiv bits).symm.permCongr

lemma oneAxis_conditionalOperator_zero {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hD : 1 < D) : conditionalOperator H 0 ρ = 0 := by
  have hdim : 1 < Module.finrank ℂ (RepSpace D) := by simpa using hD
  have hsum := Irrep.sum_eq_zero_of_finrank_gt_one ρ hdim
  have hperm : (∑ g : {g : GridChoices bits // pathEvent H g},
      ρ (remainingPerm H g.val g.property)) = 0 := by
    calc
      _ = ∑ g : {g : GridChoices bits // pathEvent H g}, ρ (oneAxisRemainingEquiv H g) := by
        simp only [oneAxisRemainingEquiv_apply]
      _ = 0 := ((oneAxisRemainingEquiv H).sum_comp (fun σ => ρ σ)).trans hsum
  unfold conditionalOperator
  have he : (∑ g : GridChoices bits, if hg : pathEvent H g then
      (gridWeight bits 0 g : ℂ) • ρ (remainingPerm H g hg) else 0) = 0 := by
    rw [sum_dite_zero]
    simp only [oneAxis_gridWeight_zero, ← Finset.smul_sum]
    apply smul_eq_zero.mpr
    right
    convert hperm using 1
  rw [he, smul_zero]
  rfl

end BinaryCoordinateSweeps

end

end OAI
