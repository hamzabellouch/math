import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalLift

namespace OAI

/-! Tensor products with identity spectators are actual finite-support
operators, with their small matrix given explicitly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalLift_apply (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) (s t : ι → Fin 2) :
    qmaLocalLift S A s t =
      A (fun i => s i.val) (fun i => t i.val)*
        if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0 := by
  rfl

theorem qmaLocalOn_permutation (S : Finset ι) (F : (ι → Fin 2) → (ι → Fin 2))
    (f : QMASupportBasis S → QMASupportBasis S)
    (hcore : ∀ t, (qmaSupportSplit S (F t)).1 = f (qmaSupportSplit S t).1)
    (hrest : ∀ t, (qmaSupportSplit S (F t)).2 = (qmaSupportSplit S t).2) :
    QMALocalOn S (fun s t => if s = F t then (1:ℂ) else 0) := by
  refine ⟨(fun s t => if s = f t then 1 else 0),?_⟩
  ext s t
  change (if s = F t then (1:ℂ) else 0) =
    (if (qmaSupportSplit S s).1 = f (qmaSupportSplit S t).1 then 1 else 0)*
      if (qmaSupportSplit S s).2 = (qmaSupportSplit S t).2 then 1 else 0
  by_cases hr : (qmaSupportSplit S s).2 = (qmaSupportSplit S t).2
  · have he : (qmaSupportSplit S s).1 = f (qmaSupportSplit S t).1 ↔ s = F t := by
      constructor
      · intro hc
        apply (qmaSupportSplit S).injective
        exact Prod.ext (hc.trans (hcore t).symm) (hr.trans (hrest t).symm)
      · intro h
        subst s
        exact hcore t
    simp [hr,he]
  · have he : s ≠ F t := by
      intro h
      subst s
      exact hr (hrest t)
    simp [hr,he]

theorem qmaLocalOn_sourceTensor (n : ℕ) (S : Finset (Fin n))
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hM : ∀ i, i ∉ S → M i = 1) :
    QMALocalOn S (sourceTensor n M) := by
  refine ⟨(fun s t => ∏ i : {i // i ∈ S}, M i.val (s i) (t i)),?_⟩
  ext s t
  change (∏ i, M i (s i) (t i)) =
    (∏ i : {i // i ∈ S}, M i.val (s i.val) (t i.val))*
      if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0
  by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
  · rw [ite_eq_left hr,mul_one]
    have he (i : Fin n) (_hi : i ∈ Finset.univ) (hi : i ∉ S) : M i (s i) (t i) = 1 := by
      rw [hM i hi]
      have ht := congrFun hr ⟨i,hi⟩
      exact ite_eq_left ht
    have hp := Finset.prod_subset (Finset.subset_univ S) he
    have hs := Finset.prod_subtype (F := inferInstance) S
      (by simp : ∀ i, i ∈ S ↔ i ∈ S) (fun i => M i (s i) (t i))
    exact hp.symm.trans hs
  · rw [ite_eq_right hr,mul_zero]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    rw [hM i.val i.property]
    exact ite_eq_right hi

end ContinuumCoulomb

end

end OAI
