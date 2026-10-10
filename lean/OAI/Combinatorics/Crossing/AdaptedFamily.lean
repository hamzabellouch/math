import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem exists_adapted_family (E : ℕ → Submodule ℝ W) (hE : Monotone E) (hzero : E 0 = ⊥)
    (h : ℕ) :
    ∃ (v : Fin (finrank ℝ (E h)) → W) (d : Fin (finrank ℝ (E h)) → ℕ),
      LinearIndependent ℝ v ∧ span ℝ (Set.range v) = E h ∧
      (∀ i, d i < h ∧ v i ∈ E (d i+1)) ∧
      (∑ i, d i) = ∑ e ∈ Finset.range h, e * (finrank ℝ (E (e+1)) - finrank ℝ (E e)) := by
  classical
  induction h with
  | zero =>
    have hd : finrank ℝ (E 0) = 0 := by simp [hzero]
    rw [hd]
    refine ⟨Fin.elim0, Fin.elim0, linearIndependent_empty_type, ?_, ?_, ?_⟩
    · simp [hzero]
    · intro i
      exact Fin.elim0 i
    · simp
  | succ h ih =>
    obtain ⟨v, d, hli, hspan, hmem, hsum⟩ := ih
    obtain ⟨C, hdisj, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq (hE (Nat.le_succ h))
    have hCle : C ≤ E (h+1) := by rw [← hsup]; exact le_sup_right
    have hdim : finrank ℝ (E h) + finrank ℝ C = finrank ℝ (E (h+1)) := by
      have hh := Submodule.finrank_sup_add_finrank_inf_eq (E h) C
      rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at hh
      exact hh.symm
    have hCdim : finrank ℝ C = finrank ℝ (E (h+1)) - finrank ℝ (E h) := by omega
    let b := finBasis ℝ C
    let w : Fin (finrank ℝ C) → W := fun i => C.subtype (b i)
    have hwli : LinearIndependent ℝ w := b.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
    have hwspan : span ℝ (Set.range w) = C := by
      change span ℝ (Set.range (C.subtype ∘ b)) = C
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    let v' := Sum.elim v w
    let d' := Sum.elim d (fun _ : Fin (finrank ℝ C) => h)
    have hv' : LinearIndependent ℝ v' :=
      hli.sum_type hwli (by rwa [hspan, hwspan])
    let e : Fin (finrank ℝ (E (h+1))) ≃
        (Fin (finrank ℝ (E h)) ⊕ Fin (finrank ℝ C)) :=
      Fintype.equivOfCardEq (by simp [hdim])
    refine ⟨v' ∘ e, d' ∘ e, hv'.comp e e.injective, ?_, ?_, ?_⟩
    · rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
      change span ℝ (Set.range (Sum.elim v w)) = E (h+1)
      rw [Set.Sum.elim_range, span_union, hspan, hwspan, hsup]
    · intro i
      change d' (e i) < h+1 ∧ v' (e i) ∈ E (d' (e i)+1)
      cases he : e i with
      | inl j =>
        change d j < h+1 ∧ v j ∈ E (d j+1)
        exact ⟨(hmem j).1.trans (Nat.lt_succ_self h), (hmem j).2⟩
      | inr j =>
        change h < h+1 ∧ w j ∈ E (h+1)
        exact ⟨Nat.lt_succ_self h, hCle (b j).property⟩
    · change (∑ i, d' (e i)) = _
      rw [e.sum_comp, Fintype.sum_sum_type, Finset.sum_range_succ]
      change (∑ i, d i) + (∑ _ : Fin (finrank ℝ C), h) = _
      rw [hsum]
      simp [hCdim, Nat.mul_comm]

end Zarankiewicz

end

end OAI
