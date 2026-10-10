import Mathlib
import OAI.Analysis.Commutator.CycleInvariants

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J]

instance (σ : Equiv.Perm J) : DecidableEq (cycleSet σ) := Classical.decEq _

def cycleMap (σ : Equiv.Perm J) (j : J) : cycleSet σ := Quotient.mk _ j

omit [Fintype J] in
@[simp] lemma cycleMap_apply (σ : Equiv.Perm J) (j : J) :
    cycleMap σ (σ j) = cycleMap σ j :=
  Quotient.sound (Equiv.Perm.SameCycle.refl σ j).apply_left

def cycleCard (σ : Equiv.Perm J) (q : cycleSet σ) : ℕ :=
  Fintype.card {j : J // cycleMap σ j = q}

lemma sum_cycleCard (σ : Equiv.Perm J) :
    ∑ q, cycleCard σ q = Fintype.card J := by
  classical
  simp only [cycleCard]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (cycleMap σ))

lemma cycleCard_pos (σ : Equiv.Perm J) (q : cycleSet σ) : 0 < cycleCard σ q := by
  let j : J := Quotient.out q
  have hj : cycleMap σ j = q := Quotient.out_eq q
  let : Nonempty {j : J // cycleMap σ j = q} := ⟨⟨j, hj⟩⟩
  exact Fintype.card_pos

lemma two_le_cycleCard (σ : Equiv.Perm J) (j : J) (hj : σ j ≠ j) :
    2 ≤ cycleCard σ (cycleMap σ j) := by
  unfold cycleCard
  apply Fintype.one_lt_card_iff.mpr
  exact ⟨⟨σ j, cycleMap_apply σ j⟩, ⟨j, rfl⟩, fun h => hj (congrArg Subtype.val h)⟩

lemma three_le_cycleCard (σ : Equiv.Perm J) (j : J) (hj : σ (σ j) ≠ j) :
    3 ≤ cycleCard σ (cycleMap σ j) := by
  have h : σ j ≠ j := by intro e; apply hj; rw [e, e]
  unfold cycleCard
  apply Fintype.two_lt_card_iff.mpr
  refine ⟨⟨j, rfl⟩, ⟨σ j, cycleMap_apply σ j⟩,
    ⟨σ (σ j), by simp⟩, ?_, ?_, ?_⟩
  · exact fun e => h (congrArg Subtype.val e).symm
  · exact fun e => hj (congrArg Subtype.val e).symm
  · exact fun e => h (σ.injective (congrArg Subtype.val e)).symm

omit [Fintype J] in
lemma cycleMap_eq_fixed (σ : Equiv.Perm J) {a j : J} (ha : σ a = a)
    (hj : cycleMap σ j = cycleMap σ a) : j = a :=
  ((Quotient.exact hj).symm.eq_of_left ha).symm

lemma minimal_cycle_sum (σ : Equiv.Perm J) (a : J) :
    (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) + 1 =
      2 * cycleCount σ := by
  classical
  calc
    _ = (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) +
        ∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 0 := by simp
    _ = ∑ q : cycleSet σ, ((if q = cycleMap σ a then 1 else 2) +
        if q = cycleMap σ a then 1 else 0) := by rw [Finset.sum_add_distrib]
    _ = ∑ _q : cycleSet σ, 2 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> rfl
    _ = _ := by simp [cycleCount, mul_comm]

lemma minimal_cycle_bound (σ : Equiv.Perm J) (a : J)
    (h : ∀ j, σ j = j → j = a) (q : cycleSet σ) :
    (if q = cycleMap σ a then 1 else 2) ≤ cycleCard σ q := by
  classical
  by_cases hq : q = cycleMap σ a
  · rw [ite_eq_left hq]; exact cycleCard_pos σ q
  · rw [ite_eq_right hq]
    have hj : cycleMap σ (Quotient.out q) = q := Quotient.out_eq q
    rw [← hj]
    apply two_le_cycleCard
    intro hfix
    exact hq (hj.symm.trans (congrArg (cycleMap σ) (h _ hfix)))

theorem endpoint_cycle_classification (σ : Equiv.Perm J) (a : J)
    (h : ∀ j, σ j = j → j = a)
    (hc : Fintype.card J + 1 ≤ 2 * cycleCount σ) :
    σ a = a ∧ ∀ j, σ (σ j) = j := by
  classical
  have ha : σ a = a := by
    by_contra hn
    have hall : ∀ j, σ j ≠ j := fun j hj => hn (by simpa [h j hj] using hj)
    have hbound (q : cycleSet σ) : 2 ≤ cycleCard σ q := by
      have hq : cycleMap σ (Quotient.out q) = q := Quotient.out_eq q
      rw [← hq]
      exact two_le_cycleCard σ _ (hall _)
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hbound q)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, sum_cycleCard] at hs
    change cycleCount σ * 2 ≤ Fintype.card J at hs
    omega
  refine ⟨ha, fun j => ?_⟩
  by_contra hj
  have hne : cycleMap σ j ≠ cycleMap σ a := by
    intro he
    have heq := cycleMap_eq_fixed σ ha he
    subst j
    exact hj (by rw [ha, ha])
  have hstrict : (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) <
      ∑ q : cycleSet σ, cycleCard σ q := by
    apply Finset.sum_lt_sum
    · exact fun q _ => minimal_cycle_bound σ a h q
    · refine ⟨cycleMap σ j, Finset.mem_univ _, ?_⟩
      rw [ite_eq_right hne]
      exact three_le_cycleCard σ j hj
  rw [sum_cycleCard] at hstrict
  have hs := minimal_cycle_sum σ a
  omega

end Kadison.SchurWeyl
end

end OAI
