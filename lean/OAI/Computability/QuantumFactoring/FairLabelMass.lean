import Mathlib
import OAI.Computability.QuantumFactoring.ParallelPreparation
import OAI.Computability.QuantumFactoring.ThresholdRetention

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma fair_value_mass {b k : ℕ} (hk : k<2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat=k) (fairState b)=1/(2:ℝ)^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat=k then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val=k then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  have he : ∀ i : Fin (2^b), i.val=k ↔ i=⟨k,hk⟩ := by
    intro i
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,one_div,inv_pow]

lemma fair_fixed_append {b k : ℕ} {α : Type*} [Fintype α]
    (hk : k<2^b) (χ : α→ℂ) (P : ℕ→α→Prop) :
    outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat=k ∧ P (bitsValue xu.1).toNat xu.2)
      (independentState (fairState b) χ)= (1/(2:ℝ)^b)*outcomeMass (P k) χ := by
  have he : (fun xu : Basis b × α => (bitsValue xu.1).toNat=k ∧ P (bitsValue xu.1).toNat xu.2)=
      (fun xu => (bitsValue xu.1).toNat=k ∧ P k xu.2) := by
    funext xu
    apply propext
    constructor
    · rintro ⟨h,hp⟩; exact ⟨h,h ▸ hp⟩
    · rintro ⟨h,hp⟩; exact ⟨h,h.symm ▸ hp⟩
  rw [he,independent_mass (fairState b) χ (fun x => (bitsValue x).toNat=k) (P k),
    fair_value_mass hk]

lemma fair_variable_append {b d : ℕ} {α : Type*} [Fintype α]
    (hd : d≤2^b) (χ : α→ℂ) (P : ℕ→α→Prop) :
    outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
      (independentState (fairState b) χ)=
      (1/(2:ℝ)^b)*∑ t ∈ Finset.range d, outcomeMass (P t) χ := by
  classical
  change outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
    (RecordedHistory.appendState (fairState b) (fun _ => χ))=_
  rw [RecordedHistory.append_mass (fairState b) (fun _ => χ)
    (fun x => (bitsValue x).toNat<d) (fun x => P (bitsValue x).toNat)]
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<d then (2:ℝ)⁻¹^b*outcomeMass (P (bitsValue x).toNat) χ else 0)
    (fun i => if i.val<d then (2:ℝ)⁻¹^b*outcomeMass (P i.val) χ else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0)=
      ∑ i ∈ Finset.range d, (2:ℝ)⁻¹^b*outcomeMass (P i) χ := by
    rw [← Finset.sum_subset (Finset.range_mono hd)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he,← Finset.mul_sum]
  simp only [one_div,inv_pow]

lemma outcomeMass_disjoint_or {α : Type*} [Fintype α] (ψ : α→ℂ) (P R : α→Prop)
    (h : ∀ x, ¬(P x ∧ R x)) :
    outcomeMass (fun x => P x ∨ R x) ψ=outcomeMass P ψ+outcomeMass R ψ := by
  classical
  unfold outcomeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases hr : R x
  · exact False.elim (h x ⟨hp,hr⟩)
  all_goals simp [hp,hr]

end ExactQuantumFactoring


end

end OAI
