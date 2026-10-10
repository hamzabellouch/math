import Mathlib

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FiniteWeightedChoiceBox

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}

noncomputable def points (P : ∀ i,Finset (α i)) : Finset (∀ i,α i) := Fintype.piFinset P
noncomputable def pointWeight (W : ∀ i,α i → ℝ) (f : ∀ i,α i) : ℝ := ∏ i,W i (f i)
noncomputable def boxMass (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ) : ℝ :=
  ∑ f ∈ points P,pointWeight W f
noncomputable def restrictedPoints (P : ∀ i,Finset (α i)) (S : Finset ι) (E : ∀ i,α i → Prop) :
    Finset (∀ i,α i) := (points P).filter (fun f => ∀ i ∈ S,E i (f i))

theorem mass_factorizes (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ) :
    boxMass P W=∏ i,∑ x ∈ P i,W i x := (Finset.prod_univ_sum P W).symm

omit [DecidableEq ι] in
theorem weight_nonnegative (W : ∀ i,α i → ℝ) (hW : ∀ i x,0 ≤ W i x) (f : ∀ i,α i) :
    0 ≤ pointWeight W f := Finset.prod_nonneg (fun i _ => hW i (f i))

theorem restricted_eq (P : ∀ i,Finset (α i)) (S : Finset ι) (E : ∀ i,α i → Prop) :
    restrictedPoints P S E=points (fun i => if i ∈ S then (P i).filter (E i) else P i) := by
  ext f
  simp only [restrictedPoints,points,Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hp,he⟩ i
    by_cases hi : i ∈ S
    · simpa only [ite_eq_left hi,Finset.mem_filter] using And.intro (hp i) (he i hi)
    · simpa only [ite_eq_right hi] using hp i
  · intro hf
    constructor
    · intro i
      have hh := hf i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at hh; exact (Finset.mem_filter.mp hh).1
      · rwa [ite_eq_right hi] at hh
    · intro i hi
      have hh := hf i
      rw [ite_eq_left hi] at hh
      exact (Finset.mem_filter.mp hh).2

theorem restriction_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (S : Finset ι) (E : ∀ i,α i → Prop) (c : ℝ)
    (hcoord : ∀ i ∈ S,(∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ restrictedPoints P S E,pointWeight W f) ≤ c^S.card*boxMass P W := by
  rw [restricted_eq]
  change boxMass (fun i => if i ∈ S then (P i).filter (E i) else P i) W ≤ _
  rw [mass_factorizes,mass_factorizes]
  calc
    _ ≤ ∏ i,(if i ∈ S then c else 1)*(∑ x ∈ P i,W i x) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun x _ => hW i x)
      · intro i _
        by_cases hi : i ∈ S
        · simp only [ite_eq_left hi]
          exact hcoord i hi
        · simp only [ite_eq_right hi,one_mul,le_refl]
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_ite_mem_eq]; simp

theorem coordinate_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (E : ∀ i,α i → Prop) (i : ι) (c : ℝ)
    (hi : (∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ (points P).filter (fun f => E i (f i)),pointWeight W f) ≤ c*boxMass P W := by
  have hh := restriction_mass_bound P W hW {i} E c (fun j hj => by
    have he : j=i := Finset.mem_singleton.mp hj
    subst j
    exact hi)
  simpa only [restrictedPoints,Finset.mem_singleton,forall_eq,Finset.card_singleton,pow_one] using hh

theorem union_mass_bound (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ)
    (hW : ∀ i x,0 ≤ W i x) (S : Finset ι) (E : ∀ i,α i → Prop) (c : ℝ)
    (hcoord : ∀ i ∈ S,(∑ x ∈ (P i).filter (E i),W i x) ≤ c*(∑ x ∈ P i,W i x)) :
    (∑ f ∈ (points P).filter (fun f => ∃ i ∈ S,E i (f i)),pointWeight W f) ≤
      (S.card:ℝ)*c*boxMass P W := by
  have hu : (∑ f ∈ (points P).filter (fun f => ∃ i ∈ S,E i (f i)),pointWeight W f) ≤
      ∑ i ∈ S,∑ f ∈ (points P).filter (fun f => E i (f i)),pointWeight W f := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f _hf
    by_cases he : ∃ i ∈ S,E i (f i)
    · rw [ite_eq_left he]
      obtain ⟨i,hi,hei⟩ := he
      have hh := Finset.single_le_sum (s := S) (f := fun j => if E j (f j) then pointWeight W f else 0)
        (fun j _ => by split_ifs; exact weight_nonnegative W hW f; rfl) hi
      simpa only [ite_eq_left hei] using hh
    · rw [ite_eq_right he]
      exact Finset.sum_nonneg (fun j _ => by split_ifs; exact weight_nonnegative W hW f; rfl)
  apply hu.trans
  calc
    _ ≤ ∑ _i ∈ S,c*boxMass P W := Finset.sum_le_sum (fun i hi => coordinate_mass_bound P W hW E i c (hcoord i hi))
    _ = _ := by simp [mul_assoc]
end NumberTheoryLean.FiniteWeightedChoiceBox


end Erdos970

end OAI
