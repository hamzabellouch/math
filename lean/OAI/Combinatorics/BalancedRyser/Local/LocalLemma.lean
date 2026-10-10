import Mathlib

namespace OAI

namespace Balanced.LocalLemma

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

theorem extension_lower_bound (a : Finset ι → ℝ) (r : ι → ℝ)
    (S : Finset ι) (hr : ∀ i ∈ S, 0 ≤ r i)
    (hstep : ∀ T ⊆ S, ∀ i ∈ S, i ∉ T → a T * r i ≤ a (insert i T))
    (T : Finset ι) (hTS : T ⊆ S) :
    a T * ∏ i ∈ S \ T, r i ≤ a S := by
  have haux : ∀ U : Finset ι, U ⊆ S → Disjoint T U →
      a T * ∏ i ∈ U, r i ≤ a (T ∪ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
      intro hUS hd
      have hiS : i ∈ S := hUS (by simp)
      have hUi : U ⊆ S := fun j hj => hUS (by simp [hj])
      have hdi : i ∉ T := by
        intro hiT
        exact Finset.disjoint_left.mp hd hiT (by simp)
      have hdU : Disjoint T U := hd.mono_right (by intro j hj; simp [hj])
      have hiTU : i ∉ T ∪ U := by simp [hdi, hi]
      have hTU : T ∪ U ⊆ S := Finset.union_subset hTS hUi
      calc
        a T * ∏ j ∈ insert i U, r j = (a T * ∏ j ∈ U, r j) * r i := by
          rw [Finset.prod_insert hi]; ring
        _ ≤ a (T ∪ U) * r i := mul_le_mul_of_nonneg_right (ih hUi hdU) (hr i hiS)
        _ ≤ a (insert i (T ∪ U)) := hstep (T ∪ U) hTU i hiS hiTU
        _ = a (T ∪ insert i U) := by rw [Finset.union_insert]
  simpa [Finset.union_sdiff_of_subset hTS] using
    haux (S \ T) Finset.sdiff_subset (by simp [Finset.disjoint_left]; tauto)

theorem avoidance_induction (a : Finset ι → ℝ) (p x : ι → ℝ)
    (N : ι → Finset ι)
    (hempty : a ∅ = 1)
    (ha : ∀ S, 0 ≤ a S)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hdep : ∀ S i, i ∉ S →
      a S - a (insert i S) ≤ p i * a (S \ N i)) :
    ∀ S, 0 < a S ∧ ∀ i, i ∉ S →
      a S * (1 - x i) ≤ a (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hstep : ∀ T ⊆ S, ∀ i ∈ S, i ∉ T →
        a T * (1 - x i) ≤ a (insert i T) := by
      intro T hTS i hiS hiT
      have hproper : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS, by
        intro heq; exact hiT (heq ▸ hiS)⟩
      exact (ih T hproper).2 i hiT
    have hpositive : 0 < a S := by
      have hlower := extension_lower_bound a (fun i => 1 - x i) S
        (fun i _ => le_of_lt (sub_pos.mpr (hx1 i))) hstep ∅ (Finset.empty_subset S)
      have hprod : 0 < ∏ i ∈ S, (1 - x i) :=
        Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))
      simpa [hempty] using lt_of_lt_of_le hprod (by simpa [hempty] using hlower)
    refine ⟨hpositive, ?_⟩
    intro i hiS
    have hratio := extension_lower_bound a (fun j => 1 - x j) S
      (fun j _ => le_of_lt (sub_pos.mpr (hx1 j))) hstep
      (S \ N i) Finset.sdiff_subset
    have hprod : 0 < ∏ j ∈ S \ (S \ N i), (1 - x j) :=
      Finset.prod_pos (fun j _ => sub_pos.mpr (hx1 j))
    have hsubset : S \ (S \ N i) ⊆ N i := by
      intro j hj
      simp only [Finset.mem_sdiff] at hj
      by_contra hjN
      exact hj.2 ⟨hj.1, hjN⟩
    have hprod_le : (∏ j ∈ N i, (1 - x j)) ≤
        ∏ j ∈ S \ (S \ N i), (1 - x j) := by
      exact Finset.prod_le_prod_of_subset_of_le_one₀ hsubset
        (fun j _ => le_of_lt (sub_pos.mpr (hx1 j)))
        (fun j _ _ => by linarith [hx0 j])
    have hpi : p i ≤ x i * ∏ j ∈ S \ (S \ N i), (1 - x j) :=
      (hp i).trans (mul_le_mul_of_nonneg_left hprod_le (hx0 i))
    have hbound : p i * a (S \ N i) ≤ x i * a S := by
      calc
        p i * a (S \ N i) ≤
            (x i * ∏ j ∈ S \ (S \ N i), (1 - x j)) * a (S \ N i) :=
          mul_le_mul_of_nonneg_right hpi (ha _)
        _ = x i * (a (S \ N i) * ∏ j ∈ S \ (S \ N i), (1 - x j)) := by ring
        _ ≤ x i * a S := mul_le_mul_of_nonneg_left hratio (hx0 i)
    have hd := (hdep S i hiS).trans hbound
    nlinarith

end Balanced.LocalLemma

end OAI
