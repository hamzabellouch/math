import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinLog

namespace OAI

/-! Finite magnetization slices for an arbitrary grouping of the sites.
Constant group fields factor exactly, with the original cube mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def spinGroupSize {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => group i = a).card

def spinGroupCount {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (σ : Spin N) (a : A) : ℕ :=
  (Finset.univ.filter fun i => group i = a ∧ σ i = true).card

def spinGroupSlice {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) : Finset (Spin N) :=
  Finset.univ.filter fun σ => ∀ a, spinGroupCount group σ a = k a

lemma spinGroupSlice_nonempty {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) :
    (spinGroupSlice group k).Nonempty := by
  classical
  choose S hS hcard using fun a => Finset.exists_subset_card_eq (hk a)
  let σ : Spin N := fun i => decide (i ∈ S (group i))
  refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => ?_⟩⟩
  have he : (Finset.univ.filter fun i => group i = a ∧ σ i = true) = S a := by
    ext i
    constructor
    · intro hi
      obtain ⟨_, hga, hpos⟩ := Finset.mem_filter.mp hi
      have hm : i ∈ S (group i) := of_decide_eq_true hpos
      simpa only [hga] using hm
    · intro hi
      have hga : group i = a := (Finset.mem_filter.mp (hS a hi)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hga, ?_⟩
      change decide (i ∈ S (group i)) = true
      exact decide_eq_true (by simpa only [hga] using hi)
  exact (congrArg Finset.card he).trans (hcard a)

lemma sum_spinValue_eq_count {N : ℕ} (S : Finset (Fin N)) (σ : Spin N) :
    (∑ i ∈ S, spinValue (σ i)) =
      2 * ((S.filter fun i => σ i = true).card : ℝ) - S.card := by
  have hi (i : Fin N) : spinValue (σ i) = (if σ i = true then 2 else 0) - 1 := by
    cases hσ : σ i <;> norm_num [spinValue]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite, mul_comm]

lemma fieldEnergy_group_counts {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (b : A → ℝ) (σ : Spin N) :
    fieldEnergy (fun i => b (group i)) σ =
      ∑ a, b a * (2 * (spinGroupCount group σ a : ℝ) - spinGroupSize group a) := by
  rw [fieldEnergy, ← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => group i = a), b a * spinValue (σ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = b a * (∑ i ∈ Finset.univ.filter (fun i => group i = a), spinValue (σ i)) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_spinValue_eq_count]
      simp only [Finset.filter_filter, spinGroupCount, spinGroupSize]

def spinGroupFieldConstant {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (b : A → ℝ) : ℝ :=
  ∑ a, b a * (2 * (k a : ℝ) - spinGroupSize group a)

lemma fieldEnergy_on_group_slice {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (b : A → ℝ) {σ : Spin N}
    (hσ : σ ∈ spinGroupSlice group k) :
    fieldEnergy (fun i => b (group i)) σ = spinGroupFieldConstant group k b := by
  have hk := (Finset.mem_filter.mp hσ).2
  rw [fieldEnergy_group_counts]
  simp only [hk, spinGroupFieldConstant]

lemma restrictedSpinLog_group_field {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (b : A → ℝ) (H : Spin N → ℝ) :
    restrictedSpinLog (spinGroupSlice group k) (fun σ => H σ + fieldEnergy (fun i => b (group i)) σ) =
      restrictedSpinLog (spinGroupSlice group k) H + spinGroupFieldConstant group k b := by
  rw [← restrictedSpinLog_add_const _ (spinGroupSlice_nonempty group k hk)]
  unfold restrictedSpinLog
  congr 2
  apply Finset.sum_congr rfl
  intro σ hσ
  dsimp only
  rw [fieldEnergy_on_group_slice group k b hσ]

end InvariantIsing

end

end OAI
