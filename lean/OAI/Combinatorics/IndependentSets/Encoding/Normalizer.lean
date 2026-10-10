import Mathlib

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

noncomputable def normalizer (m : ℕ) (ρ : ℝ) : ℝ := ∑ k : Fin (m+1), ρ^k.val
noncomputable def levelMass (m : ℕ) (ρ : ℝ) (k : Fin (m+1)) : ℝ :=
  ρ^k.val / normalizer m ρ
noncomputable def mass {ι : Type*} [Fintype ι] (m : ℕ) (ρ : ℝ)
    (t : ι → Fin (m+1)) : ℝ := ∏ i, levelMass m ρ (t i)

lemma normalizer_pos (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < normalizer m ρ := by
  apply Finset.sum_pos'
  · intro i _
    exact pow_nonneg hρ _
  · exact ⟨0, Finset.mem_univ _, by simp⟩

lemma levelMass_pos (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (k : Fin (m+1)) :
    0 < levelMass m ρ k := div_pos (pow_pos hρ _) (normalizer_pos m hρ.le)

lemma levelMass_nonneg (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : Fin (m+1)) :
    0 ≤ levelMass m ρ k := div_nonneg (pow_nonneg hρ _) (normalizer_pos m hρ).le

lemma levelMass_total (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ k, levelMass m ρ k = 1 := by
  simp only [levelMass, ← Finset.sum_div]
  exact div_self (normalizer_pos m hρ).ne'

lemma mass_nonneg {ι : Type*} [Fintype ι] (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (t : ι → Fin (m+1)) : 0 ≤ mass m ρ t :=
  Finset.prod_nonneg (fun _ _ => levelMass_nonneg m hρ _)

lemma mass_total {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ t : ι → Fin (m+1), mass m ρ t = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp [levelMass_total m hρ]

noncomputable def lower {ι : Type*} [DecidableEq ι] {m : ℕ}
    (i : ι) (t : ι → Fin (m+1)) : ι → Fin (m+1) :=
  Function.update t i ⟨(t i).val - 1, by omega⟩

lemma lower_injective_on_positive {ι : Type*} [DecidableEq ι] {m : ℕ} (i : ι)
    {t u : ι → Fin (m+1)} (ht : 0 < (t i).val) (hu : 0 < (u i).val)
    (he : lower i t = lower i u) : t = u := by
  funext j
  by_cases hji : j = i
  · subst j
    have h := congrArg (fun v => (v i).val) he
    simp only [lower, Function.update_self] at h
    exact Fin.ext (by omega)
  · simpa only [lower, Function.update_of_ne hji] using congrFun he j

lemma levelMass_lower {m : ℕ} {ρ : ℝ} (k : Fin (m+1)) (hk : 0 < k.val) :
    levelMass m ρ k = ρ * levelMass m ρ ⟨k.val-1, by omega⟩ := by
  dsimp [levelMass]
  have he : k.val = (k.val-1)+1 := by omega
  conv_lhs => rw [he]
  rw [pow_succ]
  ring

lemma mass_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} {ρ : ℝ}
    (i : ι) (t : ι → Fin (m+1)) (ht : 0 < (t i).val) :
    mass m ρ t = ρ * mass m ρ (lower i t) := by
  have he : (fun j => levelMass m ρ (lower i t j)) =
      Function.update (fun j => levelMass m ρ (t j)) i
        (levelMass m ρ ⟨(t i).val - 1, by omega⟩) := by
    funext j
    by_cases hj : j = i <;> simp [lower, hj]
  change ∏ j, levelMass m ρ (t j) = ρ * ∏ j, levelMass m ρ (lower i t j)
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelMass_lower (t i) ht]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem one_level_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ι)
    (high low : (ι → Fin (m+1)) → Prop)
    (hstep : ∀ t, 0 < (t i).val → high t → low (lower i t)) :
    (∑ t ∈ Finset.univ.filter (fun t => 0 < (t i).val ∧ high t), mass m ρ t) ≤
      ρ * ∑ t ∈ Finset.univ.filter low, mass m ρ t := by
  let A := Finset.univ.filter (fun t => 0 < (t i).val ∧ high t)
  have himage : A.image (lower i) ⊆ Finset.univ.filter low := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have ht' := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep t ht'.1 ht'.2⟩
  have hinj : Set.InjOn (lower (m:=m) i) (A : Set (ι → Fin (m+1))) := by
    intro t ht u hu he
    exact lower_injective_on_positive i (Finset.mem_filter.mp ht).2.1
      (Finset.mem_filter.mp hu).2.1 he
  calc
    _ = ρ * ∑ t ∈ A, mass m ρ (lower i t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact mass_lower i t (Finset.mem_filter.mp ht).2.1
    _ = ρ * ∑ u ∈ A.image (lower i), mass m ρ u := by rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg himage (fun u _ _ => mass_nonneg m hρ u)) hρ

theorem positive_coefficient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {ρ β K : ℝ} (hρ : 0 ≤ ρ)
    (D : (ι → Fin (m+1)) → ι → ℝ)
    (hstep : ∀ t i, 0 < (t i).val → |D t i - D (lower i t) i| < β/2)
    (hcount : ∀ t, ((Finset.univ.filter (fun i => β/2 ≤ D t i)).card : ℝ) ≤ K) :
    (∑ t ∈ Finset.univ.filter (fun t => ∃ i, 0 < (t i).val ∧ β ≤ D t i), mass m ρ t) ≤
      ρ*K := by
  let A : ι → Finset (ι → Fin (m+1)) := fun i =>
    Finset.univ.filter (fun t => 0 < (t i).val ∧ β ≤ D t i)
  have hpoint (t : ι → Fin (m+1)) :
      (if ∃ i, 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0) ≤
        ∑ i, if 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0 := by
    split_ifs with ht
    · obtain ⟨i, hi⟩ := ht
      calc
        _ = if 0 < (t i).val ∧ β ≤ D t i then mass m ρ t else 0 := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum (f := fun j : ι =>
            if 0 < (t j).val ∧ β ≤ D t j then mass m ρ t else 0)
          (fun j _ => by split_ifs <;> first | exact mass_nonneg m hρ t | exact le_rfl)
          (Finset.mem_univ i)
    · exact Finset.sum_nonneg (fun i _ => by
        split_ifs <;> first | exact mass_nonneg m hρ t | exact le_rfl)
  calc
    _ ≤ ∑ i, ∑ t ∈ A i, mass m ρ t := by
      simp only [Finset.sum_filter, A]
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun t _ => hpoint t)
    _ ≤ ∑ i, ρ * ∑ t ∈ Finset.univ.filter (fun t => β/2 ≤ D t i), mass m ρ t := by
      apply Finset.sum_le_sum
      intro i _
      apply one_level_event_bound hρ i
      intro t ht hd
      have hs := (abs_lt.mp (hstep t i ht)).2
      linarith
    _ = ρ * ∑ t, mass m ρ t * ((Finset.univ.filter (fun i => β/2 ≤ D t i)).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ρ * ∑ t : ι → Fin (m+1), mass m ρ t * K := by
      apply mul_le_mul_of_nonneg_left _ hρ
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hcount t) (mass_nonneg m hρ t)
    _ = ρ*K := by
      rw [← Finset.sum_mul]
      have hm : (∑ t : ι → Fin (m+1), mass m ρ t) = 1 := mass_total (ι:=ι) m hρ
      rw [hm, one_mul]

end LargeIndependentSets.Coefficient

end OAI
