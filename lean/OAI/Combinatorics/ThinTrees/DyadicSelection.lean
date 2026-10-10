import OAI.Combinatorics.ThinTrees.ThresholdChain

namespace OAI

section

namespace StrongThinTree.Dyadic
noncomputable section
open Finset

def selected (M : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  ((range (z+1)).filter (fun i => 0 < M i)).filter
    (fun i => ∀j ≤ z, 0 < M j → Nat.log 2 (M j)=Nat.log 2 (M i) → i ≤ j)

lemma selected_spec {M : ℕ → ℕ} {z i : ℕ} (hi : i ∈ selected M z) :
    i ≤ z ∧ 0 < M i ∧ ∀j ≤ z, 0 < M j → Nat.log 2 (M j)=Nat.log 2 (M i) → i ≤ j := by
  simp only [selected,mem_filter,mem_range] at hi
  exact ⟨by omega,hi.1.2,hi.2⟩

lemma selected_injective (M : ℕ → ℕ) (z : ℕ) :
    Set.InjOn (fun i => Nat.log 2 (M i)) (selected M z) := by
  intro i hi j hj h
  obtain ⟨hiz,hip,himin⟩ := selected_spec hi
  obtain ⟨hjz,hjp,hjmin⟩ := selected_spec hj
  exact Nat.le_antisymm (himin j hjz hjp h.symm) (hjmin i hiz hip h)

lemma representative {M : ℕ → ℕ} {z i : ℕ} (hiz : i ≤ z) (hip : 0 < M i) :
    ∃j ∈ selected M z, j ≤ i ∧ Nat.log 2 (M j)=Nat.log 2 (M i) := by
  classical
  let C := (range (z+1)).filter (fun j => 0 < M j ∧ Nat.log 2 (M j)=Nat.log 2 (M i))
  have hi : i ∈ C := mem_filter.mpr ⟨mem_range.mpr (by omega),hip,rfl⟩
  let j := C.min' ⟨i,hi⟩
  have hj : j ∈ C := min'_mem _ _
  obtain ⟨hjz,hjp,hlog⟩ := mem_filter.mp hj
  refine ⟨j,?_,min'_le _ _ hi,hlog⟩
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hjz,hjp⟩,?_⟩
  intro k hk hkp hkl
  exact min'_le C k (mem_filter.mpr ⟨mem_range.mpr (by omega),hkp,hkl.trans hlog⟩)

lemma same_bin_ratio {a b : ℕ} (hb : 0 < b) (h : Nat.log 2 a=Nat.log 2 b) : a < 2*b := by
  have ha := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
  have hl := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
  rw [h,pow_succ] at ha
  omega

lemma tail_bound {M : ℕ → ℕ} {z : ℕ} (hmono : Antitone M) {i : ℕ}
    (hi : i ∈ selected M z) :
    (∑j ∈ (selected M z).filter (fun j => i ≤ j), (M j : ℝ)) ≤ 4*(M i : ℝ) := by
  classical
  let J := (selected M z).filter (fun j => i ≤ j)
  let a := Nat.log 2 (M i)
  have hinj : Set.InjOn (fun j => Nat.log 2 (M j)) J :=
    (selected_injective M z).mono (filter_subset _ _)
  have hsub : J.image (fun j => Nat.log 2 (M j)) ⊆ range (a+1) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hmono (mem_filter.mp hj).2)))
  have hpow : (2 : ℝ)^a ≤ (M i : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt (selected_spec hi).2.1)
  calc
    (∑j ∈ J, (M j : ℝ)) ≤ ∑j ∈ J, (2 : ℝ)^(Nat.log 2 (M j)+1) := by
      apply sum_le_sum
      intro j _
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (M j)).le
    _ = ∑b ∈ J.image (fun j => Nat.log 2 (M j)), (2 : ℝ)^(b+1) :=
      (sum_image (f := fun b => (2 : ℝ)^(b+1)) hinj).symm
    _ ≤ ∑b ∈ range (a+1), (2 : ℝ)^(b+1) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 2*((2 : ℝ)^(a+1)-1) := by
      simp_rw [pow_succ]
      rw [←Finset.sum_mul,geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) (a+1)]
      ring
    _ ≤ 4*(M i : ℝ) := by rw [pow_succ]; nlinarith

end
end StrongThinTree.Dyadic

end

end OAI
