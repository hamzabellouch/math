import OAI.Combinatorics.ExpectationThreshold.Model

namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_empty (p : ℝ) : cost p (∅ : Family α) = 0 := by
  simp [cost]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_singleton (p : ℝ) (S : Finset α) :
    cost p {S} = p ^ S.card := by simp [cost]

omit [Fintype α] [DecidableEq α] in
theorem cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Family α) : 0 ≤ cost p G :=
  Finset.sum_nonneg (fun S _ => pow_nonneg hp S.card)

omit [Fintype α] [DecidableEq α] in
theorem cost_mono {p : ℝ} (hp : 0 ≤ p) {G H : Family α} (h : G ⊆ H) :
    cost p G ≤ cost p H :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun S _ _ => pow_nonneg hp S.card)

omit [Fintype α] in
theorem cost_union_le {p : ℝ} (hp : 0 ≤ p) (G H : Family α) :
    cost p (G ∪ H) ≤ cost p G + cost p H := by
  calc
    cost p (G ∪ H) ≤ cost p (G ∪ H) + cost p (G ∩ H) :=
      le_add_of_nonneg_right (cost_nonneg hp _)
    _ = cost p G + cost p H := Finset.sum_union_inter

omit [Fintype α] in
theorem cost_biUnion_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Family α) :
    cost p (T.biUnion G) ≤ ∑ i ∈ T, cost p (G i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (cost_union_le hp _ _).trans (add_le_add le_rfl ih)

omit [Fintype α] in
theorem cost_image_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Finset α) :
    cost p (T.image G) ≤ ∑ i ∈ T, p ^ (G i).card := by
  exact Finset.sum_image_le_of_nonneg (fun S _ => pow_nonneg hp S.card)

omit [Fintype α] [DecidableEq α] in
theorem cost_mono_density {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (G : Family α) :
    cost p G ≤ cost r G :=
  Finset.sum_le_sum (fun S _ => pow_le_pow_left₀ hp hpr S.card)

omit [Fintype α] [DecidableEq α] in
theorem covers_self (F : Family α) : Covers F F :=
  fun H hH => ⟨H, hH, Finset.Subset.refl H⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem covers_empty (G : Family α) : Covers G ∅ := by
  intro H hH
  exact False.elim (Finset.notMem_empty H hH)

omit [Fintype α] [DecidableEq α] in
theorem Covers.mono_target {G F E : Family α} (h : Covers G F) (hEF : E ⊆ F) :
    Covers G E := fun H hH => h H (hEF hH)

omit [Fintype α] [DecidableEq α] in
theorem Covers.mono_cover {G K F : Family α} (h : Covers G F) (hGK : G ⊆ K) :
    Covers K F := by
  intro H hH
  obtain ⟨S, hS, hSH⟩ := h H hH
  exact ⟨S, hGK hS, hSH⟩

omit [Fintype α] in
theorem Covers.union {G K F E : Family α} (hGF : Covers G F) (hKE : Covers K E) :
    Covers (G ∪ K) (F ∪ E) := by
  intro H hH
  rcases Finset.mem_union.mp hH with hH | hH
  · obtain ⟨S, hS, hSH⟩ := hGF H hH
    exact ⟨S, Finset.mem_union_left K hS, hSH⟩
  · obtain ⟨S, hS, hSH⟩ := hKE H hH
    exact ⟨S, Finset.mem_union_right G hS, hSH⟩

omit [Fintype α] [DecidableEq α] in
theorem small_empty (p : ℝ) : Small p (∅ : Family α) := by
  refine ⟨∅, covers_empty _, ?_⟩
  simp

omit [Fintype α] [DecidableEq α] in
theorem Small.mono {F : Family α} {p r : ℝ} (h : Small r F)
    (hp : 0 ≤ p) (hpr : p ≤ r) : Small p F := by
  obtain ⟨G, hG, hcost⟩ := h
  exact ⟨G, hG, (cost_mono_density hp hpr G).trans hcost⟩

omit [Fintype α] [DecidableEq α] in
theorem cost_gt_of_not_small {F G : Family α} {p : ℝ}
    (h : ¬ Small p F) (hG : Covers G F) : 1 / 2 < cost p G :=
  lt_of_not_ge (fun hc => h ⟨G, hG, hc⟩)

omit [Fintype α] [DecidableEq α] in
theorem members_nonempty {F : Family α} (hF : (∅ : Finset α) ∉ F)
    {H : Finset α} (hH : H ∈ F) : H.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  exact hF (he ▸ hH)

omit [Fintype α] [DecidableEq α] in
theorem cost_zero_of_empty_not_mem (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    cost 0 F = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  exact zero_pow (Nat.ne_of_gt (Finset.card_pos.mpr (members_nonempty hF hS)))

omit [Fintype α] [DecidableEq α] in
theorem small_zero (F : Family α) (hF : (∅ : Finset α) ∉ F) : Small 0 F := by
  refine ⟨F, covers_self F, ?_⟩
  rw [cost_zero_of_empty_not_mem F hF]
  exact div_nonneg zero_le_one zero_le_two

omit [DecidableEq α] in
theorem Increasing.empty_not_mem {F : Family α} (hF : Increasing F)
    (hproper : F ≠ Finset.univ) : (∅ : Finset α) ∉ F := by
  intro hempty
  apply hproper
  apply Finset.eq_univ_iff_forall.mpr
  intro H
  exact hF ∅ hempty H (Finset.empty_subset H)

def coverIndicator (G : Family α) (S : Finset α) : ℝ := if S ∈ G then 1 else 0

omit [Fintype α] in
theorem coverIndicator_nonneg (G : Family α) (S : Finset α) :
    0 ≤ coverIndicator G S := by
  unfold coverIndicator
  split_ifs <;> simp

omit [Fintype α] in
theorem coverIndicator_le_one (G : Family α) (S : Finset α) :
    coverIndicator G S ≤ 1 := by
  unfold coverIndicator
  split_ifs <;> simp

omit [Fintype α] in
theorem Covers.fractionalCover {G F : Family α} (h : Covers G F) :
    FractionalCover F (coverIndicator G) := by
  constructor
  · intro S
    exact ⟨coverIndicator_nonneg G S, coverIndicator_le_one G S⟩
  · intro H hH
    obtain ⟨S, hSG, hSH⟩ := h H hH
    have hs := Finset.single_le_sum (fun T _ => coverIndicator_nonneg G T)
      (Finset.mem_powerset.mpr hSH)
    simpa only [coverIndicator, ite_eq_left hSG] using hs

theorem fracCost_coverIndicator (p : ℝ) (G : Family α) :
    fracCost p (coverIndicator G) = cost p G := by
  classical
  unfold fracCost cost
  calc
    (∑ S : Finset α, coverIndicator G S * p ^ S.card) =
        ∑ S : Finset α, if S ∈ G then p ^ S.card else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ∈ G <;> simp [coverIndicator, hS]
    _ = ∑ S ∈ G, p ^ S.card := Finset.sum_ite_mem_eq G (fun S => p ^ S.card)

theorem Small.fractionalSmall {F : Family α} {p : ℝ} (h : Small p F) :
    FractionalSmall p F := by
  obtain ⟨G, hG, hcost⟩ := h
  exact ⟨coverIndicator G, hG.fractionalCover, (fracCost_coverIndicator p G).trans_le hcost⟩

theorem fractionalSmall_zero (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    FractionalSmall 0 F := (small_zero F hF).fractionalSmall

omit [Fintype α] [DecidableEq α] in
theorem FractionalCover.nonneg {F : Family α} {g : Finset α → ℝ}
    (h : FractionalCover F g) (S : Finset α) : 0 ≤ g S := (h.1 S).1

omit [Fintype α] [DecidableEq α] in
theorem FractionalCover.le_one {F : Family α} {g : Finset α → ℝ}
    (h : FractionalCover F g) (S : Finset α) : g S ≤ 1 := (h.1 S).2

omit [DecidableEq α] in
theorem fracCost_nonneg {p : ℝ} {g : Finset α → ℝ}
    (hp : 0 ≤ p) (hg : ∀ S, 0 ≤ g S) : 0 ≤ fracCost p g :=
  Finset.sum_nonneg (fun S _ => mul_nonneg (hg S) (pow_nonneg hp S.card))

omit [DecidableEq α] in
theorem fracCost_mono_density {p r : ℝ} {g : Finset α → ℝ}
    (hg : ∀ S, 0 ≤ g S) (hp : 0 ≤ p) (hpr : p ≤ r) :
    fracCost p g ≤ fracCost r g :=
  Finset.sum_le_sum (fun S _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpr S.card) (hg S))

omit [DecidableEq α] in
theorem FractionalSmall.mono {F : Family α} {p r : ℝ} (h : FractionalSmall r F)
    (hp : 0 ≤ p) (hpr : p ≤ r) : FractionalSmall p F := by
  obtain ⟨g, hg, hcost⟩ := h
  exact ⟨g, hg, (fracCost_mono_density hg.nonneg hp hpr).trans hcost⟩

omit [DecidableEq α] in
theorem empty_weight_le_fracCost {p : ℝ} {g : Finset α → ℝ}
    (hp : 0 ≤ p) (hg : ∀ S, 0 ≤ g S) : g ∅ ≤ fracCost p g := by
  have h := Finset.single_le_sum
    (fun S (_ : S ∈ (Finset.univ : Finset (Finset α))) =>
      mul_nonneg (hg S) (pow_nonneg hp S.card))
    (Finset.mem_univ (∅ : Finset α))
  simpa only [fracCost, Finset.card_empty, pow_zero, mul_one] using h

end
end TalagrandThreshold

end OAI
