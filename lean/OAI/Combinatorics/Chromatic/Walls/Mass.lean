import Mathlib

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

def mass (c : I → ℝ) (d : I → ℕ) : ℝ := ∑ i,(d i : ℝ) * c i

noncomputable def slope (c η : I → ℝ) (d : I → ℕ) : ℝ := mass η d / mass c d

lemma mass_add (c : I → ℝ) (d e : I → ℕ) : mass c (d+e) = mass c d + mass c e := by
  simp [mass,Nat.cast_add,add_mul,Finset.sum_add_distrib]

@[simp] lemma mass_zero (c : I → ℝ) : mass c 0 = 0 := by simp [mass]

lemma mass_nonneg (c : I → ℝ) (hc : ∀ i,0 ≤ c i) (d : I → ℕ) : 0 ≤ mass c d := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (hc i)

lemma mass_pos (c : I → ℝ) (hc : ∀ i,0 < c i) (d : I → ℕ) (hd : d ≠ 0) :
    0 < mass c d := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,d i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hd
    funext i
    exact hn i
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (Nat.cast_nonneg _) (hc j).le
  · exact ⟨i,Finset.mem_univ _,mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (hc i)⟩

lemma mass_eq (c η : I → ℝ) (hc : ∀ i,0 < c i) (d : I → ℕ) :
    mass η d = slope c η d * mass c d := by
  by_cases hd : d=0
  · subst d; simp
  · exact (div_mul_cancel₀ _ (mass_pos c hc d hd).ne').symm

omit [Fintype I] in
lemma add_ne_zero_left (d e : I → ℕ) (hd : d ≠ 0) : d+e ≠ 0 := by
  intro h
  apply hd
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply,Pi.zero_apply] at hi
  change d i = 0
  omega

omit [Fintype I] in
lemma add_ne_zero_right (d e : I → ℕ) (he : e ≠ 0) : d+e ≠ 0 := by
  rw [add_comm]
  exact add_ne_zero_left e d he

lemma slope_add (c η : I → ℝ) (hc : ∀ i,0 < c i) {d e : I → ℕ}
    (hd : d ≠ 0) (hs : slope c η d = slope c η e) :
    slope c η (d+e) = slope c η d := by
  apply (div_eq_iff (mass_pos c hc (d+e) (add_ne_zero_left d e hd)).ne').mpr
  rw [mass_add,mass_add,mass_eq c η hc d,mass_eq c η hc e,← hs]
  ring

lemma slope_add_same (c η : I → ℝ) (hc : ∀ i,0 < c i) {d e : I → ℕ}
    (hs : slope c η d = slope c η e) :
    slope c η (d+e) = slope c η d := by
  by_cases hd : d=0
  · subst d
    simpa using hs.symm
  · exact slope_add c η hc hd hs

lemma slope_add_gt (c η : I → ℝ) (hc : ∀ i,0 < c i) {d u : I → ℕ}
    (hu : u ≠ 0) {θ : ℝ} (hd : mass η d = θ * mass c d)
    (hs : slope c η u > θ) : slope c η (d+u) > θ := by
  have hmass := mass_pos c hc u hu
  have hu' : mass η u > θ * mass c u := (lt_div_iff₀ hmass).mp hs
  apply (lt_div_iff₀ (mass_pos c hc (d+u) (add_ne_zero_right d u hu))).mpr
  rw [mass_add,mass_add,hd,mul_add]
  linarith

lemma mass_sum_le {J : Type*} [Fintype J] (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d : J → I → ℕ) (θ : ℝ) (h : ∀ j,d j ≠ 0 → slope c η (d j) ≤ θ) :
    (∑ j,mass η (d j)) ≤ θ * ∑ j,mass c (d j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hd : d j=0
  · simp [hd]
  · exact (div_le_iff₀ (mass_pos c hc (d j) hd)).mp (h j hd)

end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma destabilized_target (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hs : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hd : d₁+d₂≠0) (hμ : slope c η (d₁+d₂) > slope c η (d₁+e₁)) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁ > slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂ > slope c η (d₂+e₂)) := by
  have ht : mass η (d₁+d₂) > slope c η (d₁+e₁) * mass c (d₁+d₂) :=
    (lt_div_iff₀ (mass_pos c hc _ hd)).mp hμ
  rw [mass_add,mass_add,mul_add] at ht
  have hex : mass η d₁ > slope c η (d₁+e₁) * mass c d₁ ∨
      mass η d₂ > slope c η (d₂+e₂) * mass c d₂ := by
    rw [← hs]
    by_contra hn
    push Not at hn
    linarith
  rcases hex with h | h
  · left
    have hdn : d₁≠0 := by intro hh; simp [hh] at h
    have hen : e₁≠0 := by
      intro hh
      rw [hh,add_zero,mass_eq c η hc d₁] at h
      exact (lt_irrefl _ h)
    exact ⟨hdn,hen,(lt_div_iff₀ (mass_pos c hc _ hdn)).mpr h⟩
  · right
    have hdn : d₂≠0 := by intro hh; simp [hh] at h
    have hen : e₂≠0 := by
      intro hh
      rw [hh,add_zero,mass_eq c η hc d₂] at h
      exact (lt_irrefl _ h)
    exact ⟨hdn,hen,(lt_div_iff₀ (mass_pos c hc _ hdn)).mpr h⟩
end ElementaryPositivity.SlopeArithmetic

end

end OAI
