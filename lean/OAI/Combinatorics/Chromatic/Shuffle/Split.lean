import Mathlib

namespace OAI

section
namespace ElementaryPositivity.ShuffleConvolution
variable {A R : Type*} [Fintype A] [DecidableEq A] [CommSemiring R]

def Split (s : Finset A) := {p : Finset A × Finset A // Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = s}
instance (s : Finset A) : Fintype (Split s) := by unfold Split; infer_instance
instance (s : Finset A) : DecidableEq (Split s) := by unfold Split; infer_instance

omit [Fintype A] in
lemma Split.left_subset {s : Finset A} (p : Split s) : p.val.1 ⊆ s := by
  intro a ha
  have hm := Finset.mem_union_left p.val.2 ha
  simpa only [p.property.2] using hm
omit [Fintype A] in
lemma Split.right_subset {s : Finset A} (p : Split s) : p.val.2 ⊆ s := by
  intro a ha
  have hm := Finset.mem_union_right p.val.1 ha
  simpa only [p.property.2] using hm

abbrev LeftIndex (s : Finset A) := Σ p : Split s, Split p.val.1
abbrev RightIndex (s : Finset A) := Σ p : Split s, Split p.val.2

def rebracket (s : Finset A) : LeftIndex s ≃ RightIndex s where
  toFun z := by
    let a := z.2.val.1
    let b := z.2.val.2
    let c := z.1.val.2
    have hab : Disjoint a b := z.2.property.1
    have hac : Disjoint a c := z.1.property.1.mono_left z.2.left_subset
    have hbc : Disjoint b c := z.1.property.1.mono_left z.2.right_subset
    have hu : a ∪ (b ∪ c) = s := by
      rw [← Finset.union_assoc, z.2.property.2, z.1.property.2]
    exact ⟨⟨(a,b∪c),⟨Finset.disjoint_union_right.mpr ⟨hab,hac⟩,hu⟩⟩,
      ⟨(b,c),⟨hbc,rfl⟩⟩⟩
  invFun z := by
    let a := z.1.val.1
    let b := z.2.val.1
    let c := z.2.val.2
    have hab : Disjoint a b := z.1.property.1.mono_right z.2.left_subset
    have hac : Disjoint a c := z.1.property.1.mono_right z.2.right_subset
    have hbc : Disjoint b c := z.2.property.1
    have hu : (a∪b)∪c = s := by
      rw [Finset.union_assoc, z.2.property.2, z.1.property.2]
    exact ⟨⟨(a∪b,c),⟨Finset.disjoint_union_left.mpr ⟨hac,hbc⟩,hu⟩⟩,
      ⟨(a,b),⟨hab,rfl⟩⟩⟩
  left_inv z := by
    rcases z with ⟨⟨⟨ab,c⟩,hac,hu⟩,⟨⟨a,b⟩,hab,habu⟩⟩
    dsimp at habu
    subst ab
    rfl
  right_inv z := by
    rcases z with ⟨⟨⟨a,bc⟩,hac,hu⟩,⟨⟨b,c⟩,hbc,hbcu⟩⟩
    dsimp at hbcu
    subst bc
    rfl

def kernel (w : A → A → R) (a b : Finset A) : R := ∏ x ∈ a, ∏ y ∈ b, w x y

omit [Fintype A] in
lemma kernel_union_left (w : A → A → R) (a b c : Finset A) (hab : Disjoint a b) :
    kernel w (a∪b) c = kernel w a c * kernel w b c := by
  exact Finset.prod_union hab

omit [Fintype A] in
lemma kernel_union_right (w : A → A → R) (a b c : Finset A) (hbc : Disjoint b c) :
    kernel w a (b∪c) = kernel w a b * kernel w a c := by
  simp only [kernel, Finset.prod_union hbc, Finset.prod_mul_distrib]

omit [Fintype A] in
lemma kernel_cocycle (w : A → A → R) (a b c : Finset A)
    (hab : Disjoint a b) (hbc : Disjoint b c) :
    kernel w a b * kernel w (a∪b) c =
      kernel w b c * kernel w a (b∪c) := by
  rw [kernel_union_left w a b c hab, kernel_union_right w a b c hbc]
  ac_rfl

def shuffle (w : A → A → R) (f g : Finset A → R) (s : Finset A) : R :=
  ∑ p : Split s, f p.val.1 * g p.val.2 * kernel w p.val.1 p.val.2

lemma shuffle_assoc (w : A → A → R) (f g h : Finset A → R) :
    shuffle w (shuffle w f g) h = shuffle w f (shuffle w g h) := by
  funext s
  have lhs : shuffle w (shuffle w f g) h s =
      ∑ z : LeftIndex s,
        (f z.2.val.1 * g z.2.val.2 * kernel w z.2.val.1 z.2.val.2) *
          h z.1.val.2 * kernel w z.1.val.1 z.1.val.2 := by
    simp only [shuffle, Fintype.sum_sigma, Finset.sum_mul]
  have rhs : shuffle w f (shuffle w g h) s =
      ∑ z : RightIndex s,
        f z.1.val.1 * (g z.2.val.1 * h z.2.val.2 * kernel w z.2.val.1 z.2.val.2) *
          kernel w z.1.val.1 z.1.val.2 := by
    simp only [shuffle, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul]
  rw [lhs,rhs,← (rebracket s).sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  change (f z.2.val.1 * g z.2.val.2 * kernel w z.2.val.1 z.2.val.2) *
      h z.1.val.2 * kernel w z.1.val.1 z.1.val.2 =
    f z.2.val.1 * (g z.2.val.2 * h z.1.val.2 * kernel w z.2.val.2 z.1.val.2) *
      kernel w z.2.val.1 (z.2.val.2 ∪ z.1.val.2)
  have hc := kernel_cocycle w z.2.val.1 z.2.val.2 z.1.val.2 z.2.property.1
    (z.1.property.1.mono_left z.2.right_subset)
  rw [z.2.property.2] at hc
  calc
    _ = (f z.2.val.1 * g z.2.val.2 * h z.1.val.2) *
        (kernel w z.2.val.1 z.2.val.2 * kernel w z.1.val.1 z.1.val.2) := by ac_rfl
    _ = _ := by rw [hc]; ac_rfl

lemma shuffle_add_left (w : A → A → R) (f f' g : Finset A → R) :
    shuffle w (f+f') g = shuffle w f g + shuffle w f' g := by
  funext s
  simp only [shuffle, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma shuffle_add_right (w : A → A → R) (f g g' : Finset A → R) :
    shuffle w f (g+g') = shuffle w f g + shuffle w f g' := by
  funext s
  simp only [shuffle, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma shuffle_supported_degree (w : A → A → R) (f g : Finset A → R) (d e : ℕ)
    (hf : ∀ s, s.card ≠ d → f s = 0) (hg : ∀ s, s.card ≠ e → g s = 0) :
    ∀ s, s.card ≠ d+e → shuffle w f g s = 0 := by
  intro s hs
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hpd : p.val.1.card = d
  · have hpe : p.val.2.card ≠ e := by
      intro he
      apply hs
      rw [← p.property.2, Finset.card_union_of_disjoint p.property.1, hpd, he]
    simp [hg _ hpe]
  · simp [hf _ hpd]

end ElementaryPositivity.ShuffleConvolution

end

end OAI
