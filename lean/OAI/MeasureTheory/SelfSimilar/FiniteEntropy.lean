import OAI.MeasureTheory.SelfSimilar.Basic

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

noncomputable def entropy {α : Type uα} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ i ∈ s, Real.negMulLog (p i)

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

noncomputable def mass {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (b : β) : ℝ := ∑ a ∈ s.filter (fun a => f a = b), p a

noncomputable def observableEntropy {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) : ℝ := entropy (s.image f) (mass s p f)

theorem mass_nonneg {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) (b : β) : 0 ≤ mass s p f b := by
  classical
  exact Finset.sum_nonneg (fun a ha => hp a (Finset.mem_filter.mp ha).1)

theorem mass_sum {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ) (f : α → β) :
    ∑ b ∈ s.image f, mass s p f b = ∑ a ∈ s, p a := by
  classical
  simpa only [mass] using
    (Finset.sum_fiberwise_of_maps_to (s := s)
      (fun a ha => Finset.mem_image_of_mem f ha) p)

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem entropy_product {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → ℝ) (q : β → ℝ) (hp : ∑ a ∈ s, p a = 1) (hq : ∑ b ∈ t, q b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 * q ab.2) = entropy s p + entropy t q := by
  simp only [entropy, Finset.sum_product, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, hq, one_mul]

theorem entropy_scale {α : Type uα} (s : Finset α) (p : α → ℝ) (c : ℝ) :
    entropy s (fun a => c * p a) =
      (∑ a ∈ s, p a) * Real.negMulLog c + c * entropy s p := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem entropy_nonneg {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∀ a ∈ s, p a ≤ 1) : 0 ≤ entropy s p :=
  Finset.sum_nonneg (fun a ha => Real.negMulLog_nonneg (hp a ha) (hp1 a ha))

theorem entropy_le_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    entropy s p ≤ Real.log s.card := by
  classical
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hs
    norm_num at hs
  have hn : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hterm : ∀ a ∈ s, (s.card : ℝ) * Real.negMulLog (p a) ≤
      1 - (s.card : ℝ) * p a - p a * Real.negMulLog s.card := by
    intro a ha
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hn.le (hp a ha))
    rw [Real.negMulLog_mul] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hs, mul_one, one_mul, Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) * entropy s p ≤ _ at hsum
  have hneg : Real.negMulLog (s.card : ℝ) = -(s.card : ℝ) * Real.log s.card := rfl
  rw [hneg] at hsum
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

theorem entropy_mixture {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (w : β → ℝ) (p : β → α → ℝ)
    (hw : ∀ b ∈ t, 0 ≤ w b) (hw1 : ∑ b ∈ t, w b = 1)
    (hp : ∀ b ∈ t, ∀ a ∈ s, 0 ≤ p b a) :
    ∑ b ∈ t, w b * entropy s (p b) ≤
      entropy s (fun a => ∑ b ∈ t, w b * p b a) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_sum hw hw1 (fun b hb => hp b hb a ha)

theorem entropy_normalize {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * entropy s (fun a => p a / ∑ b ∈ s, p b) := by
  let P := ∑ a ∈ s, p a
  by_cases hP : P = 0
  · have hz : ∀ a ∈ s, p a = 0 := by
      intro a ha
      have ha' := Finset.single_le_sum hp ha
      change p a ≤ P at ha'
      rw [hP] at ha'
      exact le_antisymm ha' (hp a ha)
    change entropy s p = Real.negMulLog P + P * _
    simp only [hP, Real.negMulLog_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero (fun a ha => by rw [hz a ha, Real.negMulLog_zero])
  · have heq : entropy s p = entropy s (fun a => P * (p a / P)) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      rw [mul_div_cancel₀ _ hP]
    rw [heq, entropy_scale]
    have hsum : (∑ a ∈ s, p a / P) = 1 := by rw [← Finset.sum_div]; exact div_self hP
    rw [hsum, one_mul]

theorem entropy_chain {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = observableEntropy s p f +
      ∑ b ∈ s.image f, mass s p f b *
        entropy (s.filter (fun a => f a = b)) (fun a => p a / mass s p f b) := by
  classical
  have hfiber : entropy s p =
      ∑ b ∈ s.image f, entropy (s.filter (fun a => f a = b)) p := by
    exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _).symm
  rw [hfiber]
  calc
    _ = ∑ b ∈ s.image f, (Real.negMulLog (mass s p f b) +
        mass s p f b * entropy (s.filter (fun a => f a = b))
          (fun a => p a / mass s p f b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact entropy_normalize _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = _ := by simp only [observableEntropy, entropy, Finset.sum_add_distrib]

theorem entropy_joint_le {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b)
    (hp1 : ∑ a ∈ s, ∑ b ∈ t, p a b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) ≤
      entropy s (fun a => ∑ b ∈ t, p a b) + entropy t (fun b => ∑ a ∈ s, p a b) := by
  let r := fun a => ∑ b ∈ t, p a b
  have hr : ∀ a ∈ s, 0 ≤ r a := fun a ha => Finset.sum_nonneg (hp a ha)
  have hterm : ∀ a ∈ s, ∀ b ∈ t, r a * (p a b / r a) = p a b := by
    intro a ha b hb
    by_cases h : r a = 0
    · have hl := Finset.single_le_sum (hp a ha) hb
      have hz : p a b = 0 := le_antisymm (h ▸ hl) (hp a ha b hb)
      simp [hz]
    · exact mul_div_cancel₀ _ h
  have hc := entropy_mixture t s r (fun a b => p a b / r a) hr hp1
    (fun a ha b hb => div_nonneg (hp a ha b hb) (hr a ha))
  have hmix : entropy t (fun b => ∑ a ∈ s, r a * (p a b / r a)) =
      entropy t (fun b => ∑ a ∈ s, p a b) := by
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    exact Finset.sum_congr rfl (fun a ha => hterm a ha b hb)
  rw [hmix] at hc
  calc
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
        ∑ a ∈ s, entropy t (p a) := by simp only [entropy, Finset.sum_product]
    _ = entropy s r + ∑ a ∈ s, r a * entropy t (fun b => p a b / r a) := by
      simp only [entropy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      exact entropy_normalize t (p a) (hp a ha)
    _ ≤ _ := add_le_add le_rfl hc

theorem sum_mass_mul {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (t : Finset β)
    (p : α → ℝ) (f : α → β) (q : β → ℝ) (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ b ∈ t, mass s p f b * q b = ∑ a ∈ s, p a * q (f a) := by
  classical
  simp only [mass, Finset.sum_mul]
  calc
    _ = ∑ b ∈ t, ∑ a ∈ s.filter (fun a => f a = b), p a * q (f a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hf _

theorem mass_eq_zero_of_not_mem {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) {b : β} (hb : b ∉ s.image f) : mass s p f b = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb (Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
    (Finset.mem_filter.mp ha).2⟩)).elim

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ) (c : γ) :
    mass (s.image f) (mass s p f) g c = mass s p (g ∘ f) c := by
  classical
  have h := sum_mass_mul s (s.image f) p f (fun b => if g b = c then 1 else 0)
    (fun a ha => Finset.mem_image_of_mem f ha)
  simpa only [mass, Finset.sum_filter, mul_ite, mul_one, mul_zero, Function.comp_apply] using h

theorem observableEntropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ) :
    observableEntropy s p (g ∘ f) = observableEntropy (s.image f) (mass s p f) g := by
  classical
  simp only [observableEntropy, entropy, Finset.image_image, mass_comp]

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem mass_pair_fst {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (b : β) :
    ∑ c ∈ s.image g, mass s p (fun a => (f a, g a)) (b, c) = mass s p f b := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hg : g a ∈ s.image g := Finset.mem_image_of_mem g ha
  by_cases hf : f a = b
  · simp [hf, hg]
  · simp [hf]

theorem mass_pair_snd {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) :
    ∑ b ∈ s.image f, mass s p (fun a => (f a, g a)) (b, c) = mass s p g c := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hf : f a ∈ s.image f := Finset.mem_image_of_mem f ha
  by_cases hg : g a = c
  · simp [hg, hf]
  · simp [hg]

theorem observableEntropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p (fun a => (f a, g a)) ≤
      observableEntropy s p f + observableEntropy s p g := by
  classical
  rw [observableEntropy_on_superset s (s.image f ×ˢ s.image g) p _
    (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem g ha⟩)]
  have h := entropy_joint_le (s.image f) (s.image g)
    (fun b c => mass s p (fun a => (f a, g a)) (b, c))
    (fun b _ c _ => mass_nonneg s p _ hp _) ?_
  · simpa only [mass_pair_fst, mass_pair_snd, observableEntropy] using h
  · simpa only [mass_pair_fst, mass_sum] using hp1

theorem observableEntropy_fst_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ observableEntropy s p (fun a => (f a, g a)) := by
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.fst hp

noncomputable def conditionalEntropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) : ℝ :=
  observableEntropy s p (fun a => (f a, g a)) - observableEntropy s p g

theorem conditionalEntropy_nonneg {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) : 0 ≤ conditionalEntropy s p f g := by
  apply sub_nonneg.mpr
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.snd hp

theorem conditionalEntropy_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f g ≤ observableEntropy s p f := by
  dsimp only [conditionalEntropy]
  linarith [observableEntropy_pair_le s p f g hp hp1]

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem observableEntropy_swap {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (fun a => (f a, g a)) =
      observableEntropy s p (fun a => (g a, f a)) := by
  exact (observableEntropy_equiv s p (fun a => (f a, g a)) (Equiv.prodComm β γ) hp).symm

theorem entropy_table_chain {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
      entropy s (fun a => ∑ b ∈ t, p a b) +
      ∑ a ∈ s, (∑ b ∈ t, p a b) * entropy t (fun b => p a b / ∑ c ∈ t, p a c) := by
  simp only [entropy, Finset.sum_product, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact entropy_normalize t (p a) (hp a ha)

theorem mass_filter_div {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) (b : β) (P : ℝ) :
    mass (s.filter (fun a => g a = c)) (fun a => p a / P) f b =
      mass s p (fun a => (g a, f a)) (c, b) / P := by
  classical
  simp only [mass, ← Finset.sum_div, Finset.filter_filter, Prod.mk.injEq]

theorem conditionalEntropy_eq_sum {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p f g = ∑ c ∈ s.image g, mass s p g c *
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
  classical
  have hrect := observableEntropy_on_superset s (s.image g ×ˢ s.image f) p
    (fun a => (g a, f a)) (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem g ha, Finset.mem_image_of_mem f ha⟩)
  rw [entropy_table_chain (s.image g) (s.image f)
    (fun c b => mass s p (fun a => (g a, f a)) (c, b))
    (fun c _ b _ => mass_nonneg s p _ hp _)] at hrect
  simp only [mass_pair_fst] at hrect
  have hinner : ∀ c ∈ s.image g,
      entropy (s.image f) (fun b => mass s p (fun a => (g a, f a)) (c, b) / mass s p g c) =
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    intro c _
    rw [observableEntropy_on_superset _ (s.image f) _ f]
    · apply Finset.sum_congr rfl
      intro b _
      rw [mass_filter_div]
    · intro a ha
      exact Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1
  have hh : observableEntropy s p (fun a => (g a, f a)) = observableEntropy s p g +
      ∑ c ∈ s.image g, mass s p g c *
        observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    rw [hrect]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [hinner c hc]
  rw [conditionalEntropy, observableEntropy_swap s p f g hp, hh, add_sub_cancel_left]

theorem conditionalEntropy_chain {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p (fun a => (f a, g a)) h =
      conditionalEntropy s p g h + conditionalEntropy s p f (fun a => (g a, h a)) := by
  have he := observableEntropy_equiv s p (fun a => ((f a, g a), h a))
    (Equiv.prodAssoc β γ δ) hp
  change observableEntropy s p (fun a => (f a, (g a, h a))) =
    observableEntropy s p (fun a => ((f a, g a), h a)) at he
  dsimp only [conditionalEntropy]
  linarith

theorem conditionalEntropy_reveal_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f h ≤ observableEntropy s p g +
      conditionalEntropy s p f (fun a => (g a, h a)) := by
  have hm := observableEntropy_comp_le s p (fun a => ((f a, g a), h a))
    (fun x => (x.1.1, x.2)) hp
  have hr := conditionalEntropy_chain s p f g h hp
  have hg := conditionalEntropy_le s p g h hp hp1
  dsimp only [conditionalEntropy] at *
  change observableEntropy s p (fun a => (f a, h a)) ≤ _ at hm
  linarith

theorem observableEntropy_const_of {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (b : β) (hf : ∀ a ∈ s, f a = b) :
    observableEntropy s p f = Real.negMulLog (∑ a ∈ s, p a) := by
  classical
  rw [observableEntropy_on_superset s {b} p f (fun a ha => Finset.mem_singleton.mpr (hf a ha))]
  simp only [entropy, Finset.sum_singleton, mass]
  rw [Finset.filter_eq_self.mpr hf]

theorem observableEntropy_le_log_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f ≤ Real.log t.card := by
  rw [observableEntropy_on_superset s t p f hf]
  apply entropy_le_log_card _ _ (fun b _ => mass_nonneg s p f hp b)
  have h := sum_mass_mul s t p f (fun _ => 1) hf
  simpa only [mul_one, hp1] using h

theorem conditionalEntropy_le_bad_mass {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by
  classical
  let K := Real.log (s.image f).card
  rw [conditionalEntropy_eq_sum s p f g hp]
  calc
    _ ≤ ∑ c ∈ s.image g, mass s p g c * (if bad c then K else 0) := by
      apply Finset.sum_le_sum
      intro c hc
      let P := mass s p g c
      have hP : 0 ≤ P := mass_nonneg s p g hp c
      by_cases hP0 : P = 0
      · change P * _ ≤ P * _
        simp only [hP0, zero_mul, le_refl]
      have hn : ∑ a ∈ s.filter (fun a => g a = c), p a / P = 1 := by
        rw [← Finset.sum_div]
        exact div_self hP0
      have hq : ∀ a ∈ s.filter (fun a => g a = c), 0 ≤ p a / P :=
        fun a ha => div_nonneg (hp a (Finset.mem_filter.mp ha).1) hP
      apply mul_le_mul_of_nonneg_left _ hP
      by_cases hbad : bad c
      · rw [ite_eq_left hbad]
        exact observableEntropy_le_log_on_superset _ (s.image f) _ f
          (fun a ha => Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1) hq hn
      · rw [ite_eq_right hbad]
        obtain ⟨a₀, ha₀, hga₀⟩ := Finset.mem_image.mp hc
        have hconst : ∀ a ∈ s.filter (fun a => g a = c), f a = f a₀ := by
          intro a ha
          obtain ⟨has, hga⟩ := Finset.mem_filter.mp ha
          exact hgood a has a₀ ha₀ (hga.trans hga₀.symm) (hga ▸ hbad)
        rw [observableEntropy_const_of _ _ _ (f a₀) hconst, hn, Real.negMulLog_one]
    _ = ∑ a ∈ s, p a * (if bad (g a) then K else 0) :=
      sum_mass_mul s (s.image g) p g _ (fun a ha => Finset.mem_image_of_mem g ha)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [K]

theorem observableEntropy_bool {α : Type uα} (s : Finset α) (p : α → ℝ)
    (f : α → Bool) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f = Real.binEntropy (mass s p f true) := by
  have hsum := sum_mass_mul s Finset.univ p f (fun _ => 1) (fun _ _ => Finset.mem_univ _)
  have hm : mass s p f false = 1 - mass s p f true := by
    simp only [mul_one, Fintype.sum_bool, hp1] at hsum
    linarith
  rw [observableEntropy_on_superset s Finset.univ p f (fun _ _ => Finset.mem_univ _)]
  simp only [entropy, Fintype.sum_bool, hm,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem conditionalEntropy_rare_flag {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (C : α → β) (Y : α → γ) (E : α → Bool)
    (B : γ → Prop) [DecidablePred B] (c₀ : β)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1)
    (hgood : ∀ a ∈ s, E a = false → ¬B (Y a) → C a = c₀) :
    conditionalEntropy s p C Y ≤ Real.binEntropy (mass s p E true) +
      (mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a) *
        Real.log (s.image C).card := by
  classical
  let bad : Bool × γ → Prop := fun ey => ey.1 = true ∨ B ey.2
  have hc := conditionalEntropy_le_bad_mass s p C (fun a => (E a, Y a)) bad hp ?_
  · have hn : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hp1
      norm_num at hp1
    have hK : 0 ≤ Real.log (s.image C).card := Real.log_nonneg (by
      exact_mod_cast Finset.card_pos.mpr (hn.image C))
    have hb : (∑ a ∈ s, if bad (E a, Y a) then p a else 0) ≤
        mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a := by
      simp only [mass, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a ha
      dsimp only [bad]
      split_ifs <;> first | linarith [hp a ha] | simp_all
    have hm := mul_le_mul_of_nonneg_right hb hK
    have hr := conditionalEntropy_reveal_le s p C E Y hp hp1
    rw [observableEntropy_bool s p E hp1] at hr
    linarith
  · intro a ha b hb he hbad
    have hEa : E a = false := by
      have : E a ≠ true := fun h => hbad (Or.inl h)
      cases h : E a <;> simp_all
    have hBa : ¬B (Y a) := fun h => hbad (Or.inr h)
    have hEb : E b = false := (congrArg Prod.fst he).symm.trans hEa
    have hBb : ¬B (Y b) := by
      simpa only [show Y b = Y a from (congrArg Prod.snd he).symm] using hBa
    rw [hgood a ha hEa hBa, hgood b hb hEb hBb]

theorem binEntropy_bits_le_three_sqrt {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ 3 * Real.sqrt q := by
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have h1 := Real.negMulLog_le_one_sub_self hs
  have h2 := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hq1)
  have hmul := mul_le_mul_of_nonneg_left h1 hs
  have hident := Real.negMulLog_mul (Real.sqrt q) (Real.sqrt q)
  rw [hs2] at hident
  have hbound : Real.binEntropy q ≤ 2 * Real.sqrt q := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  have hlog2 : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog2)]

theorem pair_flag_cost {q t b : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    (hqt : q ≤ t) (hqt2 : q ≤ t ^ 2) (hbt : b ≤ t) :
    Real.binEntropy q / Real.log 2 + 3 * k * (q + b) ≤ 9 * k * t := by
  have hs : Real.sqrt q ≤ t := (Real.sqrt_le_left ht).mpr hqt2
  have hent := binEntropy_bits_le_three_sqrt hq hq1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqb : q + b ≤ 2 * t := by linarith
  have hbmul := mul_le_mul_of_nonneg_left hqb (by positivity : 0 ≤ (3 : ℝ) * k)
  nlinarith [mul_nonneg (sub_nonneg.mpr hk') ht]

theorem event_union_bound {α : Type uα} {ι : Type uι} [Fintype ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, if ∃ i, E i a then p a else 0) ≤
      ∑ i, ∑ a ∈ s, if E i a then p a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : ∃ i, E i a
  · rw [ite_eq_left he]
    obtain ⟨i, hi⟩ := he
    apply le_trans _ (Finset.single_le_sum (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl) (Finset.mem_univ i))
    simp only [ite_eq_left hi, le_refl]
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl)

theorem two_exceptions_bound {α : Type uα} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hind : ∀ i j, i ≠ j →
      (∑ a ∈ s, if E i a ∧ E j a then p a else 0) =
        (∑ a ∈ s, if E i a then p a else 0) *
        (∑ a ∈ s, if E j a then p a else 0)) :
    let t := ∑ i, ∑ a ∈ s, if E i a then p a else 0
    let q := ∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0
    q ≤ t ^ 2 ∧ q ≤ t := by
  classical
  dsimp only
  have hPi : ∀ i, 0 ≤ ∑ a ∈ s, if E i a then p a else 0 := by
    intro i
    apply Finset.sum_nonneg
    intro a ha
    split_ifs <;> first | exact hp a ha | exact le_rfl
  constructor
  · have hU := event_union_bound s p
      (fun ij : ι × ι => fun a => ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a) hp
    have he : (∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0) =
        ∑ a ∈ s, if ∃ ij : ι × ι, ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a then p a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact propext ⟨fun ⟨i,j,h⟩ => ⟨(i,j),h⟩, fun ⟨⟨i,j⟩,h⟩ => ⟨i,j,h⟩⟩
    rw [he]
    apply le_trans hU
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero]
      exact mul_nonneg (hPi i) (hPi i)
    · simpa only [ne_eq, hij, not_false_eq_true, true_and] using (hind i j hij).le
  · apply le_trans _ (event_union_bound s p E hp)
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : ∃ i j, i ≠ j ∧ E i a ∧ E j a
    · obtain ⟨i,j,hij,hi,hj⟩ := h
      rw [ite_eq_left ⟨i,j,hij,hi,hj⟩, ite_eq_left (show ∃ i, E i a from ⟨i,hi⟩)]
    · rw [ite_eq_right h]
      split_ifs <;> first | exact hp a ha | exact le_rfl

theorem no_large_coordinate {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hE : ¬∃ i j, i ≠ j ∧ a / (4 * Fintype.card ι) ≤ |x i| ∧
      a / (4 * Fintype.card ι) ≤ |x j|)
    (hB : |∑ i, x i| < a / 2) (i : ι) : |x i| < a := by
  by_contra hn
  have hi : a ≤ |x i| := le_of_not_gt hn
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hka : a / (4 * Fintype.card ι) ≤ a := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Fintype.card ι)).mpr
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    nlinarith
  have hsmall : ∀ j ∈ Finset.univ.erase i, |x j| < a / (4 * Fintype.card ι) := by
    intro j hj
    by_contra hn
    exact hE ⟨i,j,Ne.symm (Finset.mem_erase.mp hj).1,hka.trans hi,le_of_not_gt hn⟩
  have habs : |∑ j ∈ Finset.univ.erase i, x j| ≤ a / 4 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ j ∈ Finset.univ.erase i, |x j|) ≤
          ∑ _j ∈ Finset.univ.erase i, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum (fun j hj => (hsmall j hj).le)
      _ ≤ ∑ _j : ι, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = a / 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hiabs : |x i| ≤ |∑ j, x j| + |∑ j ∈ Finset.univ.erase i, x j| := by
    have he := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    have hx : x i = (∑ j, x j) - ∑ j ∈ Finset.univ.erase i, x j := by linarith
    rw [hx]
    exact abs_sub _ _
  linarith

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

theorem observableEntropy_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) :
    observableEntropy s p f = observableEntropy t p f := by
  classical
  rw [observableEntropy_on_superset s (t.image f) p f
    (fun x hx => Finset.mem_image_of_mem f (hst hx))]
  apply Finset.sum_congr rfl
  intro b _
  rw [mass_subset p f hst hp b]

theorem observableEntropy_congr {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (f g : α → β)
    (hp : ∀ x ∈ s, p x = q x) (hf : ∀ x ∈ s, f x = g x) :
    observableEntropy s p f = observableEntropy s q g := by
  classical
  have hi : s.image f = s.image g := Finset.image_congr hf
  have hm : ∀ b, mass s p f b = mass s q g b := by
    intro b
    simp only [mass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x hx, hf x hx]
  simp only [observableEntropy, hi]
  rw [show mass s p f = mass s q g from funext hm]

theorem observableEntropy_le_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    observableEntropy s p f ≤ observableEntropy s p g := by
  classical
  let h : γ → β := fun c => if hc : ∃ x ∈ s, g x = c then f hc.choose else Classical.choice inferInstance
  have hf : ∀ x ∈ s, (h ∘ g) x = f x := by
    intro x hx
    dsimp only [Function.comp_apply,h]
    rw [dite_eq_left ⟨x,hx,rfl⟩]
    exact hfg _ (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).1
      x hx (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).2
  rw [← observableEntropy_congr s p p (h ∘ g) f (fun _ _ => rfl) hf]
  exact observableEntropy_comp_le s p g h hp

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

theorem conditionalEntropy_disintegrate {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) =
      ∑ c ∈ s.image g, mass s p g c * conditionalEntropy
        (s.filter (fun x => g x = c)) (fun x => p x / mass s p g c) f h := by
  have hc := conditionalEntropy_chain s p f h g hp
  rw [conditionalEntropy_eq_sum s p (fun x => (f x,h x)) g hp,
      conditionalEntropy_eq_sum s p h g hp] at hc
  simp only [conditionalEntropy, mul_sub, Finset.sum_sub_distrib]
  dsimp only [conditionalEntropy] at hc
  linarith

theorem observableEntropy_eq_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    observableEntropy s p f = observableEntropy s p g :=
  le_antisymm (observableEntropy_le_of_fibers s p f g hp
    (fun x hx y hy => (hfg x hx y hy).mpr))
    (observableEntropy_le_of_fibers s p g f hp
    (fun x hx y hy => (hfg x hx y hy).mp))

theorem observableEntropy_of_injective {α : Type uα} {β : Type uβ} [DecidableEq β] [Nonempty β]
    [Nonempty α] (s : Finset α) (p : α → ℝ) (f : α → β)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hf : Function.Injective f) :
    observableEntropy s p f = entropy s p := by
  classical
  rw [← observableEntropy_id s p]
  exact observableEntropy_eq_of_fibers s p f id hp (fun _ _ _ _ => hf.eq_iff)

theorem conditionalEntropy_eq_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    [Nonempty β] [Nonempty γ] [Nonempty δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    conditionalEntropy s p f h = conditionalEntropy s p g h := by
  unfold conditionalEntropy
  congr 1
  apply observableEntropy_eq_of_fibers _ _ _ _ hp
  intro x hx y hy
  simp only [Prod.mk.injEq, hfg x hx y hy]

theorem conditionalEntropy_condition_swap {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    [Nonempty β] [Nonempty γ] [Nonempty δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (g x,h x)) =
      conditionalEntropy s p f (fun x => (h x,g x)) := by
  unfold conditionalEntropy
  rw [observableEntropy_swap s p g h hp]
  congr 1
  apply observableEntropy_eq_of_fibers _ _ _ _ hp
  intro x _ y _
  simp only [Prod.mk.injEq, and_comm (a := g x = g y)]

theorem conditionalEntropy_condition_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) ≤ conditionalEntropy s p f g := by
  classical
  rw [conditionalEntropy_disintegrate s p f g h hp, conditionalEntropy_eq_sum s p f g hp]
  apply Finset.sum_le_sum
  intro c _
  have hP := mass_nonneg s p g hp c
  by_cases hc : mass s p g c = 0
  · simp only [hc, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ hP
  apply conditionalEntropy_le
  · intro a ha
    exact div_nonneg (hp a (Finset.mem_filter.mp ha).1) hP
  · rw [← Finset.sum_div]
    exact div_self hc

theorem observableEntropy_mixture_marginal {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) =
      observableEntropy s (fun a => ∑ i ∈ t, w i*p i a) f := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (s.image f) _ _ (by
    intro x hx; exact Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2)]
  unfold observableEntropy entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  simp only [mass, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a = b <;> simp [hf]

theorem observableEntropy_mixture_joint {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β)
    (hp : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      entropy t w + ∑ i ∈ t, w i*observableEntropy s (p i) f := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (t ×ˢ s.image f) _ _ (by
    intro x hx
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hx).1,
      Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2⟩)]
  have hm : ∀ i ∈ t, ∀ b : β,
      mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) (i,b) =
        w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq]
    simp_rw [ite_and]
    rw [Finset.sum_eq_single i]
    · simp [Finset.mul_sum, mul_ite]
    · intro j _ hji
      simp [hji]
    · exact fun h => (h hi).elim
  calc
    _ = ∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b) := by
      simp only [entropy, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (hm i hi b))
    _ = _ := by
      change (∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b)) =
        (∑ i ∈ t, Real.negMulLog (w i)) + ∑ i ∈ t, w i*observableEntropy s (p i) f
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [entropy_scale, mass_sum, hp i hi, one_mul]
      rfl

theorem conditionalEntropy_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  let q : ι × α → ℝ := fun ia => w ia.1*p ia.1 ia.2
  have hq : ∀ x ∈ t ×ˢ s, 0 ≤ q x := by
    intro x hx
    exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
      (hp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
  have hh := conditionalEntropy_condition_le (t ×ˢ s) q
    (fun ia => f ia.2) (fun ia => g ia.2) Prod.fst hq
  have he : observableEntropy (t ×ˢ s) q (fun x => (f x.2,(x.1,g x.2))) =
      observableEntropy (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) := by
    let e : ι × (β × γ) ≃ β × (ι × γ) :=
      { toFun := fun x => (x.2.1,(x.1,x.2.2))
        invFun := fun x => (x.2.1,(x.1,x.2.2))
        left_inv := by rintro ⟨i,b,c⟩; rfl
        right_inv := by rintro ⟨b,i,c⟩; rfl }
    exact observableEntropy_equiv (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) e hq
  dsimp only [conditionalEntropy] at hh ⊢
  rw [he, observableEntropy_mixture_joint t s w p (fun a => (f a,g a)) hp1,
    observableEntropy_mixture_joint t s w p g hp1,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub] using hh

theorem observableEntropy_mixture_joint_general {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (t ×ˢ s.image f) _ _ (by
    intro x hx
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hx).1,
      Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2⟩)]
  have hm : ∀ i ∈ t, ∀ b : β,
      mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) (i,b) =
        w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq]
    simp_rw [ite_and]
    rw [Finset.sum_eq_single i]
    · simp [Finset.mul_sum, mul_ite]
    · intro j _ hji
      simp [hji]
    · exact fun h => (h hi).elim
  calc
    _ = ∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b) := by
      simp only [entropy, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (hm i hi b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [entropy_scale, mass_sum]
      rfl

theorem conditionalEntropy_mixture_general {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  let q : ι × α → ℝ := fun ia => w ia.1*p ia.1 ia.2
  have hq : ∀ x ∈ t ×ˢ s, 0 ≤ q x := by
    intro x hx
    exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
      (hp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
  have hh := conditionalEntropy_condition_le (t ×ˢ s) q
    (fun ia => f ia.2) (fun ia => g ia.2) Prod.fst hq
  have he : observableEntropy (t ×ˢ s) q (fun x => (f x.2,(x.1,g x.2))) =
      observableEntropy (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) := by
    let e : ι × (β × γ) ≃ β × (ι × γ) :=
      { toFun := fun x => (x.2.1,(x.1,x.2.2))
        invFun := fun x => (x.2.1,(x.1,x.2.2))
        left_inv := by rintro ⟨i,b,c⟩; rfl
        right_inv := by rintro ⟨b,i,c⟩; rfl }
    exact observableEntropy_equiv (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) e hq
  dsimp only [conditionalEntropy] at hh ⊢
  rw [he, observableEntropy_mixture_joint_general t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_joint_general t s w p g,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, add_sub_add_left_eq_sub] using hh

theorem conditionalEntropy_mono {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hpq : ∀ a ∈ s, p a ≤ q a) :
    conditionalEntropy s p f g ≤ conditionalEntropy s q f g := by
  let P : Bool → α → ℝ := fun b => if b then p else fun a => q a-p a
  have hh := conditionalEntropy_mixture_general Finset.univ s (fun _ : Bool => (1 : ℝ))
    P f g (by intros; exact zero_le_one) (by
      intro b _ a ha
      cases b
      · exact sub_nonneg.mpr (hpq a ha)
      · exact hp a ha)
  have he : (fun a => ∑ b : Bool, (1 : ℝ)*P b a)=q := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul] at hh
  have hn := conditionalEntropy_nonneg s (fun a => q a-p a) f g
    (fun a ha => sub_nonneg.mpr (hpq a ha))
  linarith

theorem mixture_information_common {ι : Type uι} {α : Type uα} [DecidableEq ι] [DecidableEq α]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (r : α → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i=1)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a=1)
    (hr : ∀ a ∈ s, 0 ≤ r a) (hrp : ∀ i ∈ t, ∀ a ∈ s, r a ≤ p i a) :
    entropy s (fun a => ∑ i ∈ t, w i*p i a) - (∑ i ∈ t, w i*entropy s (p i)) ≤
      (1-∑ a ∈ s, r a)*entropy t w := by
  have hh := conditionalEntropy_mono (t ×ˢ s)
    (fun ia => w ia.1*r ia.2) (fun ia => w ia.1*p ia.1 ia.2) Prod.fst Prod.snd
    (by
      intro x hx
      exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
        (hr x.2 (Finset.mem_product.mp hx).2))
    (by
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (hrp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
        (hw x.1 (Finset.mem_product.mp hx).1))
  dsimp only [conditionalEntropy] at hh
  have hjr := observableEntropy_mixture_joint_general t s w (fun _ => r) id
  have hjp := observableEntropy_mixture_joint t s w p id hp1
  have hmr := observableEntropy_mixture_marginal t s w (fun _ => r) id
  have hmp := observableEntropy_mixture_marginal t s w p id
  simp only [id_eq] at hjr hjp hmr hmp
  rw [hjr, hjp, hmr, hmp] at hh
  simp_rw [observableEntropy_id, ← Finset.sum_mul, hw1, one_mul] at hh
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul] at hh
  change (∑ a ∈ s, r a)*entropy t w+entropy s r-entropy s r ≤
    entropy t w+(∑ i ∈ t, w i*entropy s (p i))-
      entropy s (fun a => ∑ i ∈ t, w i*p i a) at hh
  nlinarith

theorem conditionalEntropy_id {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (g : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p id g = entropy s p-observableEntropy s p g := by
  have hh := observableEntropy_comp_le s p (fun a => (a,g a)) Prod.fst hp
  change observableEntropy s p id ≤ _ at hh
  rw [observableEntropy_id] at hh
  have he := le_antisymm (observableEntropy_le s p (fun a => (a,g a)) hp) hh
  exact congrArg (fun x => x-observableEntropy s p g) he

noncomputable def js {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  entropy s (fun a => (p a+q a)/2)-(entropy s p+entropy s q)/2

theorem conditionalEntropy_midpoint {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → β) (g : α → γ) :
    (conditionalEntropy s p f g+conditionalEntropy s q f g)/2 ≤
      conditionalEntropy s (fun a => (p a+q a)/2) f g := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := conditionalEntropy_mixture Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P f g (by intros; positivity) (by intro b _; cases b <;> assumption)
      (by intro b _; cases b <;> assumption)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a) = fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  linarith

theorem js_observable_le {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (g : α → β) :
    observableEntropy s (fun a => (p a+q a)/2) g-
      (observableEntropy s p g+observableEntropy s q g)/2 ≤ js s p q := by
  have hh := conditionalEntropy_midpoint s p q hp hq hp1 hq1 id g
  rw [conditionalEntropy_id s p g hp, conditionalEntropy_id s q g hq,
    conditionalEntropy_id s _ g (fun a ha => div_nonneg (add_nonneg (hp a ha) (hq a ha)) (by norm_num))] at hh
  unfold js
  linarith

theorem js_nonneg {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) : 0 ≤ js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 (fun _ => ())
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_const_of s p (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s q (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s _ (fun _ => ()) () (by intros; rfl), hp1, hq1, hm1] at hh
  simpa only [Real.negMulLog_one, add_zero, zero_div, sub_zero] using hh

theorem event_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → Bool) :
    (mass s p f true-mass s q f true)^2 ≤ 2*js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 f
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_bool s p f hp1, observableEntropy_bool s q f hq1,
    observableEntropy_bool s _ f hm1] at hh
  have hm : mass s (fun a => (p a+q a)/2) f true =
      (mass s p f true+mass s q f true)/2 := by
    simp only [mass, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hm] at hh
  have hple : mass s p f true ≤ 1 := by
    rw [mass, ← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hp a ha)
  have hqle : mass s q f true ≤ 1 := by
    rw [mass, ← hq1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hq a ha)
  have hg := binaryEntropy_midpoint_gap (mass s p f true) (mass s q f true)
    ⟨mass_nonneg s p f hp true,hple⟩ ⟨mass_nonneg s q f hq true,hqle⟩
  linarith

noncomputable def totalVariation {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  (∑ a ∈ s, |p a-q a|)/2

theorem totalVariation_nonneg {α : Type uα} (s : Finset α) (p q : α → ℝ) :
    0 ≤ totalVariation s p q := div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem totalVariation_eq_event {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    totalVariation s p q = mass s p (fun a => decide (q a ≤ p a)) true-
      mass s q (fun a => decide (q a ≤ p a)) true := by
  classical
  have he (a : α) : |p a-q a|=2*(if q a ≤ p a then p a-q a else 0)-(p a-q a) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]; ring
  simp_rw [totalVariation, he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp1, hq1]
  simp only [sub_self, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mass, Finset.sum_filter, decide_eq_true_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem totalVariation_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    (totalVariation s p q)^2 ≤ 2*js s p q := by
  rw [totalVariation_eq_event s p q hp1 hq1]
  exact event_sq_le_two_js s p q hp hq hp1 hq1 _

theorem sum_min_eq_one_sub_tv {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    (∑ a ∈ s, min (p a) (q a))=1-totalVariation s p q := by
  have he (a : α) : min (p a) (q a)=(p a+q a-|p a-q a|)/2 := by
    rcases le_total (p a) (q a) with h|h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]
  unfold totalVariation
  ring

theorem js_le_tv {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    js s p q ≤ totalVariation s p q*Real.log 2 := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := mixture_information_common Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P (fun a => min (p a) (q a)) (by intros; positivity)
    (by norm_num [Fintype.sum_bool]) (by intro b _; cases b <;> assumption)
    (fun a ha => le_min (hp a ha) (hq a ha)) (by
      intro b _ a _
      cases b
      · exact min_le_right _ _
      · exact min_le_left _ _)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a)=fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he, sum_min_eq_one_sub_tv s p q hp1 hq1] at hh
  have hb : entropy Finset.univ (fun _ : Bool => (1/2 : ℝ))=Real.log 2 := by
    simp only [entropy, Fintype.sum_bool]
    change -(1/2 : ℝ)*Real.log (1/2)+(-(1/2 : ℝ)*Real.log (1/2))=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hb] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  unfold js
  linarith

theorem totalVariation_triangle {α : Type uα} (s : Finset α) (p q r : α → ℝ) :
    totalVariation s p r ≤ totalVariation s p q+totalVariation s q r := by
  unfold totalVariation
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => abs_sub_le _ _ _)) (by norm_num)

end FiniteEntropy
end EntropyRateDimension
end

end OAI
