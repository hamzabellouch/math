import Mathlib

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section

variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def bitMass (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r

def thinningMass (rate : V → ℝ) (b : V → Bool) : ℝ :=
  ∏ v, bitMass (rate v) (b v)

lemma sum_bitMass (r : ℝ) : (∑ b : Bool, bitMass r b) = 1 := by
  simp [bitMass]

lemma sum_thinningMass (rate : V → ℝ) :
    (∑ b : V → Bool, thinningMass rate b) = 1 := by
  unfold thinningMass
  rw [← Fintype.prod_sum]
  simp only [sum_bitMass, Finset.prod_const_one]

lemma thinningMass_nonneg (rate : V → ℝ) (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1)
    (b : V → Bool) : 0 ≤ thinningMass rate b := by
  apply Finset.prod_nonneg
  intro v _
  unfold bitMass
  split <;> linarith [(hrate v).1, (hrate v).2]

lemma thinning_false_mass (rate : V → ℝ) (u : V) :
    (∑ b : V → Bool, if b u = false then thinningMass rate b else 0) = 1 - rate u := by
  have hprod (b : V → Bool) :
      (if b u = false then thinningMass rate b else 0) =
        ∏ v, bitMass (rate v) (b v) *
          (if v = u then (if b v = false then 1 else 0) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    by_cases h : b u = false <;> simp [h, thinningMass]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun v (b : Bool) => bitMass (rate v) b *
    (if v = u then (if b = false then 1 else 0) else 1))]
  have hsum (v : V) :
      (∑ b : Bool, bitMass (rate v) b *
        (if v = u then (if b = false then 1 else 0) else 1)) =
      if v = u then 1 - rate v else 1 := by
    by_cases h : v = u <;> simp [h, bitMass]
  simp_rw [hsum]
  simp

def thinningRate (α r : ℝ) : ℝ := (α - r) / (1 - r)

lemma thinningRate_bounds {α r : ℝ} (hr : 0 ≤ r) (hra : r ≤ α) (ha : α < 1) :
    0 ≤ thinningRate α r ∧ thinningRate α r ≤ α := by
  have hden : 0 < 1 - r := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hra) hden.le
  · rw [thinningRate, div_le_iff₀ hden]
    have hprod : 0 ≤ r * (1 - α) := mul_nonneg hr (by linarith)
    nlinarith

lemma equal_survival {α r : ℝ} (hr : r < 1) :
    (1 - r) * (1 - thinningRate α r) = 1 - α := by
  unfold thinningRate
  have hden : 1 - r ≠ 0 := by linarith
  field_simp
  ring

def eventMass (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then p ω else 0

def jointMass (p : Ω → ℝ) (rate : V → ℝ) (ω : Ω) (b : V → Bool) : ℝ :=
  p ω * thinningMass rate b

omit [Fintype Ω] in
lemma jointMass_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (rate : V → ℝ) (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1)
    (ω : Ω) (b : V → Bool) : 0 ≤ jointMass p rate ω b :=
  mul_nonneg (hp ω) (thinningMass_nonneg rate hrate b)

lemma sum_jointMass (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) (rate : V → ℝ) :
    (∑ ω, ∑ b, jointMass p rate ω b) = 1 := by
  simp only [jointMass, ← Finset.mul_sum, sum_thinningMass, mul_one, hp]

lemma surviving_event_mass (p : Ω → ℝ) (rate : V → ℝ)
    (E : Ω → Prop) (u : V) :
    (∑ ω, ∑ b : V → Bool,
      if E ω ∧ b u = false then jointMass p rate ω b else 0) =
      eventMass p E * (1 - rate u) := by
  have hinner (ω : Ω) :
      (∑ b : V → Bool, if E ω ∧ b u = false then jointMass p rate ω b else 0) =
      (if E ω then p ω else 0) * (1 - rate u) := by
    by_cases h : E ω
    · simp only [h, true_and, jointMass, ite_true]
      calc
        _ = ∑ b : V → Bool, p ω * (if b u = false then thinningMass rate b else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : b u = false <;> simp [hb]
        _ = p ω * ∑ b : V → Bool, (if b u = false then thinningMass rate b else 0) :=
          (Finset.mul_sum ..).symm
        _ = _ := by rw [thinning_false_mass]
    · simp [h]
  simp_rw [hinner]
  exact (Finset.sum_mul ..).symm

lemma eventMass_compl (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) (E : Ω → Prop) :
    eventMass p (fun ω => ¬ E ω) = 1 - eventMass p E := by
  have h (ω : Ω) : (if ¬ E ω then p ω else 0) = p ω - (if E ω then p ω else 0) := by
    by_cases h : E ω <;> simp [h]
  unfold eventMass
  calc
    _ = ∑ ω, (p ω - (if E ω then p ω else 0)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : E ω <;> simp [he]
    _ = _ := by rw [Finset.sum_sub_distrib, hp]

lemma pre_removal_survival (p : Ω → ℝ) (hp : ∑ ω, p ω = 1)
    (conflict : Ω → V → Prop) (α : ℝ)
    (hr : ∀ u, eventMass p (fun ω => conflict ω u) < 1) (u : V) :
    (∑ ω, ∑ b : V → Bool,
      if ¬ conflict ω u ∧ b u = false then
        jointMass p (fun v => thinningRate α (eventMass p (fun w => conflict w v))) ω b
      else 0) = 1 - α := by
  have hs := surviving_event_mass p
    (fun v => thinningRate α (eventMass p (fun w => conflict w v)))
    (fun ω => ¬ conflict ω u) u
  have he : eventMass p (fun ω => ¬ conflict ω u) *
      (1 - thinningRate α (eventMass p (fun w => conflict w u))) = 1 - α := by
    rw [eventMass_compl p hp]
    exact equal_survival (hr u)
  rw [he] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : ¬ conflict ω u ∧ b u = false <;> simp [h]

lemma eventMass_survives_removal (p : Ω → ℝ) (hp : ∑ ω, p ω = 1)
    (C R : Ω → Prop) (hdisj : ∀ ω, R ω → ¬ C ω) :
    eventMass p (fun ω => ¬ C ω ∧ ¬ R ω) = 1 - eventMass p C - eventMass p R := by
  have h (ω : Ω) : (if ¬ C ω ∧ ¬ R ω then p ω else 0) =
      p ω - (if C ω then p ω else 0) - (if R ω then p ω else 0) := by
    by_cases hc : C ω <;> by_cases hr : R ω
    · exact (hdisj ω hr hc).elim
    all_goals simp [hc, hr]
  unfold eventMass
  calc
    _ = ∑ ω, (p ω - (if C ω then p ω else 0) - (if R ω then p ω else 0)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hc : C ω <;> by_cases hr : R ω
      · exact (hdisj ω hr hc).elim
      all_goals simp [hc, hr]
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp]

lemma post_removal_survival_le (p : Ω → ℝ) (hp : ∑ ω, p ω = 1)
    (conflict removed : Ω → V → Prop) (hdisj : ∀ ω u, removed ω u → ¬ conflict ω u)
    (α s : ℝ) (hs : 0 ≤ s) (ha : α < 1)
    (hr0 : ∀ u, 0 ≤ eventMass p (fun ω => conflict ω u))
    (hra : ∀ u, eventMass p (fun ω => conflict ω u) ≤ α)
    (hslot : ∀ u, eventMass p (fun ω => removed ω u) = s) (u : V) :
    (∑ ω, ∑ b : V → Bool,
      if (¬ conflict ω u ∧ ¬ removed ω u) ∧ b u = false then
        jointMass p (fun v => thinningRate α (eventMass p (fun w => conflict w v))) ω b
      else 0) ≤ (1 - α) * (1 - s) := by
  have hsurv := surviving_event_mass p
    (fun v => thinningRate α (eventMass p (fun w => conflict w v)))
    (fun ω => ¬ conflict ω u ∧ ¬ removed ω u) u
  have he : (∑ ω, ∑ b : V → Bool,
      if (¬ conflict ω u ∧ ¬ removed ω u) ∧ b u = false then
        jointMass p (fun v => thinningRate α (eventMass p (fun w => conflict w v))) ω b
      else 0) =
      (1 - eventMass p (fun ω => conflict ω u) - s) *
        (1 - thinningRate α (eventMass p (fun ω => conflict ω u))) := by
    rw [eventMass_survives_removal p hp _ _ (fun ω => hdisj ω u), hslot] at hsurv
    convert hsurv using 1
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : (¬ conflict ω u ∧ ¬ removed ω u) ∧ b u = false <;> simp [h]
  rw [he]
  have hrate := (thinningRate_bounds (hr0 u) (hra u) ha).2
  have heq := equal_survival (α := α) (lt_of_le_of_lt (hra u) ha)
  have hmul : 0 ≤ s * (α - thinningRate α (eventMass p (fun ω => conflict ω u))) :=
    mul_nonneg hs (sub_nonneg.mpr hrate)
  nlinarith

section UniformSlots

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

def slotDrawMass (x : Σ i, A i) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * (Fintype.card (A x.1) : ℝ)⁻¹

lemma slotDrawMass_nonneg (x : Σ i, A i) : 0 ≤ slotDrawMass A x := by
  unfold slotDrawMass
  positivity

lemma slotDrawMass_fiber [∀ i, Nonempty (A i)] (i : I) :
    (∑ a : A i, slotDrawMass A ⟨i, a⟩) = (Fintype.card I : ℝ)⁻¹ := by
  have hc : (Fintype.card (A i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ _a : A i, (Fintype.card I : ℝ)⁻¹ * (Fintype.card (A i) : ℝ)⁻¹) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma sum_slotDrawMass [Nonempty I] [∀ i, Nonempty (A i)] :
    (∑ x : Σ i, A i, slotDrawMass A x) = 1 := by
  rw [Fintype.sum_sigma]
  simp only [slotDrawMass_fiber, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_inv_cancel₀ hc

lemma slotDrawMass_slot [∀ i, Nonempty (A i)] (i : I) :
    eventMass (slotDrawMass A) (fun x => x.1 = i) = (Fintype.card I : ℝ)⁻¹ := by
  unfold eventMass
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ j : I, if j = i then (Fintype.card I : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j
        simpa using slotDrawMass_fiber A i
      · simp [h]
    _ = _ := by simp

lemma uniform_slot_survival_le [Nonempty I] [∀ i, Nonempty (A i)]
    (conflict : (Σ i, A i) → (Σ i, A i) → Prop)
    (hinternal : ∀ x u, x.1 = u.1 → ¬ conflict x u)
    (α : ℝ) (ha : α < 1)
    (hcheck : ∀ u, eventMass (slotDrawMass A) (fun x => conflict x u) ≤ α)
    (u : Σ i, A i) :
    (∑ x, ∑ b : (Σ i, A i) → Bool,
      if (¬ conflict x u ∧ x.1 ≠ u.1) ∧ b u = false then
        jointMass (slotDrawMass A)
          (fun v => thinningRate α (eventMass (slotDrawMass A) (fun w => conflict w v))) x b
      else 0) ≤ (1 - α) * (1 - (Fintype.card I : ℝ)⁻¹) := by
  have hr0 (u : Σ i, A i) : 0 ≤ eventMass (slotDrawMass A) (fun x => conflict x u) := by
    apply Finset.sum_nonneg
    intro x _
    split
    · exact slotDrawMass_nonneg A x
    · exact le_rfl
  have h := post_removal_survival_le (slotDrawMass A) (sum_slotDrawMass A)
    conflict (fun x u => x.1 = u.1) hinternal α (Fintype.card I : ℝ)⁻¹
    (by positivity) ha hr0 hcheck (fun u => slotDrawMass_slot A u.1) u
  convert h using 1
  apply Finset.sum_congr (by ext; simp)
  intro x _
  apply Finset.sum_congr (by ext; simp)
  intro b _
  by_cases he : (¬ conflict x u ∧ x.1 ≠ u.1) ∧ b u = false <;> simp [he]

end UniformSlots

lemma expected_count_eq_sum (p : Ω → ℝ) (rate : V → ℝ)
    (S : Finset V) (E : Ω → (V → Bool) → V → Prop) :
    (∑ ω, ∑ b : V → Bool,
      jointMass p rate ω b * ((S.filter (E ω b)).card : ℝ)) =
    ∑ u ∈ S, ∑ ω, ∑ b : V → Bool,
      if E ω b u then jointMass p rate ω b else 0 := by
  calc
    _ = ∑ ω, ∑ b : V → Bool, ∑ u ∈ S,
        if E ω b u then jointMass p rate ω b else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_boole (E ω b) S, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : E ω b u <;> simp [h]
    _ = ∑ ω, ∑ u ∈ S, ∑ b : V → Bool,
        if E ω b u then jointMass p rate ω b else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma sum_pre_removal_survival (p : Ω → ℝ) (hp : ∑ ω, p ω = 1)
    (conflict : Ω → V → Prop) (α : ℝ)
    (hr : ∀ u, eventMass p (fun ω => conflict ω u) < 1) (S : Finset V) :
    (∑ u ∈ S, ∑ ω, ∑ b : V → Bool,
      if ¬ conflict ω u ∧ b u = false then
        jointMass p (fun v => thinningRate α (eventMass p (fun w => conflict w v))) ω b
      else 0) = (1 - α) * S.card := by
  calc
    _ = ∑ _u ∈ S, (1 - α) := by
      apply Finset.sum_congr rfl
      intro u _
      exact pre_removal_survival p hp conflict α hr u
    _ = _ := by simp [mul_comm]; ring

lemma sum_post_removal_survival_le (p : Ω → ℝ) (hp : ∑ ω, p ω = 1)
    (conflict removed : Ω → V → Prop) (hdisj : ∀ ω u, removed ω u → ¬ conflict ω u)
    (α s : ℝ) (hs : 0 ≤ s) (ha : α < 1)
    (hr0 : ∀ u, 0 ≤ eventMass p (fun ω => conflict ω u))
    (hra : ∀ u, eventMass p (fun ω => conflict ω u) ≤ α)
    (hslot : ∀ u, eventMass p (fun ω => removed ω u) = s) (S : Finset V) :
    (∑ u ∈ S, ∑ ω, ∑ b : V → Bool,
      if (¬ conflict ω u ∧ ¬ removed ω u) ∧ b u = false then
        jointMass p (fun v => thinningRate α (eventMass p (fun w => conflict w v))) ω b
      else 0) ≤ (1 - α) * (1 - s) * S.card := by
  calc
    _ ≤ ∑ _u ∈ S, ((1 - α) * (1 - s)) := by
      apply Finset.sum_le_sum
      intro u _
      exact post_removal_survival_le p hp conflict removed hdisj α s hs ha hr0 hra hslot u
    _ = _ := by simp [mul_comm]

end
end Balanced.SelectionThinning

end OAI
