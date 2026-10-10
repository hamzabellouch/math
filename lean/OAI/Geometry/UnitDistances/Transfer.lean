import OAI.Geometry.UnitDistances.Cross

namespace OAI

namespace PlanarUnitDistances.RestrictedTransfer
open Finset

noncomputable def mass {X : Type*} (ν : X → ℝ) (s : Finset X) : ℝ := ∑ x ∈ s, ν x

section Mass
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {ν : X → ℝ}
omit [Fintype X] [DecidableEq X] in
lemma mass_nonneg (hν : ∀ x, 0 ≤ ν x) (s : Finset X) : 0 ≤ mass ν s :=
  sum_nonneg (fun x _ => hν x)
omit [Fintype X] [DecidableEq X] in
lemma mass_mono (hν : ∀ x, 0 ≤ ν x) {s t : Finset X} (h : s ⊆ t) :
    mass ν s ≤ mass ν t := sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hν x)
lemma mass_compl (hν : ∑ x, ν x = 1) (s : Finset X) : mass ν sᶜ = 1 - mass ν s := by
  have h := sum_compl_add_sum s ν
  dsimp [mass]
  linarith
omit [Fintype X] in
lemma mass_union_le (hν : ∀ x, 0 ≤ ν x) (s t : Finset X) :
    mass ν (s ∪ t) ≤ mass ν s + mass ν t := by
  have he := sum_union_inter (s₁ := s) (s₂ := t) (f := ν)
  have hi : 0 ≤ ∑ x ∈ s ∩ t, ν x := sum_nonneg (fun x _ => hν x)
  dsimp [mass]
  linarith
omit [Fintype X] [DecidableEq X] in
lemma atom_le_mass (hν : ∀ x, 0 ≤ ν x) {s : Finset X} {x : X} (hx : x ∈ s) :
    ν x ≤ mass ν s := single_le_sum (fun y _ => hν y) hx
omit [DecidableEq X] in
lemma mass_le_one (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (s : Finset X) :
    mass ν s ≤ 1 := by simpa [mass, hs] using mass_mono hν (subset_univ s)
end Mass

section Supports
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
abbrev State := A × B

def row (a : A) : Finset (A × B) := univ.filter (fun x => x.1 = a)
def col (b : B) : Finset (A × B) := univ.filter (fun x => x.2 = b)

def Permitted (U : Finset (A × B)) : Prop :=
  (∃ a, U = row a) ∨ (∃ b, U = col b) ∨ U.card ≤ 2

lemma high_row_unique {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2) {a a' : A}
    (ha : 1-η ≤ mass ν (row a)) (ha' : 1-η ≤ mass ν (row a')) : a = a' := by
  by_contra hn
  have hd : Disjoint (row a : Finset (A × B)) (row a') := by
    simp only [disjoint_left, row, mem_filter, mem_univ, true_and]
    intro x hx hx'
    exact hn (hx.symm.trans hx')
  have hu := mass_le_one hν hs (row a ∪ row a')
  rw [mass, sum_union hd] at hu
  change mass ν (row a) + mass ν (row a') ≤ 1 at hu
  linarith

lemma high_col_unique {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2) {b b' : B}
    (hb : 1-η ≤ mass ν (col b)) (hb' : 1-η ≤ mass ν (col b')) : b = b' := by
  by_contra hn
  have hd : Disjoint (col b : Finset (A × B)) (col b') := by
    simp only [disjoint_left, col, mem_filter, mem_univ, true_and]
    intro x hx hx'
    exact hn (hx.symm.trans hx')
  have hu := mass_le_one hν hs (col b ∪ col b')
  rw [mass, sum_union hd] at hu
  change mass ν (col b) + mass ν (col b') ≤ 1 at hu
  linarith

noncomputable def rowException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if h : ∃ a, 1-η ≤ mass ν (row a) then (row h.choose)ᶜ else ∅
noncomputable def colException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if h : ∃ b, 1-η ≤ mass ν (col b) then (col h.choose)ᶜ else ∅
noncomputable def smallException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if ∃ U : Finset (A × B), U.card ≤ 2 ∧ 1-η ≤ mass ν U
    then univ.filter (fun x => ν x ≤ η) else ∅
noncomputable def exception (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) :=
  rowException ν η ∪ colException ν η ∪ smallException ν η

lemma rowException_mass {ν : A × B → ℝ} (hs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 ≤ η) : mass ν (rowException ν η) ≤ η := by
  unfold rowException
  split_ifs with h
  · rw [mass_compl hs]; linarith [h.choose_spec]
  · simpa [mass] using hη
lemma colException_mass {ν : A × B → ℝ} (hs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 ≤ η) : mass ν (colException ν η) ≤ η := by
  unfold colException
  split_ifs with h
  · rw [mass_compl hs]; linarith [h.choose_spec]
  · simpa [mass] using hη

lemma smallException_mass {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : 0 ≤ η) :
    mass ν (smallException ν η) ≤ 3*η := by
  classical
  unfold smallException
  split_ifs with h
  · obtain ⟨U, hUcard, hU⟩ := h
    have hsub : univ.filter (fun x => ν x ≤ η) ⊆
        Uᶜ ∪ U.filter (fun x => ν x ≤ η) := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact mem_union_right _ (mem_filter.mpr ⟨hxU, (mem_filter.mp hx).2⟩)
      · exact mem_union_left _ (mem_compl.mpr hxU)
    have hsmall : mass ν (U.filter (fun x => ν x ≤ η)) ≤ 2*η := by
      calc
        _ ≤ ∑ _x ∈ U.filter (fun x => ν x ≤ η), η :=
          sum_le_sum (fun x hx => (mem_filter.mp hx).2)
        _ = ((U.filter (fun x => ν x ≤ η)).card : ℝ) * η := by simp
        _ ≤ 2*η := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le U _).trans hUcard) hη
    have huu := mass_union_le hν Uᶜ (U.filter (fun x => ν x ≤ η))
    have hmm := mass_mono hν hsub
    rw [mass_compl hs] at huu
    linarith
  · simp [mass]; positivity

lemma exception_mass {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : 0 ≤ η) :
    mass ν (exception ν η) ≤ 5*η := by
  have h₁ := mass_union_le hν (rowException ν η) (colException ν η)
  have h₂ := mass_union_le hν (rowException ν η ∪ colException ν η) (smallException ν η)
  have h₃ := rowException_mass hs hη
  have h₄ := colException_mass hs hη
  have h₅ := smallException_mass hν hs hη
  dsimp [exception]
  linarith

lemma outside_exception_mem {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2)
    {U : Finset (A × B)} (hU : Permitted U) (hm : 1-η ≤ mass ν U)
    {x : A × B} (hx : x ∉ exception ν η) : x ∈ U := by
  classical
  have hxR : x ∉ rowException ν η := fun h => hx (mem_union_left _ (mem_union_left _ h))
  have hxC : x ∉ colException ν η := fun h => hx (mem_union_left _ (mem_union_right _ h))
  have hxS : x ∉ smallException ν η := fun h => hx (mem_union_right _ h)
  rcases hU with ⟨a, rfl⟩ | ⟨b, rfl⟩ | hcard
  · have h : ∃ a', 1-η ≤ mass ν (row a') := ⟨a, hm⟩
    simp only [rowException, dite_eq_left h, mem_compl, not_not] at hxR
    have he := high_row_unique hν hs hη h.choose_spec hm
    simpa only [he] using hxR
  · have h : ∃ b', 1-η ≤ mass ν (col b') := ⟨b, hm⟩
    simp only [colException, dite_eq_left h, mem_compl, not_not] at hxC
    have he := high_col_unique hν hs hη h.choose_spec hm
    simpa only [he] using hxC
  · have h : ∃ U', U'.card ≤ 2 ∧ 1-η ≤ mass ν U' := ⟨U, hcard, hm⟩
    simp only [smallException, ite_eq_left h, mem_filter, mem_univ, true_and, not_le] at hxS
    by_contra hxn
    have ha := atom_le_mass hν (mem_compl.mpr hxn)
    rw [mass_compl hs] at ha
    linarith
end Supports

section Posterior
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]
  [DecidableEq H] [DecidableEq A] [DecidableEq B]

noncomputable def historyMass (μ : P → ℝ) (h : P → H) (a : H) : ℝ :=
  ∑ p, if h p = a then μ p else 0
noncomputable def posterior (μ : P → ℝ) (h : P → H) (a : H) (p : P) : ℝ :=
  (if h p = a then μ p else 0) / historyMass μ h a
noncomputable def statePosterior (μ : P → ℝ) (h : P → H)
    (X : P → A × B) (a : H) (x : A × B) : ℝ := ∑ p, if X p = x then posterior μ h a p else 0

omit [Fintype H] in
lemma historyMass_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (h : P → H) (a : H) :
    0 ≤ historyMass μ h a := sum_nonneg fun p _ => by split; exact hμ p; exact le_rfl
omit [Fintype H] in
lemma historyMass_pos (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → H) (p : P) :
    0 < historyMass μ h (h p) := by
  apply lt_of_lt_of_le (hμ p)
  have hh := single_le_sum (f := fun x => if h x = h p then μ x else 0)
    (fun x _ => by split; exact (hμ x).le; exact le_rfl) (mem_univ p)
  simpa [historyMass] using hh
omit [Fintype H] in
lemma posterior_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (h : P → H) (a : H) (p : P) :
    0 ≤ posterior μ h a p := by
  unfold posterior
  exact div_nonneg (by split; exact hμ p; exact le_rfl) (historyMass_nonneg μ hμ h a)
omit [Fintype H] in
lemma posterior_stationary (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → H) (x : P) :
    ∑ p, μ p * posterior μ h (h p) x = μ x := by
  have he (p : P) : μ p * posterior μ h (h p) x =
      (if h p = h x then μ p else 0) * (μ x / historyMass μ h (h x)) := by
    by_cases hp : h p = h x
    · simp [posterior, hp]
    · simp [posterior, hp, Ne.symm hp]
  simp_rw [he]
  rw [← sum_mul]
  change historyMass μ h (h x) * (μ x / historyMass μ h (h x)) = μ x
  exact mul_div_cancel₀ _ (historyMass_pos μ hμ h x).ne'

omit [Fintype H] in
lemma posterior_function (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (h : P → H) (f : H → P → ℝ) :
    (∑ p, μ p * ∑ x, posterior μ h (h p) x * f (h p) x) =
      ∑ x, μ x * f (h x) x := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have he (p : P) : μ p * (posterior μ h (h p) x * f (h p) x) =
      (μ p * posterior μ h (h p) x) * f (h x) x := by
    by_cases hp : h p = h x
    · rw [hp]; ring
    · simp [posterior, Ne.symm hp]
  simp_rw [he]
  rw [← sum_mul, posterior_stationary μ hμ h]

omit [Fintype H] [Fintype A] [Fintype B] in
lemma statePosterior_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (h : P → H) (X : P → A × B) (a : H) (x : A × B) :
    0 ≤ statePosterior μ h X a x := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact posterior_nonneg μ hμ h a p
  · rfl
omit [Fintype H] in
lemma statePosterior_sum (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (h : P → H) (X : P → A × B) (p : P) : ∑ x, statePosterior μ h X (h p) x = 1 := by
  unfold statePosterior
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, posterior, ← sum_div]
  exact div_self (historyMass_pos μ hμ h p).ne'
omit [Fintype H] [Fintype A] [Fintype B] in
lemma statePosterior_mass (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (a : H) (U : Finset (A × B)) :
    mass (statePosterior μ h X a) U =
      ∑ p, posterior μ h a p * if X p ∈ U then 1 else 0 := by
  unfold mass statePosterior
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases hp : X p ∈ U <;> simp [hp]

omit [Fintype H] in

lemma actual_exception_mass (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    {η : ℝ} (hη : 0 ≤ η) :
    (∑ p, μ p * if X p ∈ exception (statePosterior μ h X (h p)) η then 1 else 0) ≤ 5*η := by
  classical
  let f : H → P → ℝ := fun a p =>
    if X p ∈ exception (statePosterior μ h X a) η then 1 else 0
  have he := posterior_function μ hμ h f
  change (∑ p, μ p * f (h p) p) ≤ 5*η
  rw [← he]
  calc
    _ ≤ ∑ p, μ p * (5*η) := by
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hμ p).le
      change (∑ x, posterior μ h (h p) x *
        if X x ∈ exception (statePosterior μ h X (h p)) η then 1 else 0) ≤ 5*η
      rw [← statePosterior_mass]
      exact exception_mass (statePosterior_nonneg μ (fun p => (hμ p).le) h X (h p))
        (statePosterior_sum μ hμ h X p) hη
    _ = 5*η := by rw [← sum_mul, hsμ, one_mul]
end Posterior

section Transfer
variable {P H A B T : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]
  [Fintype T] [DecidableEq H] [DecidableEq A] [DecidableEq B]

omit [Fintype H] in

theorem restricted_transfer (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    (w : P → T → ℝ) (hw : ∀ p t, 0 ≤ w p t) (hwμ : ∀ p, ∑ t, w p t = μ p)
    (U : T → Finset (A × B)) (hU : ∀ t, Permitted (U t))
    (G : T → Prop) [DecidablePred G] {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    (hG : ∀ t, G t →
      (∑ p, w p t * mass (statePosterior μ h X (h p)) (U t)ᶜ) ≤
        3*η^2 * ∑ p, w p t) :
    (∑ p, ∑ t, w p t * if G t ∧ X p ∉ U t then 1 else 0) ≤ 8*η := by
  classical
  let ν := statePosterior μ h X
  let exc (p : P) : ℝ := if X p ∈ exception (ν (h p)) η then 1 else 0
  have hexc0 (p : P) : 0 ≤ exc p := by dsimp [exc]; split <;> norm_num
  have hν (p : P) : ∀ x, 0 ≤ ν (h p) x :=
    statePosterior_nonneg μ (fun p => (hμ p).le) h X (h p)
  have hsν (p : P) : ∑ x, ν (h p) x = 1 := statePosterior_sum μ hμ h X p
  have hpt (p : P) (t : T) :
      w p t * (if G t ∧ X p ∉ U t then 1 else 0) ≤
        (if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) + w p t * exc p := by
    have hnn := mul_nonneg (hw p t) (mass_nonneg (hν p) (U t)ᶜ)
    by_cases hg : G t
    · simp only [hg, true_and, ite_true]
      by_cases hx : X p ∈ U t
      · simp only [hx, not_true_eq_false, ite_false, mul_zero]
        exact add_nonneg (div_nonneg hnn hη.le) (mul_nonneg (hw p t) (hexc0 p))
      by_cases hc : 1-η ≤ mass (ν (h p)) (U t)
      · have hxexc : X p ∈ exception (ν (h p)) η := by
          by_contra hn
          exact hx (outside_exception_mem (hν p) (hsν p) hη' (hU t) hc hn)
        simp only [hx, not_false_eq_true, ite_true, mul_one]
        have hex : exc p = 1 := ite_eq_left hxexc
        rw [hex, mul_one]
        linarith [div_nonneg hnn hη.le]
      · have hmc : η ≤ mass (ν (h p)) (U t)ᶜ := by
          rw [mass_compl (hsν p)]; linarith [lt_of_not_ge hc]
        have hmul := mul_le_mul_of_nonneg_left hmc (hw p t)
        have hd : w p t ≤ w p t * mass (ν (h p)) (U t)ᶜ / η :=
          (le_div_iff₀ hη).mpr hmul
        simp only [hx, not_false_eq_true, ite_true, mul_one]
        linarith [mul_nonneg (hw p t) (hexc0 p)]
    · simp only [hg, false_and, ite_false, mul_zero, zero_add]
      exact mul_nonneg (hw p t) (hexc0 p)
  have hlocal (t : T) :
      (∑ p, if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) ≤
        3*η * ∑ p, w p t := by
    by_cases hg : G t
    · simp only [hg, ite_true, ← sum_div]
      apply (div_le_iff₀ hη).mpr
      calc
        _ ≤ 3*η^2 * ∑ p, w p t := hG t hg
        _ = _ := by ring
    · simp only [hg, ite_false, sum_const_zero]
      exact mul_nonneg (by positivity) (sum_nonneg (fun p _ => hw p t))
  have htt : (∑ p, ∑ t, w p t) = 1 := by simp_rw [hwμ]; exact hsμ
  calc
    _ ≤ ∑ p, ∑ t,
          ((if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) + w p t * exc p) :=
      sum_le_sum (fun p _ => sum_le_sum (fun t _ => hpt p t))
    _ = (∑ t, ∑ p, if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) +
        ∑ p, μ p * exc p := by
      simp only [sum_add_distrib, ← sum_mul, hwμ]
      rw [sum_comm]
    _ ≤ (∑ t, 3*η * ∑ p, w p t) + 5*η := by
      apply add_le_add
      · exact sum_le_sum (fun t _ => hlocal t)
      · exact actual_exception_mass μ hμ hsμ h X hη.le
    _ = 8*η := by
      rw [← mul_sum, sum_comm, htt]
      ring
end Transfer

section EdgeTemplate
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ] [DecidableEq H] [DecidableEq A] [DecidableEq B]

noncomputable def centerMixture (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (q : Q) (x : A × B) : ℝ :=
  ∑ p, edge p q / (∑ r, edge r q) * statePosterior μ h X (h p) x

omit [Fintype Q] [Fintype H] [Fintype A] [Fintype B] in
lemma centerMixture_mass (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (q : Q) (U : Finset (A × B)) :
    mass (centerMixture μ h X edge q) U =
      (∑ p, edge p q * mass (statePosterior μ h X (h p)) U) / (∑ r, edge r q) := by
  unfold mass centerMixture
  rw [sum_comm]
  simp only [← mul_sum, div_mul_eq_mul_div, ← sum_div]

omit [Fintype H] in

theorem edge_template_transfer (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (he : ∀ p q, 0 ≤ edge p q)
    (heμ : ∀ p, ∑ q, edge p q = μ p) (hκ : ∀ q, 0 < ∑ p, edge p q)
    (a : Q → Θ → ℝ) (ha : ∀ q θ, 0 ≤ a q θ) (has : ∀ q, ∑ θ, a q θ = 1)
    (U : Q → Θ → Finset (A × B)) (hU : ∀ q θ, Permitted (U q θ))
    (G : Q → Θ → Prop) [∀ q, DecidablePred (G q)]
    {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    (hg : ∀ q θ, G q θ → 1-3*η^2 ≤ mass (centerMixture μ h X edge q) (U q θ)) :
    (∑ p, ∑ q, ∑ θ, edge p q * a q θ *
      if G q θ ∧ X p ∉ U q θ then 1 else 0) ≤ 8*η := by
  classical
  let w : P → Q × Θ → ℝ := fun p v => edge p v.1 * a v.1 v.2
  have hw : ∀ p v, 0 ≤ w p v := fun p v => mul_nonneg (he p v.1) (ha v.1 v.2)
  have hws (p : P) : ∑ v, w p v = μ p := by
    simp only [w, Fintype.sum_prod_type, ← mul_sum, has, mul_one, heμ]
  have hm (v : Q × Θ) (hv : G v.1 v.2) :
      (∑ p, w p v * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) ≤
        3*η^2 * ∑ p, w p v := by
    have hg' := hg v.1 v.2 hv
    rw [centerMixture_mass] at hg'
    have hg'' := (le_div_iff₀ (hκ v.1)).mp hg'
    have heq : (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) =
        (∑ p, edge p v.1) - ∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2) := by
      simp only [mass_compl (statePosterior_sum μ hμ h X _), mul_sub,
        mul_one, sum_sub_distrib]
    have hh : (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) ≤
        3*η^2 * ∑ p, edge p v.1 := by rw [heq]; nlinarith
    have hmult := mul_le_mul_of_nonneg_right hh (ha v.1 v.2)
    calc
      _ = (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) *
          a v.1 v.2 := by
        rw [sum_mul]
        apply sum_congr rfl
        intro p _
        dsimp [w]
        ring
      _ ≤ (3*η^2 * ∑ p, edge p v.1) * a v.1 v.2 := hmult
      _ = _ := by simp only [w, ← sum_mul]; ring
  have hfinal := restricted_transfer μ hμ hsμ h X w hw hws
    (fun v => U v.1 v.2) (fun v => hU v.1 v.2)
    (fun v => G v.1 v.2) hη hη' hm
  simpa only [Fintype.sum_prod_type, w] using hfinal
end EdgeTemplate

end PlanarUnitDistances.RestrictedTransfer

namespace PlanarUnitDistances.CrossStructure
open Finset StrictCross RestrictedTransfer
open scoped Classical
noncomputable section
variable {A B : Type*}

def Consistent (b : Bool) (x y : A×B) : Prop :=
  if b then x.1=y.1 ∧ x.2≠y.2 else x.1≠y.1 ∧ x.2=y.2

lemma consistent_adj {b : Bool} {x y : A×B} (h : Consistent b x y) : Adj x y := by
  cases b with
  | false => exact Or.inr h
  | true => exact Or.inl h
lemma consistent_symm {b : Bool} {x y : A×B} (h : Consistent b x y) : Consistent b y x := by
  cases b <;> dsimp [Consistent] at *
  · exact ⟨Ne.symm h.1,Eq.symm h.2⟩
  · exact ⟨Eq.symm h.1,Ne.symm h.2⟩
lemma bit_unique {b c : Bool} {x y : A×B} (h : Consistent b x y) (h' : Consistent c x y) : b=c := by
  cases b <;> cases c <;> simp_all [Consistent]
lemma bit_true {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.1=y.1) : b=true := by
  cases b <;> simp_all [Consistent]
lemma bit_false {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.2=y.2) : b=false := by
  cases b <;> simp_all [Consistent]

def Shape (Y U : Finset (A×B)) : Prop :=
  (∀ y∈Y,∀ z∈Y,y=z) ∨ (∀ x∈U,∀ z∈U,x=z) ∨
  (∃ b : Bool,∀ x∈U,∀ y∈Y,∀ c,Consistent c x y → c=b) ∨
  ((∀ x∈U,∀ y∈Y,∀ z∈Y,∀ b,Consistent b x y → Consistent b x z → y=z) ∧
   (∀ y∈Y,∀ x∈U,∀ z∈U,∀ b,Consistent b x y → Consistent b z y → x=z))

lemma card_pair_le (y z : A×B) : ({y,z} : Finset (A×B)).card≤3 := by
  have := card_insert_le y {z}
  simp only [card_singleton] at this
  omega
lemma card_triple_le (y z w : A×B) : ({y,z,w} : Finset (A×B)).card≤3 := by
  have h := card_insert_le y {z,w}
  have h' := card_insert_le z {w}
  simp only [card_singleton] at h'
  omega

lemma pair_coord_inj {S : Finset (A×B)} {y z : A×B} (h : ∀w∈S,w=y ∨ w=z)
    (h₁ : y.1≠z.1) (h₂ : y.2≠z.2) :
    (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v) := by
  constructor <;> intro u hu v hv he
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₁ he).elim
    · exact (h₁ he.symm).elim
    · rfl
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₂ he).elim
    · exact (h₂ he.symm).elim
    · rfl

lemma determined_of_inj {S : Finset (A×B)}
    (h : (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v))
    (x : A×B) (y : A×B) (hy : y∈S) (z : A×B) (hz : z∈S) (b : Bool)
    (hc : Consistent b x y) (hd : Consistent b x z) : y=z := by
  cases b with
  | false => exact h.2 y hy z hz (hc.2.symm.trans hd.2)
  | true => exact h.1 y hy z hz (hc.1.symm.trans hd.1)

variable [Fintype A] [Fintype B]

theorem witnesses (Y : Finset (A×B)) :
    ∃ W U : Finset (A×B), W⊆Y ∧ W.card≤3 ∧ (U=univ ∨ Permitted U) ∧
      (∀x,(∀w∈W,Adj x w) → x∈U) ∧ Shape Y U := by
  classical
  rcases classification Y with h|h|h|h
  · refine ⟨∅,univ,empty_subset _,by simp,Or.inl rfl,fun x _ => mem_univ x,Or.inl ?_⟩
    exact card_le_one.mp h
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},row y.1,?_,card_pair_le y z,Or.inr (Or.inl ⟨y.1,rfl⟩),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_row hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [row] using hx'.1
      · right; right; left
        refine ⟨true,?_⟩
        intro x hx v hv b hb
        have hx' : x.1=y.1 := by simpa [row] using hx
        exact bit_true hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(y.1,w.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hx' := third_off_row hn hwy.symm x (hx y (by simp))
          (by simpa only [Adj,← he] using hx z (by simp)) (hx w (by simp))
        exact mem_singleton.mpr hx'
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},col y.2,?_,card_pair_le y z,Or.inr (Or.inr (Or.inl ⟨y.2,rfl⟩)),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_column hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [col] using hx'.1
      · right; right; left
        refine ⟨false,?_⟩
        intro x hx v hv b hb
        have hx' : x.2=y.2 := by simpa [col] using hx
        exact bit_false hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(w.1,y.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hxy := (swap_iff x y).mpr (hx y (by simp))
        have hxz := (swap_iff x z).mpr (hx z (by simp))
        have hxw := (swap_iff x w).mpr (hx w (by simp))
        have hx' := third_off_row hn hwy.symm x.swap hxy
          (by simpa only [Prod.swap,← he] using hxz) hxw
        apply mem_singleton.mpr
        exact Prod.ext (congrArg Prod.snd hx') (congrArg Prod.fst hx')
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := h
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · refine ⟨{y,z},{(y.1,z.2),(z.1,y.2)},?_,card_pair_le y z,?_,?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · right; right; right
        exact (card_insert_le _ _).trans (by simp)
      · intro x hx
        simpa only [mem_insert,mem_singleton] using (corners h₁ h₂ x).mp ⟨hx y (by simp),hx z (by simp)⟩
      · right; right; right
        have hY := pair_coord_inj hall h₁ h₂
        have hU := pair_coord_inj (y := (y.1,z.2)) (z := (z.1,y.2)) (S := {(y.1,z.2),(z.1,y.2)})
          (by intro v hv; simpa only [mem_insert,mem_singleton] using hv) h₁ h₂.symm
        constructor
        · intro x _ u hu v hv b hc hd
          exact determined_of_inj hY x u hu v hv b hc hd
        · intro v _ x hx u hu b hc hd
          exact determined_of_inj hU v x hx u hu b (consistent_symm hc) (consistent_symm hd)
    · refine ⟨{y,z,w},∅,?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x
          ⟨hx y (by simp),hx z (by simp),hx w (by simp)⟩).elim
      · simp
end
end PlanarUnitDistances.CrossStructure

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma cond_tower_dep (μ : Law X) (φ : X → Y) (f : Y → X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) (f y)) = avg μ (fun x => f (φ x) x) := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

def left (π : Law (P×Q)) : Law P := push π Prod.fst
def right (π : Law (P×Q)) : Law Q := push π Prod.snd
def row (π : Law (P×Q)) (p : P) : Law Q := push (cond π Prod.fst p) Prod.snd
def col (π : Law (P×Q)) (q : Q) : Law P := push (cond π Prod.snd q) Prod.fst

lemma row_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (left π) (fun p => avg (row π p) (f p)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [row,push_avg]
  change avg (push π Prod.fst) _ = _
  exact cond_tower_dep π Prod.fst (fun p pq => f p pq.2)
lemma col_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (right π) (fun q => avg (col π q) (fun p => f p q)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [col,push_avg]
  change avg (push π Prod.snd) _ = _
  exact cond_tower_dep π Prod.snd (fun q pq => f pq.1 q)
lemma row_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (left π) (fun p => event (row π p) (g p)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact row_avg π _
lemma col_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (right π) (fun q => event (col π q) (fun p => g p q)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact col_avg π _

def DP (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : ℝ :=
  avg (left π) (fun p => score (row π p) (bit p) y)
def DQ (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : ℝ :=
  avg (right π) (fun q => score (col π q) (fun p => bit p q) x)
def VP (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (left π) (fun p => variation (row π p) (bit p))
def VQ (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (right π) (fun q => variation (col π q) (fun p => bit p q))
def bad (π : Law (P×Q)) (good : P → Q → Prop) : ℝ := event π (fun pq => ¬good pq.1 pq.2)

lemma vp_le (π : Law (P×Q)) (bit : P → Q → Bool) : VP π bit ≤ 1/2 :=
  avg_le_const _ (fun p => variation_le_half (row π p) (bit p))
lemma vq_le (π : Law (P×Q)) (bit : P → Q → Bool) : VQ π bit ≤ 1/2 :=
  avg_le_const _ (fun q => variation_le_half (col π q) (fun p => bit p q))
lemma dp_lower (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : -VP π bit ≤ DP π bit y := by
  have h := avg_mono (left π) (fun p => score_lower (row π p) (bit p) y)
  have he : avg (left π) (fun p => -variation (row π p) (bit p)) = -VP π bit := by
    calc
      _ = avg (left π) (fun p => (-1)*variation (row π p) (bit p)) :=
        avg_congr _ (fun p => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VP]
  exact he ▸ h
lemma dq_lower (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : -VQ π bit ≤ DQ π bit x := by
  have h := avg_mono (right π) (fun q => score_lower (col π q) (fun p => bit p q) x)
  have he : avg (right π) (fun q => -variation (col π q) (fun p => bit p q)) = -VQ π bit := by
    calc
      _ = avg (right π) (fun q => (-1)*variation (col π q) (fun p => bit p q)) :=
        avg_congr _ (fun q => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VQ]
  exact he ▸ h

theorem slice_score (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : P → Q → Prop) (Y U : Finset (A×B)) (hs : Shape Y U)
    (hg : ∀ p q,good p q → x p∈U ∧ y q∈Y ∧ Consistent (bit p q) (x p) (y q)) :
    (VP π bit+VQ π bit)/80000-12*bad π good ≤ DP π bit y+DQ π bit x := by
  have hbad : 0≤bad π good := event_nonneg _ _
  have hvp := vp_le π bit
  have hvq := vq_le π bit
  have hdp := dp_lower π bit y
  have hdq := dq_lower π bit x
  rcases hs with hs|hs|⟨b,hs⟩|⟨hsP,hsQ⟩
  · have h (p : P) := constant_good (row π p) (bit p) y (good p) (by
      intro q r hq hr
      have hy := hs (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1
      refine ⟨?_,hy⟩
      exact bit_unique (hg p q hq).2.2 (hy ▸ (hg p r hr).2.2))
    have ha := avg_mono (left π) h
    rw [avg_sub,avg_const,avg_smul,row_event] at ha
    change (1-1/20000:ℝ)-4*bad π good ≤ DP π bit y at ha
    linarith
  · have h (q : Q) := constant_good (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr
      have hx := hs (x p) (hg p q hp).1 (x r) (hg r q hr).1
      refine ⟨?_,hx⟩
      exact bit_unique (hg p q hp).2.2 (hx ▸ (hg r q hr).2.2))
    have ha := avg_mono (right π) h
    rw [avg_sub,avg_const,avg_smul,col_event] at ha
    change (1-1/20000:ℝ)-4*bad π good ≤ DQ π bit x at ha
    linarith
  · have hc : ∀p q,good p q → bit p q=b := by
      intro p q hp
      exact hs (x p) (hg p q hp).1 (y q) (hg p q hp).2.1 _ (hg p q hp).2.2
    have hp := avg_mono (left π) (fun p => constant_bit (row π p) (bit p) (good p)
      (by intro q r hq hr; exact (hc p q hq).trans (hc p r hr).symm))
    have hq := avg_mono (right π) (fun q => constant_bit (col π q) (fun p => bit p q) (fun p => good p q)
      (by intro p r hp hr; exact (hc p q hp).trans (hc r q hr).symm))
    rw [avg_smul,row_event] at hp
    rw [avg_smul,col_event] at hq
    change VP π bit ≤ 2*bad π good at hp
    change VQ π bit ≤ 2*bad π good at hq
    linarith
  · have hp := avg_mono (left π) (fun p => determined (row π p) (bit p) y (good p) (by
      intro q r hq hr hb
      apply hsP (x p) (hg p q hq).1 (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1 (bit p q)
      · exact (hg p q hq).2.2
      · exact hb ▸ (hg p r hr).2.2))
    have hq := avg_mono (right π) (fun q => determined (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr hb
      apply hsQ (y q) (hg p q hp).2.1 (x p) (hg p q hp).1 (x r) (hg r q hr).1 (bit p q)
      · exact (hg p q hp).2.2
      · exact hb ▸ (hg r q hr).2.2))
    rw [avg_sub,avg_const,avg_smul,row_event] at hp
    rw [avg_sub,avg_const,avg_smul,col_event] at hq
    change (1/40000:ℝ)-6*bad π good ≤ DP π bit y at hp
    change (1/40000:ℝ)-6*bad π good ≤ DQ π bit x at hq
    linarith
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

def exceptional (r : Bool) (l x : A×B) : Prop :=
  if r then x.2≠l.2 else x.1≠l.1

def nonshared (b : Bool) (y z : A×B) : Prop :=
  if b then y.2=z.2 else y.1=z.1

lemma normal_bits {r b c : Bool} {l x y z : A×B}
    (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) : b=c := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent]

lemma exceptional_bits {r b c : Bool} {l x y z : A×B}
    (hx : exceptional r l x) (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) :
    b=r ∧ c=r ∧ nonshared r y z := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent,nonshared]

lemma minority_exception {r b : Bool} {l x y : A×B}
    (hb : Consistent b x y) (hr : b=r) : exceptional r l x ∨ exceptional r l y := by
  subst b
  cases r <;> simp only [exceptional,Consistent,Bool.false_eq_true, ↓reduceIte] at *
  · by_contra! h; exact hb.1 (h.1.trans h.2.symm)
  · by_contra! h; exact hb.2 (h.1.trans h.2.symm)

def ind (h : Prop) : ℝ := if h then 1 else 0
lemma ind_nonneg (h : Prop) : 0≤ ind h := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (h : Prop) : ind h≤1 := by unfold ind; split_ifs <;> norm_num

def slot (r : Bool) (l x y z : A×B) (b c : Bool) : ℝ :=
  2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z)-ind (b≠c)

lemma slot_lower (r : Bool) (l x y z : A×B) (b c : Bool) :
    2*ind (exceptional r l x)-2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-ind (exceptional r l y)-
      ind (exceptional r l z)-3*ind (¬Consistent b x y)-3*ind (¬Consistent c x z) ≤
    slot r l x y z b c := by
  have hp := exceptional_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hn := normal_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hpos : 2*ind (exceptional r l x)-
      2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-
      2*ind (¬Consistent b x y)-2*ind (¬Consistent c x z) ≤
      2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  have hneg : ind (b≠c)≤ ind (exceptional r l y)+ind (exceptional r l z)+
      ind (¬Consistent b x y)+ind (¬Consistent c x z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  unfold slot
  linarith

variable [Fintype X]

theorem star_lower (μ : Law X) (r : Bool) (l base : A×B)
    (state : X → A×B) (bit : X → Bool) :
    2*ind (exceptional r l base)-
      4*event μ (fun y => exceptional r l base ∧ exceptional r l (state y))-
      2*event μ (fun y => exceptional r l (state y))-
      6*event μ (fun y => ¬Consistent (bit y) base (state y)) ≤
    avg (pair μ μ) (fun yz => slot r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2)) := by
  have hs := avg_mono (pair μ μ) (fun yz =>
    slot_lower r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2))
  simp only [avg_sub,avg_smul,avg_const] at hs
  have hf (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.1))=event μ g := by
    rw [pair_fst μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  have hg (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.2))=event μ g := by
    rw [pair_snd μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  rw [hf (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hg (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hf (fun y => exceptional r l (state y)),hg (fun y => exceptional r l (state y)),
    hf (fun y => ¬Consistent (bit y) base (state y)),
    hg (fun y => ¬Consistent (bit y) base (state y))] at hs
  linarith

end
end PlanarUnitDistances.RareScore

namespace PlanarUnitDistances.WedgeProfiles
open RareScore CrossStructure FiniteLaw
open scoped Classical
noncomputable section
variable {A B : Type*}

def value (b : Bool) : ℝ := if b then 1 else 0
def sign (r : Bool) : ℝ := if r then 1 else -1

lemma edge_residual (r b : Bool) (l x y : A×B) :
    |value b-(1-value r+sign r*(ind (exceptional r l x)+ind (exceptional r l y)))| ≤
      2*(ind (exceptional r l x ∧ exceptional r l y)+ind (¬Consistent b x y)) := by
  cases r <;> cases b <;>
    simp only [value,sign,Bool.false_eq_true,ite_false,ite_true,exceptional,Consistent]
  all_goals
    by_cases hx : x.1=l.1
    <;> by_cases hy : y.1=l.1
    <;> by_cases hx' : x.2=l.2
    <;> by_cases hy' : y.2=l.2
    <;> by_cases he : x.1=y.1
    <;> by_cases he' : x.2=y.2
    <;> simp_all [ind]
    <;> norm_num

lemma wedge_residual (r b c : Bool) (l x y z : A×B) :
    |value b-value c-sign r*(ind (exceptional r l x)-ind (exceptional r l z))| ≤
      2*(ind (exceptional r l x ∧ exceptional r l y)+ind (exceptional r l z ∧ exceptional r l y)+
        ind (¬Consistent b x y)+ind (¬Consistent c z y)) := by
  have hb := edge_residual r b l x y
  have hc := edge_residual r c l z y
  have he : value b-value c-sign r*(ind (exceptional r l x)-ind (exceptional r l z))=
      (value b-(1-value r+sign r*(ind (exceptional r l x)+ind (exceptional r l y))))-
      (value c-(1-value r+sign r*(ind (exceptional r l z)+ind (exceptional r l y)))) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma wedge_size (r b c : Bool) (l x y z : A×B) :
    ind (exceptional r l x)+ind (exceptional r l z)-
      2*(ind (exceptional r l x ∧ exceptional r l z)+
        ind (exceptional r l x ∧ exceptional r l y)+ind (exceptional r l z ∧ exceptional r l y)+
        ind (¬Consistent b x y)+ind (¬Consistent c z y)) ≤ |value b-value c| := by
  have hh := wedge_residual r b c l x y z
  have he : |sign r*(ind (exceptional r l x)-ind (exceptional r l z))|=
      ind (exceptional r l x)+ind (exceptional r l z)-2*ind (exceptional r l x ∧ exceptional r l z) := by
    cases r <;> by_cases hx : exceptional false l x <;> by_cases hz : exceptional false l z
    <;> by_cases hx' : exceptional true l x <;> by_cases hz' : exceptional true l z
    <;> simp_all [sign,ind]
    <;> norm_num
  have ht := abs_sub_le (sign r*(ind (exceptional r l x)-ind (exceptional r l z))) (value b-value c) 0
  rw [sub_zero,sub_zero,abs_sub_comm (sign r*_) (value b-value c),he] at ht
  linarith
end
end PlanarUnitDistances.WedgeProfiles

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma event_eq_sum (μ : Law X) (P : X → Prop) :
    event μ P = ∑ x, if P x then μ.val x else 0 := by
  unfold event avg
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma event_congr (μ : Law X) {P Q : X → Prop} (h : ∀ x,P x ↔ Q x) :
    event μ P=event μ Q := le_antisymm (event_mono μ (fun x => (h x).mp))
      (event_mono μ (fun x => (h x).mpr))

lemma event_true (μ : Law X) : event μ (fun _ => True)=1 := by
  simp [event,avg_const]
lemma event_false (μ : Law X) : event μ (fun _ => False)=0 := by
  simp [event,avg_const]

lemma event_exists_le (μ : Law X) (P : I → X → Prop) :
    event μ (fun x => ∃ i,P i x) ≤ ∑ i,event μ (P i) := by
  classical
  unfold event avg
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
  dsimp only
  split_ifs with hx
  · obtain ⟨i,hi⟩ := hx
    have := single_le_sum (s := univ) (f := fun i => if P i x then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa only [hi,ite_true] using this
  · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma avg_sum (μ : Law X) (f : I → X → ℝ) :
    avg μ (fun x => ∑ i,f i x) = ∑ i,avg μ (f i) := by
  simp only [avg,mul_sum]
  rw [sum_comm]

lemma sum_event_fibers (μ : Law X) (f : X → Y) : ∑ y,event μ (fun x => f x=y)=1 := by
  simp_rw [event_eq_sum]
  rw [sum_comm]
  simpa using μ.total

def independent (μ : Law X) (I : Type*) [Fintype I] [DecidableEq I] : Law (I → X) where
  val x := ∏ i,μ.val (x i)
  nonneg x := prod_nonneg fun i _ => μ.nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [μ.total]

lemma indicator_forall (P : I → Prop) :
    (if ∀ i,P i then (1:ℝ) else 0) = ∏ i,if P i then 1 else 0 := by
  classical
  by_cases h : ∀ i,P i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [h,ite_false]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]

variable [DecidableEq I]

lemma independent_event (μ : Law X) (P : I → X → Prop) :
    event (independent μ I) (fun x => ∀ i,P i (x i)) = ∏ i,event μ (P i) := by
  classical
  simp only [event_eq_sum,independent]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : ∀ i,P i (x i)
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [h,ite_false]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]

lemma independent_all (μ : Law X) (P : X → Prop) :
    event (independent μ I) (fun x => ∀ i,P (x i)) = (event μ P)^(Fintype.card I) := by
  rw [independent_event]
  simp

lemma equiv_avg {Y : Type*} [Fintype Y] (μ : Law X) (ν : Law Y) (e : X ≃ Y)
    (he : ∀ x,μ.val x=ν.val (e x)) (f : Y → ℝ) :
    avg μ (fun x => f (e x)) = avg ν f := by
  unfold avg
  simp_rw [he]
  exact e.sum_comp (fun y => ν.val y*f y)

lemma independent_split (μ : Law X) (i : I) (f : (I → X) → ℝ) :
    avg (independent μ I) f = avg μ (fun x =>
      avg (independent μ {j : I // j ≠ i}) (fun xs => f ((Equiv.piSplitAt i (fun _ => X)).symm (x,xs)))) := by
  classical
  let e := Equiv.piSplitAt i (fun _ => X)
  have he : ∀ xs : I → X, (independent μ I).val xs =
      (pair μ (independent μ {j : I // j ≠ i})).val (e xs) := by
    intro xs
    change (∏ j,μ.val (xs j)) = μ.val (xs i)* ∏ j : {j : I // j ≠ i},μ.val (xs j)
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    congr 1
    exact Finset.prod_subtype (univ.erase i) (fun j => by simp) (fun j => μ.val (xs j))
  have h := equiv_avg (independent μ I) (pair μ (independent μ {j : I // j ≠ i}))
    e he (fun z => f (e.symm z))
  simp only [Equiv.symm_apply_apply] at h
  rw [h,pair_avg]

lemma independent_two_split (μ : Law X) (i j : I) (hij : i≠j)
    (f : (I → X) → ℝ) :
    avg (independent μ I) f = avg μ (fun x => avg μ (fun y =>
      avg (independent μ {l : {l : I // l ≠ i} // l ≠ ⟨j,hij.symm⟩}) (fun xs =>
        f ((Equiv.piSplitAt i (fun _ => X)).symm (x,
          (Equiv.piSplitAt (⟨j,hij.symm⟩ : {l : I // l≠i}) (fun _ => X)).symm (y,xs)))))) := by
  classical
  rw [independent_split μ i]
  apply avg_congr
  intro x
  exact independent_split μ (⟨j,hij.symm⟩ : {l : I // l≠i}) _
end
end PlanarUnitDistances.FiniteLaw

end OAI
