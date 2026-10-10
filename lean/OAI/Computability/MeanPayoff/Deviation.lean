import OAI.Computability.MeanPayoff.Recursion

namespace OAI

section

namespace MeanPayoff

def deviation (G : Game) (y q : Vec (Fin G.n)) : ℤ :=
  Finset.univ.sup' ⟨⟨0, G.positive⟩, Finset.mem_univ _⟩ (fun i => y i - q i)

theorem le_deviation (G : Game) (y q : Vec (Fin G.n)) (i : Fin G.n) :
    y i - q i ≤ deviation G y q :=
  Finset.le_sup' (fun j => y j - q j) (Finset.mem_univ i)

theorem deviation_le (G : Game) {y q : Vec (Fin G.n)} {d : ℤ}
    (h : ∀ i, y i - q i ≤ d) : deviation G y q ≤ d :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem deviation_attained (G : Game) (y q : Vec (Fin G.n)) :
    ∃ i, deviation G y q = y i - q i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset (Fin G.n)).Nonempty from ⟨⟨0, G.positive⟩, Finset.mem_univ _⟩)
    (fun i => y i - q i)
  exact ⟨i, hi⟩

def highCore {n Bmax : ℕ} (I : SolveBox n Bmax) (y : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * I.width - I.width ≤
    (globalS Bmax : ℤ) * (y i - I.a i))
def lowCore {n Bmax : ℕ} (I : SolveBox n Bmax) (z : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * I.width - I.width ≤
    (globalS Bmax : ℤ) * (I.b i - z i))

def nearHigh (G : Game) (y q : Vec (Fin G.n)) (A : ℕ) : Finset (Fin G.n) :=
  Finset.univ.filter (fun i => deviation G y q - 2 * A < y i - q i)
def nearLow (G : Game) (z q : Vec (Fin G.n)) (A : ℕ) : Finset (Fin G.n) :=
  Finset.univ.filter (fun i => deviation G q z - 2 * A < q i - z i)

namespace SolveBox

theorem radius_bounds {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    I.width ≤ 64 * globalS Bmax * I.D ∧ globalS Bmax * I.D ≤ I.E ∧
    32 * globalS Bmax * I.D ≤ I.width ∧ 8 * I.E ≤ I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  have hdm := Nat.div_add_mod I.width (32 * globalS Bmax)
  have hdr := Nat.mod_lt I.width (show 0 < 32 * globalS Bmax by omega)
  have he := Nat.div_mul_le_self I.width 8
  have hem := Nat.div_add_mod I.width 8
  have her := Nat.mod_lt I.width (show 0 < 8 by omega)
  change I.width ≤ 64 * globalS Bmax * (I.width / (32 * globalS Bmax)) ∧
    globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width / 8 ∧
    32 * globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width ∧
    8 * (I.width / 8) ≤ I.width
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem midpoint_twice {n Bmax : ℕ} (I : SolveBox n Bmax) (i : Fin n) :
    I.b i - I.a i - 1 ≤ 2 * (I.midpoint.val i - I.a i) ∧
    2 * (I.midpoint.val i - I.a i) ≤ I.b i - I.a i := by
  change I.b i - I.a i - 1 ≤ 2 * ((I.a i + I.b i) / 2 - I.a i) ∧
    2 * ((I.a i + I.b i) / 2 - I.a i) ≤ I.b i - I.a i
  omega

theorem average_movement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I)
    {A : ℤ} (_hA : 0 ≤ A) {r₁ r₂ : Vec (Fin n)}
    (h₁ : InBox (fun i => q.val i - A) (fun i => q.val i + A) r₁)
    (h₂ : InBox (fun i => q.val i - A) (fun i => q.val i + A) r₂) (i : Fin n) :
    |(I.averageClipped r₁ r₂).val i - q.val i| ≤ A := by
  have h1a : q.val i - A ≤ r₁ i := h₁.1 i
  have h1b : r₁ i ≤ q.val i + A := h₁.2 i
  have h2a : q.val i - A ≤ r₂ i := h₂.1 i
  have h2b : r₂ i ≤ q.val i + A := h₂.2 i
  have ha : I.a i ≤ q.val i := q.property.1 i
  have hb : q.val i ≤ I.b i := q.property.2 i
  rw [abs_le]
  change -A ≤ min (I.b i) (max (I.a i) ((r₁ i + r₂ i) / 2)) - q.val i ∧
    min (I.b i) (max (I.a i) ((r₁ i + r₂ i) / 2)) - q.val i ≤ A
  omega

end SolveBox

theorem highCore_support {n Bmax : ℕ} (I : SolveBox n Bmax) (y : Vec (Fin n)) :
    highCore I y ⊆ lowerActive I.a y := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  simp only [lowerActive, Finset.mem_filter, Finset.mem_univ, true_and]
  nlinarith

theorem lowCore_support {n Bmax : ℕ} (I : SolveBox n Bmax) (z : Vec (Fin n)) :
    lowCore I z ⊆ upperActive I.b z := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  simp only [upperActive, Finset.mem_filter, Finset.mem_univ, true_and]
  nlinarith

theorem high_initial_deficit (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : y ≤ I.b) {i : Fin G.n} (hi : i ∈ highCore I y) :
    (globalS Bmax : ℤ) * (deviation G y I.midpoint.val - (y i - I.midpoint.val i)) ≤
      I.width + globalS Bmax := by
  obtain ⟨j, hj⟩ := deviation_attained G y I.midpoint.val
  have hmt := I.midpoint_twice j
  have hmi := I.midpoint_twice i
  have hwj := I.width_bound j
  have hwi := I.width_bound i
  have hyj : y j ≤ I.b j := hy j
  have hcore := (Finset.mem_filter.mp hi).2
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hmul₁ := mul_le_mul_of_nonneg_left hmt.1 hs
  have hmul₂ := mul_le_mul_of_nonneg_left hmi.2 hs
  have hmul₃ := mul_le_mul_of_nonneg_left hwj hs
  have hmul₄ := mul_le_mul_of_nonneg_left hwi hs
  have hmul₅ := mul_le_mul_of_nonneg_left hyj hs
  rw [hj]
  nlinarith only [hcore, hs, hmul₁, hmul₂, hmul₃, hmul₄, hmul₅]

theorem low_initial_deficit (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : I.a ≤ z) {i : Fin G.n} (hi : i ∈ lowCore I z) :
    (globalS Bmax : ℤ) * (deviation G I.midpoint.val z - (I.midpoint.val i - z i)) ≤
      I.width + globalS Bmax := by
  obtain ⟨j, hj⟩ := deviation_attained G I.midpoint.val z
  have hmt := I.midpoint_twice j
  have hmi := I.midpoint_twice i
  have hwj := I.width_bound j
  have hwi := I.width_bound i
  have hzj : I.a j ≤ z j := hz j
  have hcore := (Finset.mem_filter.mp hi).2
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hmul₁ := mul_le_mul_of_nonneg_left hmt.2 hs
  have hmul₂ := mul_le_mul_of_nonneg_left hmi.1 hs
  have hmul₃ := mul_le_mul_of_nonneg_left hwj hs
  have hmul₄ := mul_le_mul_of_nonneg_left hwi hs
  have hmul₅ := mul_le_mul_of_nonneg_left hzj hs
  rw [hj]
  nlinarith only [hcore, hs, hmul₁, hmul₂, hmul₃, hmul₄, hmul₅]

theorem high_center_deviation (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {y q : Vec (Fin G.n)}
    (hy : y ≤ I.b) (hcore : (highCore I y).Nonempty)
    (hq : ∀ i, |q i - I.midpoint.val i| ≤ (globalS Bmax : ℤ) * I.D) :
    2 * (I.E : ℤ) ≤ deviation G y q := by
  obtain ⟨i, hi⟩ := hcore
  have hic := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hm := I.midpoint_twice i
  have hyi : y i ≤ I.b i := hy i
  have hw := I.width_bound i
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hwgt : (y i - I.a i) ≤ I.width := by omega
  have h15 : 15 * (I.width : ℤ) ≤ 16 * (y i - I.a i) := by
    nlinarith only [hic, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hwgt)]
  have hr := I.radius_bounds hB
  have hD : 32 * (globalS Bmax : ℤ) * I.D ≤ I.width := by exact_mod_cast hr.2.2.1
  have hE : 8 * (I.E : ℤ) ≤ I.width := by exact_mod_cast hr.2.2.2
  have hq' := (abs_le.mp (hq i)).2
  have hd := le_deviation G y q i
  nlinarith only [h15, hm.2, hw, hb, hD, hE, hq', hd]

theorem low_center_deviation (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {z q : Vec (Fin G.n)}
    (hz : I.a ≤ z) (hcore : (lowCore I z).Nonempty)
    (hq : ∀ i, |q i - I.midpoint.val i| ≤ (globalS Bmax : ℤ) * I.D) :
    2 * (I.E : ℤ) ≤ deviation G q z := by
  obtain ⟨i, hi⟩ := hcore
  have hic := (Finset.mem_filter.mp hi).2
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hm := I.midpoint_twice i
  have hzi : I.a i ≤ z i := hz i
  have hw := I.width_bound i
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hwgt : (I.b i - z i) ≤ I.width := by omega
  have h15 : 15 * (I.width : ℤ) ≤ 16 * (I.b i - z i) := by
    nlinarith only [hic, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hwgt)]
  have hr := I.radius_bounds hB
  have hD : 32 * (globalS Bmax : ℤ) * I.D ≤ I.width := by exact_mod_cast hr.2.2.1
  have hE : 8 * (I.E : ℤ) ≤ I.width := by exact_mod_cast hr.2.2.2
  have hq' := (abs_le.mp (hq i)).1
  have hd := le_deviation G q z i
  have hb' : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  nlinarith only [h15, hm.1, hw, hb, hD, hE, hq', hd, hb', hs]


namespace RandomTree

open Classical in
@[simp] theorem probability_leaf {α : Type} (a : α) (P : α → Prop) :
    (leaf a).probability P = if P a then 1 else 0 := by
  classical
  rfl

theorem probability_zero_of_all {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All (fun a => ¬P a)) : t.probability P = 0 := by
  classical
  apply le_antisymm _ (probability_nonneg t P)
  have hh := expect_mono_all t (fun a => if P a then (1 : ℚ) else 0) (fun _ => 0)
    (all_mono _ h (fun a ha => by simp [ha]))
  simpa [probability] using hh

theorem bind_error {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (good : α → Prop) (bad : β → Prop) {ρ ε : ℚ} (hε : 0 ≤ ε)
    (ht : t.probability (fun a => ¬good a) ≤ ρ)
    (hf : ∀ a, good a → (f a).probability bad ≤ ε) :
    (t.bind f).probability bad ≤ ρ + ε := by
  classical
  have hs : (t.bind f).probability bad ≤ t.probability (fun a => ¬good a) + ε := by
    unfold probability
    rw [expect_bind]
    rw [← expect_const t ε, ← expect_add]
    apply expect_mono
    intro a
    by_cases ha : good a
    · simpa [ha, probability] using hf a ha
    · have hh := probability_le_one (f a) bad
      simp only [ha, not_false_eq_true, ite_true]
      change (f a).probability bad ≤ 1 + ε
      linarith
  linarith

theorem bind_probability_le {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (bad : β → Prop) {ε : ℚ} (hf : ∀ a, (f a).probability bad ≤ ε) :
    (t.bind f).probability bad ≤ ε := by
  classical
  unfold probability
  rw [expect_bind, ← expect_const t ε]
  exact expect_mono t _ _ hf

theorem map_error {α β : Type} (t : RandomTree α) (f : α → β)
    (good : α → Prop) (bad : β → Prop) {ε : ℚ}
    (ht : t.probability (fun a => ¬good a) ≤ ε)
    (hf : ∀ a, good a → ¬bad (f a)) : (t.map f).probability bad ≤ ε := by
  rw [probability_map]
  apply le_trans _ ht
  exact probability_mono t (fun a ha hg => hf a hg ha)

end RandomTree

def Comparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (solver : (I : SolveBox G.n Bmax) → RandomTree (BoxVector I)) : Prop :=
  (∀ I y, AdmissibleSub (operator G) I.a I.b y P →
    (solver I).probability (fun p => ¬ y ≤ p.val) ≤ 1 / 16) ∧
  (∀ I z, AdmissibleSuper (operator G) I.a I.b z P →
    (solver I).probability (fun p => ¬ p.val ≤ z) ≤ 1 / 16)

def LowerComparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (lower : LowerSolver (Bmax := Bmax) P) : Prop :=
  ∀ Q hQ, Comparisons G Q (lower Q hQ)

theorem centered_active_high (G : Game) (y q : Vec (Fin G.n)) (A : ℕ) :
    lowerActive (fun i => q i - A) (centerSub y q (deviation G y q) A) = nearHigh G y q A := by
  ext i
  simp only [lowerActive, nearHigh, Finset.mem_filter, Finset.mem_univ, true_and,
    centerSub, lt_max_iff, lt_self_iff_false, or_false]
  omega

theorem centered_active_low (G : Game) (z q : Vec (Fin G.n)) (A : ℕ) :
    upperActive (fun i => q i + A) (centerSuper z q (deviation G q z) A) = nearLow G z q A := by
  ext i
  simp only [upperActive, nearLow, Finset.mem_filter, Finset.mem_univ, true_and,
    centerSuper, min_lt_iff, lt_self_iff_false, or_false]
  omega

theorem centered_admissible_high (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (q : BoxVector I) (A : ℕ) (hA : 0 < A) (hmax : 2 * A ≤ Bmax)
    (hd : 2 * (A : ℤ) ≤ deviation G y q.val) :
    AdmissibleSub (operator G) (SolveBox.centered q.val A hA hmax).a
      (SolveBox.centered q.val A hA hmax).b (centerSub y q.val (deviation G y q.val) A) P := by
  have hp := centered_subsolution (operator_laws G) hy.1 q.property
    (show (0 : ℤ) < A by exact_mod_cast hA) (le_deviation G y q.val) hd
  refine ⟨hp.1, ?_⟩
  apply le_trans _ hy.2
  apply mass_mono (fun i => (P.alpha_pos i).le)
  intro i hi
  have hi' : i ∈ subSupport (fun i => q.val i - A)
      (centerSub y q.val (deviation G y q.val) A) := (Finset.mem_filter.mp hi).2
  have hh := hp.2 hi'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩

theorem centered_admissible_low (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (q : BoxVector I) (A : ℕ) (hA : 0 < A) (hmax : 2 * A ≤ Bmax)
    (hd : 2 * (A : ℤ) ≤ deviation G q.val z) :
    AdmissibleSuper (operator G) (SolveBox.centered q.val A hA hmax).a
      (SolveBox.centered q.val A hA hmax).b (centerSuper z q.val (deviation G q.val z) A) P := by
  have hp := centered_supersolution (operator_laws G) hz.1 q.property
    (show (0 : ℤ) < A by exact_mod_cast hA) (le_deviation G q.val z) hd
  refine ⟨hp.1, ?_⟩
  apply le_trans _ hz.2
  apply mass_mono (fun i => (P.beta_pos i).le)
  intro i hi
  have hi' : i ∈ superSupport (fun i => q.val i + A)
      (centerSuper z q.val (deviation G q.val z) A) := (Finset.mem_filter.mp hi).2
  have hh := hp.2 hi'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩

end MeanPayoff
end

end OAI
