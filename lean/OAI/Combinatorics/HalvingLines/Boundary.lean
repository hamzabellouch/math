import OAI.Combinatorics.HalvingLines.Activity

namespace OAI

namespace PlanarHalving

namespace Boundary

lemma outside_strip {t c ρ : ℝ} (h : ¬ |t - c| ≤ 3 * ρ) :
    t < c - 3 * ρ ∨ c + 3 * ρ < t := by
  have h' : 3 * ρ < |t - c| := lt_of_not_ge h
  rcases lt_abs.mp h' with h' | h'
  · right
    linarith
  · left
    linarith

lemma initially_marked_loss {t c₀ cmin ρ : ℝ}
    (hρ : 0 ≤ ρ) (hmark : t < c₀)
    (hactive : cmin - ρ ≤ t)
    (hstrip₀ : ¬ |t - c₀| ≤ 3 * ρ)
    (hstripmin : ¬ |t - cmin| ≤ 3 * ρ) :
    cmin + 3 * ρ < t ∧ t < c₀ - 3 * ρ ∧ cmin + 6 * ρ < c₀ := by
  rcases outside_strip hstrip₀ with h₀ | h₀
  · rcases outside_strip hstripmin with hm | hm
    · linarith
    · exact ⟨hm, h₀, by linarith⟩
  · linarith

lemma initially_unmarked_gain {t c₀ cmax ρ : ℝ}
    (hρ : 0 ≤ ρ) (hunmark : c₀ ≤ t)
    (hactive : t ≤ cmax + ρ)
    (hstrip₀ : ¬ |t - c₀| ≤ 3 * ρ)
    (hstripmax : ¬ |t - cmax| ≤ 3 * ρ) :
    c₀ + 3 * ρ < t ∧ t < cmax - 3 * ρ ∧ c₀ + 6 * ρ < cmax := by
  rcases outside_strip hstrip₀ with h₀ | h₀
  · linarith
  · rcases outside_strip hstripmax with hm | hm
    · exact ⟨h₀, hm, by linarith⟩
    · linarith

theorem three_strips_core {α ι : Type*} [DecidableEq α]
    (M : ι → Finset α) (A B : Finset α) (t : α → ℝ)
    (c : ι → ℝ) (e : ι → α → ℝ) (i₀ imin imax : ι) (ρ : ℝ) (C : ℕ)
    (hρ : 0 ≤ ρ)
    (hmin : ∀ i, c imin ≤ c i) (hmax : ∀ i, c i ≤ c imax)
    (herr : ∀ i x, x ∈ B → |e i x| ≤ ρ)
    (hzero : ∀ x ∈ B, e i₀ x = 0)
    (hcut : ∀ i x, x ∈ B → (x ∈ M i ↔ t x + e i x < c i))
    (hactive : ∀ x ∈ A,
      (x ∈ M i₀ → ∃ i, x ∉ M i) ∧ (x ∉ M i₀ → ∃ i, x ∈ M i))
    (hbudget : ∀ i,
      (M i₀ ∩ B).card ≤ (M i ∩ B).card + C ∧
      (M i ∩ B).card ≤ (M i₀ ∩ B).card + C) :
    ((A ∩ B).filter fun x =>
      ¬ (|t x - c i₀| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
        |t x - c imax| ≤ 3 * ρ)).card ≤ 2 * C := by
  classical
  let H := (A ∩ B).filter fun x =>
    ¬ (|t x - c i₀| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
      |t x - c imax| ≤ 3 * ρ)
  let L := H.filter fun x => x ∈ M i₀
  let G := H.filter fun x => x ∉ M i₀
  have hH (x : α) (hx : x ∈ H) :
      x ∈ A ∧ x ∈ B ∧ ¬ |t x - c i₀| ≤ 3 * ρ ∧
        ¬ |t x - c imin| ≤ 3 * ρ ∧ ¬ |t x - c imax| ≤ 3 * ρ := by
    simpa only [H, Finset.mem_filter, Finset.mem_inter, not_or, and_assoc] using hx
  have hL (x : α) (hx : x ∈ L) :
      c imin + 3 * ρ < t x ∧ t x < c i₀ - 3 * ρ ∧ c imin + 6 * ρ < c i₀ := by
    obtain ⟨hxH, hxM⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxB, hx₀, hxm, _⟩ := hH x hxH
    have hmarked : t x < c i₀ := by
      simpa only [hzero x hxB, add_zero] using (hcut i₀ x hxB).mp hxM
    obtain ⟨i, hi⟩ := (hactive x hxA).1 hxM
    have hi' : c i ≤ t x + e i x := not_lt.mp fun h => hi ((hcut i x hxB).mpr h)
    have he := (abs_le.mp (herr i x hxB)).2
    have ht : c imin - ρ ≤ t x := by linarith [hmin i]
    exact initially_marked_loss hρ hmarked ht hx₀ hxm
  have hG (x : α) (hx : x ∈ G) :
      c i₀ + 3 * ρ < t x ∧ t x < c imax - 3 * ρ ∧ c i₀ + 6 * ρ < c imax := by
    obtain ⟨hxH, hxM⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxB, hx₀, _, hxmax⟩ := hH x hxH
    have hunmarked : c i₀ ≤ t x := by
      apply not_lt.mp
      intro h
      exact hxM ((hcut i₀ x hxB).mpr (by simpa only [hzero x hxB, add_zero] using h))
    obtain ⟨i, hi⟩ := (hactive x hxA).2 hxM
    have hi' := (hcut i x hxB).mp hi
    have he := (abs_le.mp (herr i x hxB)).1
    have ht : t x ≤ c imax + ρ := by linarith [hmax i]
    exact initially_unmarked_gain hρ hunmarked ht hx₀ hxmax
  have hLcard : L.card ≤ C := by
    by_cases hn : L.Nonempty
    · obtain ⟨x, hx⟩ := hn
      have hgap := (hL x hx).2.2
      have hsub : M imin ∩ B ⊆ M i₀ ∩ B := by
        intro y hy
        obtain ⟨hyM, hyB⟩ := Finset.mem_inter.mp hy
        refine Finset.mem_inter.mpr ⟨?_, hyB⟩
        by_contra hnM
        have hy₀ : c i₀ ≤ t y := by
          apply not_lt.mp
          intro h
          exact hnM ((hcut i₀ y hyB).mpr (by simpa only [hzero y hyB, add_zero] using h))
        have hymin := (hcut imin y hyB).mp hyM
        have he := (abs_le.mp (herr imin y hyB)).1
        linarith
      have hsubL : L ⊆ (M i₀ ∩ B) \ (M imin ∩ B) := by
        intro y hy
        obtain ⟨hyH, hyM⟩ := Finset.mem_filter.mp hy
        have hyB := (hH y hyH).2.1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hyM, hyB⟩, ?_⟩
        intro hymin
        have hc := (hcut imin y hyB).mp (Finset.mem_inter.mp hymin).1
        have he := (abs_le.mp (herr imin y hyB)).1
        have ht := (hL y hy).1
        linarith
      have hcount := Finset.card_sdiff_add_card_eq_card hsub
      have hle := Finset.card_le_card hsubL
      have hb := (hbudget imin).1
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]
  have hGcard : G.card ≤ C := by
    by_cases hn : G.Nonempty
    · obtain ⟨x, hx⟩ := hn
      have hgap := (hG x hx).2.2
      have hsub : M i₀ ∩ B ⊆ M imax ∩ B := by
        intro y hy
        obtain ⟨hyM, hyB⟩ := Finset.mem_inter.mp hy
        refine Finset.mem_inter.mpr ⟨(hcut imax y hyB).mpr ?_, hyB⟩
        have hy₀ : t y < c i₀ := by
          simpa only [hzero y hyB, add_zero] using (hcut i₀ y hyB).mp hyM
        have he := (abs_le.mp (herr imax y hyB)).2
        linarith
      have hsubG : G ⊆ (M imax ∩ B) \ (M i₀ ∩ B) := by
        intro y hy
        obtain ⟨hyH, hyM⟩ := Finset.mem_filter.mp hy
        have hyB := (hH y hyH).2.1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨?_, hyB⟩, ?_⟩
        · apply (hcut imax y hyB).mpr
          have he := (abs_le.mp (herr imax y hyB)).2
          have ht := (hG y hy).2.1
          linarith
        · exact fun hi => hyM (Finset.mem_inter.mp hi).1
      have hcount := Finset.card_sdiff_add_card_eq_card hsub
      have hle := Finset.card_le_card hsubG
      have hb := (hbudget imax).2
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]
  have hsplit : L.card + G.card = H.card := Finset.card_filter_add_card_filter_not (s := H) (fun x => x ∈ M i₀)
  change H.card ≤ 2 * C
  omega

lemma token_population {α τ : Type*} [DecidableEq α] [Fintype τ]
    (f : τ → α) (hf : Function.Injective f) (B : Finset α) :
    ((Finset.univ.image f) ∩ B).card =
      (Finset.univ.filter fun u => f u ∈ B).card := by
  classical
  rw [← Finset.filter_mem_eq_inter, Finset.filter_image,
    Finset.card_image_of_injective _ hf]

lemma filter_population_change {τ : Type*} [Fintype τ]
    (p q : τ → Prop) [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card +
      (Finset.univ.filter fun u => ¬ (p u ↔ q u)).card ∧
    (Finset.univ.filter q).card ≤ (Finset.univ.filter p).card +
      (Finset.univ.filter fun u => ¬ (p u ↔ q u)).card := by
  classical
  have h₁ : Finset.univ.filter p ⊆
      (Finset.univ.filter q) ∪ (Finset.univ.filter fun u => ¬ (p u ↔ q u)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : q u
    · exact Or.inl hq
    · exact Or.inr fun h => hq (h.mp hu)
  have h₂ : Finset.univ.filter q ⊆
      (Finset.univ.filter p) ∪ (Finset.univ.filter fun u => ¬ (p u ↔ q u)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hp : p u
    · exact Or.inl hp
    · exact Or.inr fun h => hp (h.mpr hu)
  exact ⟨(Finset.card_le_card h₁).trans (Finset.card_union_le _ _),
    (Finset.card_le_card h₂).trans (Finset.card_union_le _ _)⟩

theorem token_population_budget {τ : Type*} [Fintype τ]
    (inside : ℕ → τ → Prop) [∀ i, DecidablePred (inside i)] (m i : ℕ) (hi : i ≤ m) :
    let pop := fun j => (Finset.univ.filter (inside j)).card
    let cost := fun j => (Finset.univ.filter fun u =>
      ¬ (inside j u ↔ inside (j + 1) u)).card
    pop 0 ≤ pop i + ∑ j ∈ Finset.range m, cost j ∧
    pop i ≤ pop 0 + ∑ j ∈ Finset.range m, cost j := by
  classical
  dsimp only
  let pop := fun j => (Finset.univ.filter (inside j)).card
  let cost := fun j => (Finset.univ.filter fun u =>
    ¬ (inside j u ↔ inside (j + 1) u)).card
  change pop 0 ≤ pop i + ∑ j ∈ Finset.range m, cost j ∧
    pop i ≤ pop 0 + ∑ j ∈ Finset.range m, cost j
  have hpref (i : ℕ) :
      pop 0 ≤ pop i + ∑ j ∈ Finset.range i, cost j ∧
      pop i ≤ pop 0 + ∑ j ∈ Finset.range i, cost j := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := filter_population_change (inside i) (inside (i + 1))
      change pop i ≤ pop (i+1) + cost i ∧ pop (i+1) ≤ pop i + cost i at hstep
      rw [Finset.sum_range_succ]
      omega
  have hsum : ∑ j ∈ Finset.range i, cost j ≤ ∑ j ∈ Finset.range m, cost j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (by intros; omega)
  have hp := hpref i
  omega

theorem three_strips_tokens {α τ : Type*} [DecidableEq α] [Fintype τ]
    (m : ℕ) (f : ℕ → τ → α) (hf : ∀ i ≤ m, Function.Injective (f i))
    (A B : Finset α) (t : α → ℝ) (c : Fin (m + 1) → ℝ)
    (e : Fin (m + 1) → α → ℝ) (imin imax : Fin (m + 1)) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hmin : ∀ i, c imin ≤ c i) (hmax : ∀ i, c i ≤ c imax)
    (herr : ∀ i x, x ∈ B → |e i x| ≤ ρ)
    (hzero : ∀ x ∈ B, e 0 x = 0)
    (hcut : ∀ (i : Fin (m + 1)) (x : α), x ∈ B →
      (x ∈ Finset.univ.image (f i) ↔ t x + e i x < c i))
    (hactive : ∀ x ∈ A,
      (x ∈ Finset.univ.image (f 0) → ∃ i : Fin (m + 1),
        x ∉ Finset.univ.image (f i)) ∧
      (x ∉ Finset.univ.image (f 0) → ∃ i : Fin (m + 1),
        x ∈ Finset.univ.image (f i))) :
    ((A ∩ B).filter fun x =>
      ¬ (|t x - c 0| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
        |t x - c imax| ≤ 3 * ρ)).card ≤
      2 * ∑ j ∈ Finset.range m, (Finset.univ.filter fun u =>
        ¬ (f j u ∈ B ↔ f (j + 1) u ∈ B)).card := by
  classical
  apply three_strips_core (fun i : Fin (m + 1) => Finset.univ.image (f i))
    A B t c e 0 imin imax ρ _ hρ hmin hmax herr hzero hcut hactive
  intro i
  simp only [Fin.val_zero]
  rw [token_population _ (hf 0 (Nat.zero_le _)),
    token_population _ (hf i (by omega))]
  exact token_population_budget (fun j u => f j u ∈ B) m i (by omega)

lemma changes_initial {ι : Type*} (p : ι → Prop) (i₀ : ι)
    (hp : ∃ i j, ¬ (p i ↔ p j)) :
    (p i₀ → ∃ i, ¬ p i) ∧ (¬ p i₀ → ∃ i, p i) := by
  classical
  obtain ⟨i, j, h⟩ := hp
  constructor
  · intro _
    by_cases hi : p i
    · exact ⟨j, fun hj => h ⟨fun _ => hj, fun _ => hi⟩⟩
    · exact ⟨i, hi⟩
  · intro _
    by_cases hi : p i
    · exact ⟨i, hi⟩
    · refine ⟨j, ?_⟩
      by_contra hj
      exact h ⟨fun hpi => (hi hpi).elim, fun hpj => (hj hpj).elim⟩

def dot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2

def sqNorm (u : Point) : ℝ := u.1 ^ 2 + u.2 ^ 2

lemma dot_sq_le (u v : Point) : dot u v ^ 2 ≤ sqNorm u * sqNorm v := by
  unfold dot sqNorm
  nlinarith [sq_nonneg (u.1 * v.2 - u.2 * v.1)]

lemma abs_dot_le {u v : Point} {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ)
    (hu : sqNorm u ≤ θ ^ 2) (hv : sqNorm v ≤ D ^ 2) :
    |dot u v| ≤ D * θ := by
  have hs : 0 ≤ sqNorm v := by unfold sqNorm; positivity
  have hsq := (dot_sq_le u v).trans (mul_le_mul hu hv hs (sq_nonneg θ))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD hθ)).mp
  rw [sq_abs]
  nlinarith

theorem three_strips_geometric {τ : Type*} [Fintype τ]
    (m : ℕ) (f : ℕ → τ → Point) (hf : ∀ i ≤ m, Function.Injective (f i))
    (A B : Finset Point) (ν : Fin (m + 1) → Point) (c : Fin (m + 1) → ℝ)
    (imin imax : Fin (m + 1)) (D θ : ℝ)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ)
    (hmin : ∀ i, c imin ≤ c i) (hmax : ∀ i, c i ≤ c imax)
    (hnormal : ∀ i, sqNorm (ν i - ν 0) ≤ θ ^ 2)
    (hbounded : ∀ x ∈ B, sqNorm x ≤ D ^ 2)
    (hcut : ∀ (i : Fin (m + 1)) (x : Point), x ∈ B →
      (x ∈ Finset.univ.image (f i) ↔ dot (ν i) x < c i))
    (hactive : ∀ x ∈ A, ∃ i j : Fin (m + 1),
      ¬ (x ∈ Finset.univ.image (f i) ↔ x ∈ Finset.univ.image (f j))) :
    ((A ∩ B).filter fun x =>
      ¬ (|dot (ν 0) x - c 0| ≤ 3 * (D * θ) ∨
        |dot (ν 0) x - c imin| ≤ 3 * (D * θ) ∨
        |dot (ν 0) x - c imax| ≤ 3 * (D * θ))).card ≤
      2 * ∑ j ∈ Finset.range m, (Finset.univ.filter fun u =>
        ¬ (f j u ∈ B ↔ f (j + 1) u ∈ B)).card := by
  classical
  apply three_strips_tokens m f hf A B (dot (ν 0)) c
    (fun i x => dot (ν i - ν 0) x) imin imax (D * θ)
    (mul_nonneg hD hθ) hmin hmax
  · intro i x hx
    exact abs_dot_le hD hθ (hnormal i) (hbounded x hx)
  · intro x _
    simp [dot]
  · intro i x hx
    have hid : dot (ν 0) x + dot (ν i - ν 0) x = dot (ν i) x := by
      simp only [dot, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hid]
    exact hcut i x hx
  · intro x hx
    simpa only [Fin.val_zero] using
      changes_initial (fun i : Fin (m + 1) => x ∈ Finset.univ.image (f i)) 0
        (hactive x hx)

lemma active_le_outside_add_strips {α : Type*} [DecidableEq α]
    (A B : Finset α) (p q r : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] :
    (A ∩ B).card ≤
      ((A ∩ B).filter fun x => ¬ (p x ∨ q x ∨ r x)).card +
        (B.filter p).card + (B.filter q).card + (B.filter r).card := by
  classical
  have hsub : A ∩ B ⊆
      (((A ∩ B).filter fun x => ¬ (p x ∨ q x ∨ r x)) ∪ B.filter p ∪
        B.filter q) ∪ B.filter r := by
    intro x hx
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter]
    tauto
  have h₀ := Finset.card_le_card hsub
  have h₁ := Finset.card_union_le
    (((A ∩ B).filter fun x => ¬ (p x ∨ q x ∨ r x)) ∪ B.filter p ∪
      B.filter q) (B.filter r)
  have h₂ := Finset.card_union_le
    (((A ∩ B).filter fun x => ¬ (p x ∨ q x ∨ r x)) ∪ B.filter p) (B.filter q)
  have h₃ := Finset.card_union_le
    ((A ∩ B).filter fun x => ¬ (p x ∨ q x ∨ r x)) (B.filter p)
  omega

end Boundary

end PlanarHalving

end OAI
