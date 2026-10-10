import OAI.Combinatorics.ParityLifts.WeightedDual

namespace OAI

namespace ParityWL

open scoped BigOperators

section Masses

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

noncomputable def WeightedWitness.mass (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) : Bit :=
  ∑ x ∈ Y, if a x = u then w.vertex x else 0

lemma WeightedWitness.coordinate_mass (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y : Finset W) :
    w.mass Y u = ∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · have h := w.coordinate x ⟨v, hx ▸ huv⟩
    simpa [hx] using h.symm
  · simp [hx]

lemma WeightedWitness.mass_univ_adj (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) :
    w.mass Finset.univ u = w.mass Finset.univ v := by
  rw [w.coordinate_mass huv, w.coordinate_mass huv.symm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [and_comm, w.symmetric]

lemma WeightedWitness.mass_union (w : WeightedWitness T F a b)
    (X Y : Finset W) (h : Disjoint X Y) (u : A) :
    w.mass (X ∪ Y) u = w.mass X u + w.mass Y u :=
  Finset.sum_union h

lemma WeightedWitness.mass_eq_zero (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (h : ∀ x ∈ Y, a x ≠ u) : w.mass Y u = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp [h x hx]

lemma WeightedWitness.mass_univ_reachable (w : WeightedWitness T F a b)
    {u v : A} (h : T.Reachable u v) :
    w.mass Finset.univ u = w.mass Finset.univ v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons x y z h p ih => exact (w.mass_univ_adj h).trans ih

/-- Two types absent from the boundary of a separated vertex set have equal mass. -/
lemma WeightedWitness.mass_separator (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hu : ∀ x ∈ S, a x ≠ u) (hv : ∀ x ∈ S, a x ≠ v) :
    w.mass Y u = w.mass Y v := by
  have restrict : ∀ (q r : A), T.Adj q r → (∀ x ∈ S, a x ≠ r) →
      w.mass Y q = ∑ x ∈ Y, ∑ y ∈ Y,
        if a x = q ∧ a y = r then w.edge x y else 0 := by
    intro q r hqr hr
    rw [w.coordinate_mass hqr]
    apply Finset.sum_congr rfl
    intro x hx
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_cases hy' : a y = r
    · have hn : ¬ F.Adj x y := fun hxy => hr y (hboundary x hx y hxy hy) hy'
      simp [w.supported x y hn]
    · simp [hy']
  rw [restrict u v huv hv, restrict v u huv.symm hu, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [and_comm, w.symmetric]

end Masses

section TemplateMass

open scoped Classical

lemma starParity_value {t : ℕ} (ht : 0 < t) (u : TemplateVertex t) :
    starParity t u = if u = .inl ⟨0, ht⟩ then 1 else 0 := by
  have hi : ∀ i : Fin t, i.val = 0 ↔ i = ⟨0, ht⟩ := by
    intro i
    exact (Fin.ext_iff (a := i) (b := ⟨0, ht⟩)).symm
  simp [starParity, hi]

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

lemma WeightedWitness.main_mass (w : WeightedWitness (template t) F a (starParity t))
    (ht : 0 < t) (i : Fin t) : w.mass Finset.univ (.inl i) = 1 := by
  have hz : w.mass Finset.univ (.inl ⟨0, ht⟩) = 1 := by
    calc
      _ = ∑ x, w.vertex x * starParity t (a x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [starParity_value ht]
        by_cases h : a x = .inl ⟨0, ht⟩ <;> simp [h]
      _ = 1 := w.odd
  by_cases hi : i = ⟨0, ht⟩
  · simpa [hi] using hz
  · have := w.mass_univ_adj (u := .inl i) (v := .inl ⟨0, ht⟩) hi
    exact this.trans hz

lemma WeightedWitness.template_mass (w : WeightedWitness (template t) F a (starParity t))
    (ht : 0 < t) (u : TemplateVertex t) : w.mass Finset.univ u = 1 := by
  cases u with
  | inl i => exact w.main_mass ht i
  | inr q =>
    exact (w.mass_univ_adj (u := .inr q) (v := .inl q.1.1.1.1) (Or.inl rfl)).trans
      (w.main_mass ht q.1.1.1.1)

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

noncomputable def WeightedWitness.testMass (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit) : Bit :=
  ∑ x ∈ Y, if a x = u then w.vertex x * p x else 0

lemma WeightedWitness.testMass_add (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p q : W → Bit) :
    w.testMass Y u (p + q) = w.testMass Y u p + w.testMass Y u q := by
  unfold WeightedWitness.testMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : a x = u <;> simp [h, mul_add]

lemma WeightedWitness.testMass_one (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) : w.testMass Y u (fun _ => 1) = w.mass Y u := by
  simp [WeightedWitness.testMass, WeightedWitness.mass]

lemma WeightedWitness.testMass_zero (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit)
    (h : ∀ x ∈ Y, a x = u → p x = 0) : w.testMass Y u p = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases ha : a x = u <;> simp [ha, h x hx]

lemma WeightedWitness.testMass_coordinate (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y : Finset W) (p : W → Bit) :
    w.testMass Y u p = ∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · have h := w.coordinate x ⟨v, hx ▸ huv⟩
    simp only [hx, ↓reduceIte, true_and]
    rw [← h, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : a y = v <;> simp [hy]
  · simp [hx]

/-- Transfer of a tested type mass across a separator. The test vanishes on its
boundary representatives; target-type vertices are absent from the boundary.
This includes every boundary edge rather than dropping such edges. -/
lemma WeightedWitness.testMass_transfer (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W) (p q : W → Bit)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hv : ∀ x ∈ S, a x ≠ v)
    (hp : ∀ x ∈ S, a x = u → p x = 0)
    (hcompat : ∀ x y, F.Adj x y → a x = u → a y = v → p x = q y) :
    w.testMass Y u p = w.testMass Y v q := by
  rw [w.testMass_coordinate huv]
  have hr : (∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0) =
      ∑ x ∈ Y, ∑ y ∈ Y,
        if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_cases hxy : F.Adj x y
    · have hn := hv y (hboundary x hx y hxy hy)
      simp [hn]
    · simp [w.supported x y hxy]
  rw [hr, Finset.sum_comm]
  have hr' : (∑ y ∈ Y, ∑ x ∈ Y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0) =
      ∑ y ∈ Y, ∑ x,
        if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    by_cases hxy : F.Adj y x
    · by_cases ha : a x = u
      · simp [hp x (hboundary y hy x hxy hx) ha]
      · simp [ha]
    · have hn : ¬ F.Adj x y := fun h => hxy h.symm
      simp [w.supported x y hn]
  rw [hr', w.testMass_coordinate huv.symm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · by_cases hy : a y = v
    · simp only [hx, hy, and_self, ↓reduceIte]
      by_cases hxy : F.Adj x y
      · rw [w.symmetric, hcompat x y hxy hx hy]
      · rw [w.supported x y hxy, ← w.symmetric x y, w.supported x y hxy]
        simp
    · simp [hy]
  · simp [hx]

lemma WeightedWitness.testMass_complement (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit) :
    w.testMass Y u p + w.testMass Y u (fun x => 1 + p x) = w.mass Y u := by
  rw [← w.testMass_add]
  have he : p + (fun x => 1 + p x) = fun _ => (1 : Bit) := by
    funext x
    change p x + (1 + p x) = 1
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  rw [he, w.testMass_one]

/-- The global mismatch identity, including arbitrary zero representative weights. -/
lemma WeightedWitness.global_mismatch (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (p q : W → Bit)
    (hc : ∀ x y, F.Adj x y → a x = u → a y = v → p x + q y = 1) :
    w.testMass Finset.univ u p + w.testMass Finset.univ v q =
      w.mass Finset.univ u := by
  have ht := w.testMass_transfer huv.symm Finset.univ ∅ q (fun x => 1 + p x)
    (by simp) (by simp) (by simp) (by
      intro x y hxy hx hy
      have he := hc y x hxy.symm hy hx
      have hh := congrArg (fun e => p y + e) he
      simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_comm, add_zero] using hh)
  rw [ht, w.testMass_complement]

end BoundaryTests

end ParityWL

end OAI
