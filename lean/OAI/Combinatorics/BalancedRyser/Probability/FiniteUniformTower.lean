import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformFibers

namespace OAI

namespace Balanced.FiniteUniformTower

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def fiberMean {Ω Y : Type*} [Fintype Ω] (expose : Ω → Y)
    (g : Ω → ℝ) (z : Y) : ℝ :=
  (∑ x : {x // expose x = z}, g x) / Fintype.card {x // expose x = z}

def average {Ω : Type*} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (∑ x, g x) / Fintype.card Ω

theorem sum_fiberMean {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (g : Ω → ℝ) :
    (∑ x, fiberMean expose g (expose x)) = ∑ x, g x := by
  classical
  rw [← Fintype.sum_fiberwise expose (fun x => fiberMean expose g (expose x)),
    ← Fintype.sum_fiberwise expose g]
  apply Finset.sum_congr rfl
  intro z _
  have hval (x : {x // expose x = z}) :
      fiberMean expose g (expose x.1) = fiberMean expose g z := by rw [x.2]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  cases isEmpty_or_nonempty {x // expose x = z} with
  | inl h =>
    let := h
    simp [fiberMean]
  | inr h =>
    let := h
    have hc : (Fintype.card {x // expose x = z} : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold fiberMean
    field_simp

theorem average_fiberMean {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (g : Ω → ℝ) :
    average (fun x => fiberMean expose g (expose x)) = average g := by
  unfold average
  rw [sum_fiberMean]

theorem fiberMean_mul_exposed {Ω Y : Type*} [Fintype Ω]
    (expose : Ω → Y) (w g : Ω → ℝ)
    (hw : ∀ x y, expose x = expose y → w x = w y) (x : Ω) :
    fiberMean expose (fun y => w y * g y) (expose x) =
      w x * fiberMean expose g (expose x) := by
  unfold fiberMean
  have heq : (∑ y : {y // expose y = expose x}, w y * g y) =
      w x * ∑ y : {y // expose y = expose x}, g y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hw y x y.2]
  rw [heq]
  ring

theorem average_mul_fiberMean {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (w g : Ω → ℝ)
    (hw : ∀ x y, expose x = expose y → w x = w y) :
    average (fun x => w x * fiberMean expose g (expose x)) =
      average (fun x => w x * g x) := by
  have h := average_fiberMean expose (fun x => w x * g x)
  simpa only [fiberMean_mul_exposed expose w g hw] using h

theorem average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x))
    (Nat.cast_nonneg _)

theorem average_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (g : Ω → ℝ) :
    average (fun x => c * g x) = c * average g := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem average_event_inter_le {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (A B : Ω → Prop) (c : ℝ)
    (hA : ∀ x y, expose x = expose y → (A x ↔ A y))
    (hB : ∀ x, A x → fiberMean expose (fun y => if B y then 1 else 0)
      (expose x) ≤ c) :
    average (fun x => if A x ∧ B x then 1 else 0) ≤
      c * average (fun x => if A x then 1 else 0) := by
  let w : Ω → ℝ := fun x => if A x then 1 else 0
  let g : Ω → ℝ := fun x => if B x then 1 else 0
  have hw : ∀ x y, expose x = expose y → w x = w y := by
    intro x y hxy
    simp only [w, hA x y hxy]
  have hprod : (fun x => if A x ∧ B x then (1 : ℝ) else 0) =
      (fun x => w x * g x) := by
    funext x
    simp only [w, g]
    split_ifs <;> simp_all
  rw [hprod, ← average_mul_fiberMean expose w g hw]
  calc
    average (fun x => w x * fiberMean expose g (expose x)) ≤
        average (fun x => c * w x) := average_mono (by
      intro x
      by_cases hx : A x
      · simpa only [w, hx, ite_true, one_mul, mul_one, g] using hB x hx
      · simp only [w, hx, ite_false, zero_mul, mul_zero, le_refl])
    _ = c * average w := average_const_mul c w

theorem probability_eq_average {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {x | E x}).toReal =
      average (fun x => if E x then 1 else 0) :=
  FiniteUniformFibers.probability_eq_sum E

theorem probability_event_inter_le {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    [Nonempty Ω] (expose : Ω → Y) (A B : Ω → Prop) (c : ℝ)
    (hA : ∀ x y, expose x = expose y → (A x ↔ A y))
    (hB : ∀ x, A x → fiberMean expose (fun y => if B y then 1 else 0)
      (expose x) ≤ c) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {x | A x ∧ B x}).toReal ≤
      c * ((PMF.uniformOfFintype Ω).toOuterMeasure {x | A x}).toReal := by
  simp only [probability_eq_average]
  convert average_event_inter_le expose A B c hA hB using 1
  congr 1
  funext x
  split_ifs <;> rfl

theorem observed_supported {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]
    (expose : Ω → Y) (x : Ω) :
    ∃ y ∈ {y | expose y = expose x}, y ∈ (PMF.uniformOfFintype Ω).support := by
  exact ⟨x, rfl, by simp⟩

theorem filtered_probability_eq_fiberMean {Ω Y : Type*}
    [Fintype Ω] [Nonempty Ω] (expose : Ω → Y) (x : Ω) (B : Ω → Prop) :
    (((PMF.uniformOfFintype Ω).filter {y | expose y = expose x}
      (observed_supported expose x)).toOuterMeasure {y | B y}).toReal =
        fiberMean expose (fun y => if B y then 1 else 0) (expose x) := by
  let : Nonempty ({y | expose y = expose x} : Set Ω) := ⟨⟨x, rfl⟩⟩
  rw [uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply]
  simp only [Set.preimage_ofPred_eq]
  rw [FiniteUniformFibers.probability_eq_sum]
  rfl

theorem probability_event_inter_le_of_filtered {Ω Y : Type*}
    [Fintype Ω] [Fintype Y] [Nonempty Ω]
    (expose : Ω → Y) (A B : Ω → Prop) (c : ℝ)
    (hA : ∀ x y, expose x = expose y → (A x ↔ A y))
    (hB : ∀ x, A x →
      (((PMF.uniformOfFintype Ω).filter {y | expose y = expose x}
        (observed_supported expose x)).toOuterMeasure {y | B y}).toReal ≤ c) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {x | A x ∧ B x}).toReal ≤
      c * ((PMF.uniformOfFintype Ω).toOuterMeasure {x | A x}).toReal := by
  apply probability_event_inter_le expose A B c hA
  intro x hx
  rw [← filtered_probability_eq_fiberMean]
  exact hB x hx

end
end Balanced.FiniteUniformTower

end OAI
