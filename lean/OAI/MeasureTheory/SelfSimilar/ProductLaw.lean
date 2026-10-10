import OAI.MeasureTheory.SelfSimilar.FairPairs

namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def weight (p : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, p i (x i)

omit [Fintype α] [DecidableEq ι] in
theorem weight_nonneg (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → α) :
    0 ≤ weight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

theorem weight_sum (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ x, weight p x = 1 := by
  simpa only [weight, hp, Finset.prod_const_one] using (Fintype.prod_sum p).symm

theorem moment (p f : ι → α → ℝ) (s : Finset ι)
    (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ x, weight p x * ∏ i ∈ s, f i (x i)) = ∏ i ∈ s, ∑ a, p i a * f i a := by
  classical
  have h := (Fintype.prod_sum (fun i a => p i a * if i ∈ s then f i a else 1)).symm
  have hleft : ∀ x : ι → α, (∏ i, p i (x i) * if i ∈ s then f i (x i) else 1) =
      weight p x * ∏ i ∈ s, f i (x i) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
    rfl
  have hright : ∀ i, (∑ a, p i a * if i ∈ s then f i a else 1) =
      if i ∈ s then ∑ a, p i a * f i a else 1 := by
    intro i
    split_ifs <;> simp_all only [mul_one]
  simpa only [hleft, hright, Finset.prod_ite_mem_eq] using h

theorem coordinate_event (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1) (i : ι) :
    (∑ x, if E i (x i) then weight p x else 0) = ∑ a, if E i a then p i a else 0 := by
  classical
  simpa only [Finset.prod_singleton, mul_ite, mul_one, mul_zero] using
    moment p (fun j a => if E j a then 1 else 0) {i} hp

theorem two_coordinate_events (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1)
    (i j : ι) (hij : i ≠ j) :
    (∑ x, if E i (x i) ∧ E j (x j) then weight p x else 0) =
      (∑ x, if E i (x i) then weight p x else 0) *
      (∑ x, if E j (x j) then weight p x else 0) := by
  classical
  rw [coordinate_event p E hp i, coordinate_event p E hp j]
  have h := moment p (fun l a => if E l a then 1 else 0) {i,j} hp
  simp only [Finset.prod_pair hij] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  · simp only [mul_ite, mul_one, mul_zero]

theorem entropy (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    FiniteEntropy.entropy Finset.univ (weight p) =
      ∑ i, FiniteEntropy.entropy Finset.univ (p i) := by
  classical
  have hm : ∀ i, (∑ x, weight p x * Real.log (p i (x i))) = ∑ a, p i a * Real.log (p i a) := by
    intro i
    simpa only [Finset.prod_singleton] using moment p (fun j a => Real.log (p j a)) {i} hp
  have hn : ∀ x : ι → α, Real.negMulLog (weight p x) =
      -(∑ i, weight p x * Real.log (p i (x i))) := by
    intro x
    by_cases hx : weight p x = 0
    · simp only [hx, Real.negMulLog_zero, zero_mul, Finset.sum_const_zero, neg_zero]
    · change -(weight p x) * Real.log (weight p x) = _
      have hfac : ∀ i ∈ (Finset.univ : Finset ι), p i (x i) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hx)
      rw [weight, Real.log_prod hfac, Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib]
  simp only [FiniteEntropy.entropy, hn, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [hm, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

variable {β : Type uβ} [DecidableEq β]

noncomputable def cellMass (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) : ℝ :=
  ∑ a, if g i a = c i then p i a else 0

noncomputable def conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) (a : α) : ℝ :=
  (if g i a = c i then p i a else 0) / cellMass p g c i

theorem mass_cells (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) :
    FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c =
      ∏ i, cellMass p g c i := by
  classical
  have hh := (Fintype.prod_sum (fun i a => if g i a = c i then p i a else 0)).symm
  simpa only [Fintype.prod_ite_zero, ← funext_iff, FiniteEntropy.mass,
    Finset.sum_filter, weight, cellMass] using hh

theorem weight_conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (x : ι → α) :
    weight (conditional p g c) x =
      if (fun i => g i (x i)) = c then weight p x /
        FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0 := by
  classical
  rw [mass_cells]
  simp only [weight, conditional, Finset.prod_div_distrib, Fintype.prod_ite_zero, ← funext_iff]
  split_ifs <;> simp_all

theorem conditional_sum (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hc : FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c ≠ 0) (i : ι) :
    ∑ a, conditional p g c i a = 1 := by
  rw [mass_cells] at hc
  have hi : cellMass p g c i ≠ 0 := (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
  simp only [conditional, ← Finset.sum_div]
  exact div_self hi

omit [Fintype ι] [DecidableEq ι] in
theorem conditional_nonneg (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hp : ∀ i a, 0 ≤ p i a) (i : ι) (a : α) : 0 ≤ conditional p g c i a := by
  have hn : ∀ j b, 0 ≤ (if g j b = c j then p j b else 0) := by
    intro j b
    split_ifs <;> first | exact hp j b | exact le_rfl
  exact div_nonneg (hn i a) (Finset.sum_nonneg (fun b _ => hn i b))

theorem conditional_event (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (E : (ι → α) → Prop) [DecidablePred E] :
    (∑ x ∈ Finset.univ.filter (fun x => (fun i => g i (x i)) = c),
      if E x then weight p x / FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0) =
    ∑ x, if E x then weight (conditional p g c) x else 0 := by
  classical
  simp only [Finset.sum_filter, weight_conditional]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

theorem observableEntropy_conditional {γ : Type uγ} [DecidableEq γ]
    (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (f : (ι → α) → γ) :
    FiniteEntropy.observableEntropy
      (Finset.univ.filter (fun x => (fun i => g i (x i)) = c))
      (fun x => weight p x / FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c) f =
      FiniteEntropy.observableEntropy Finset.univ (weight (conditional p g c)) f := by
  classical
  rw [← FiniteEntropy.observableEntropy_subset (s := Finset.univ.filter (fun x => (fun i => g i (x i)) = c))
    (weight (conditional p g c)) f (Finset.filter_subset _ _) (by
      intro x _ hx
      rw [weight_conditional, ite_eq_right]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx)]
  apply FiniteEntropy.observableEntropy_congr _ _ _ _ _ _ (fun _ _ => rfl)
  intro x hx
  rw [weight_conditional, ite_eq_left (Finset.mem_filter.mp hx).2]

theorem observable_entropy [Nonempty α] [Nonempty β]
    (p : α → ℝ) (g : α → β) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      Fintype.card ι * FiniteEntropy.observableEntropy Finset.univ p g := by
  classical
  let B : Finset β := Finset.univ.image g
  let g' : α → B := fun a => ⟨g a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have : Nonempty B := ⟨g' (Classical.choice inferInstance)⟩
  have hg : FiniteEntropy.observableEntropy Finset.univ p g =
      FiniteEntropy.observableEntropy Finset.univ p g' := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _ (fun a _ => hp a)
    intro a _ b _
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hG : FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _
      (fun x _ => weight_nonneg _ (fun _ a => hp a) x)
    intro x _ y _
    constructor
    · intro h
      funext i
      exact Subtype.ext (congrFun h i)
    · intro h
      funext i
      exact congrArg Subtype.val (congrFun h i)
  rw [hg, hG, FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ _ _
    (fun _ _ => Finset.mem_univ _)]
  have hm : FiniteEntropy.mass Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) =
      weight (fun _ : ι => FiniteEntropy.mass Finset.univ p g') := by
    funext c
    rw [mass_cells]
    simp only [weight, cellMass, FiniteEntropy.mass, Finset.sum_filter]
  have hpB : ∑ b : B, FiniteEntropy.mass Finset.univ p g' b = 1 := by
    rw [← hp1, ← FiniteEntropy.mass_sum Finset.univ p g']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    exact FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ hb
  rw [hm, entropy _ (fun _ => hpB)]
  rw [FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ p g'
    (fun _ _ => Finset.mem_univ _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ProductLaw

end EntropyRateDimension
end

end OAI
