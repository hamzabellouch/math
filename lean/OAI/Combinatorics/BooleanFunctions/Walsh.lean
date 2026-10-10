import Mathlib

namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

abbrev Cube (ι : Type*) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def character {ι : Type*} (s : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ s, sign (x i)

def fourierCoeff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (s : Finset ι) : ℝ := by
  classical
  exact average (fun x => f x * character s x)

def fourierDegree {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0)).sup Finset.card

def IsBoolean {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = -1 ∨ f x = 1

def Nonconstant {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x y, f x ≠ f y

def singletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, fourierCoeff f {i}

def absoluteSingletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, |fourierCoeff f {i}|

def SignedViolations : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ Nonconstant f ∧ C * Real.sqrt (fourierDegree f) < singletonSum f

def AbsoluteRatios : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ 0 < fourierDegree f ∧
      r = absoluteSingletonSum f / Real.sqrt (fourierDegree f)}



/-! ## Finite Walsh calculus -/

@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_xor (a b : Bool) : sign (Bool.xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

theorem sign_injective : Function.Injective sign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | norm_num [sign] at h

@[simp] theorem average_zero {α : Type*} [Fintype α] :
    average (fun _ : α => 0) = 0 := by simp [average]

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := by
  simp [average, ← Finset.sum_mul, mul_assoc]

theorem average_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [mul_comm c, average_mul_const]

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun x _ => h x)

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, Fintype.card_congr e, e.sum_comp]

@[simp] theorem character_empty {ι : Type*} (x : Cube ι) : character ∅ x = 1 := by
  simp [character]

@[simp] theorem character_singleton {ι : Type*} (i : ι) (x : Cube ι) :
    character {i} x = sign (x i) := by simp [character]

theorem character_ne_zero {ι : Type*} (s : Finset ι) (x : Cube ι) :
    character s x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => sign_ne_zero (x i)

@[simp] theorem character_sq {ι : Type*} (s : Finset ι) (x : Cube ι) :
    character s x ^ 2 = 1 := by
  simp [character, ← Finset.prod_pow]

def reflection {ι : Type*} (a : Cube ι) : Cube ι ≃ Cube ι where
  toFun x i := Bool.xor (a i) (x i)
  invFun x i := Bool.xor (a i) (x i)
  left_inv x := by
    funext i
    change Bool.xor (a i) (Bool.xor (a i) (x i)) = x i
    cases a i <;> cases x i <;> rfl
  right_inv x := by
    funext i
    change Bool.xor (a i) (Bool.xor (a i) (x i)) = x i
    cases a i <;> cases x i <;> rfl

@[simp] theorem reflection_involutive {ι : Type*} (a x : Cube ι) :
    reflection a (reflection a x) = x := (reflection a).left_inv x

theorem character_reflection {ι : Type*} (a x : Cube ι) (s : Finset ι) :
    character s (reflection a x) = character s a * character s x := by
  simp [character, reflection, sign_xor, Finset.prod_mul_distrib]

theorem fourierCoeff_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (a : Cube ι) (s : Finset ι) :
    fourierCoeff (fun x => f (reflection a x)) s = character s a * fourierCoeff f s := by
  classical
  unfold fourierCoeff
  rw [← average_equiv (reflection a) (fun x => f (reflection a x) * character s x)]
  simp only [reflection_involutive, character_reflection]
  calc
    _ = average (fun x => character s a * (f x * character s x)) := by
      congr 1
      funext x
      ring
    _ = _ := average_const_mul _ _

theorem fourierDegree_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (a : Cube ι) :
    fourierDegree (fun x => f (reflection a x)) = fourierDegree f := by
  classical
  simp [fourierDegree, fourierCoeff_reflection, character_ne_zero]

def positiveMask {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : Cube ι := by
  classical
  exact fun i => decide (fourierCoeff f {i} < 0)

theorem fourierCoeff_positive_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (i : ι) :
    fourierCoeff (fun x => f (reflection (positiveMask f) x)) {i} =
      |fourierCoeff f {i}| := by
  classical
  rw [fourierCoeff_reflection, character_singleton]
  by_cases h : fourierCoeff f {i} < 0
  · simp [positiveMask, sign, h, abs_of_neg h]
  · simp [positiveMask, sign, h, abs_of_nonneg (le_of_not_gt h)]

theorem singletonSum_positive_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) :
    singletonSum (fun x => f (reflection (positiveMask f) x)) = absoluteSingletonSum f := by
  simp [singletonSum, absoluteSingletonSum, fourierCoeff_positive_reflection]

theorem isBoolean_reflection {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι)
    (hf : IsBoolean f) : IsBoolean (fun x => f (reflection a x)) := fun x => hf (reflection a x)

theorem nonconstant_reflection {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι)
    (hf : Nonconstant f) : Nonconstant (fun x => f (reflection a x)) := by
  obtain ⟨x, y, h⟩ := hf
  exact ⟨reflection a x, reflection a y, by simpa using h⟩

theorem singletonSum_le_absoluteSingletonSum {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) : singletonSum f ≤ absoluteSingletonSum f :=
  Finset.sum_le_sum fun i _ => le_abs_self (fourierCoeff f {i})

theorem character_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : Cube ι) :
    (∑ s : Finset ι, character s x * character s y) =
      if x = y then (Fintype.card (Cube ι) : ℝ) else 0 := by
  classical
  calc
    _ = ∏ i : ι, (1 + sign (x i) * sign (y i)) := by
      rw [Finset.prod_one_add, Finset.powerset_univ]
      simp [character, Finset.prod_mul_distrib]
    _ = _ := by
      by_cases h : x = y
      · subst y
        simp only [↓reduceIte]
        have hsign (i : ι) : (1 : ℝ) + sign (x i) * sign (x i) = 2 := by
          nlinarith [sign_sq (x i)]
        simp [hsign, Fintype.card_bool]
      · simp only [h, ↓reduceIte]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          simpa only [funext_iff, not_forall] using h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hx : x i <;> cases hy : y i <;> simp_all [sign]

theorem fourier_inversion {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (x : Cube ι) :
    f x = ∑ s : Finset ι, fourierCoeff f s * character s x := by
  classical
  have hn : (Fintype.card (Cube ι) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  symm
  calc
    _ = (Fintype.card (Cube ι) : ℝ)⁻¹ *
        ∑ y : Cube ι, f y * ∑ s : Finset ι, character s y * character s x := by
      simp only [fourierCoeff, average, mul_assoc, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (Fintype.card (Cube ι) : ℝ)⁻¹ *
        ∑ y : Cube ι, f y * (if y = x then (Fintype.card (Cube ι) : ℝ) else 0) := by
      simp only [character_kernel]
    _ = f x := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      field_simp

theorem fourierCoeff_eq_zero_of_degree_lt {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) {s : Finset ι} (h : fourierDegree f < s.card) :
    fourierCoeff f s = 0 := by
  classical
  by_contra hc
  have hs := Finset.le_sup (s := Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0))
    (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  exact (not_le_of_gt h) hs

theorem fourierDegree_le_iff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (d : ℕ) :
    fourierDegree f ≤ d ↔ ∀ s : Finset ι, d < s.card → fourierCoeff f s = 0 := by
  classical
  constructor
  · intro h s hs
    exact fourierCoeff_eq_zero_of_degree_lt f (lt_of_le_of_lt h hs)
  · intro h
    apply Finset.sup_le
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact le_of_not_gt (fun hd => hs (h s hd))

theorem positive_degree_of_nonconstant {ι : Type*} [Fintype ι] (f : Cube ι → ℝ)
    (hf : Nonconstant f) : 0 < fourierDegree f := by
  classical
  by_contra h
  have hd : fourierDegree f = 0 := Nat.eq_zero_of_not_pos h
  have hc (x : Cube ι) : f x = fourierCoeff f ∅ := by
    rw [fourier_inversion f x]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro s _ hs
      have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      rw [fourierCoeff_eq_zero_of_degree_lt f (by simpa [hd] using hpos), zero_mul]
    · simp
  obtain ⟨x, y, hxy⟩ := hf
  exact hxy ((hc x).trans (hc y).symm)

/-- Coordinate reflection exactly identifies the signed and absolute linear sums,
without changing the ordinary real Fourier degree or Boolean/nonconstant status. -/
theorem coordinate_reflection {ι : Type*} [Fintype ι] (f : Cube ι → ℝ)
    (hf : IsBoolean f) (hn : Nonconstant f) :
    ∃ g : Cube ι → ℝ, IsBoolean g ∧ Nonconstant g ∧
      fourierDegree g = fourierDegree f ∧ singletonSum g = absoluteSingletonSum f := by
  exact ⟨fun x => f (reflection (positiveMask f) x), isBoolean_reflection _ _ hf,
    nonconstant_reflection _ _ hn, fourierDegree_reflection _ _,
    singletonSum_positive_reflection _⟩

theorem absolute_unbounded_of_signed (h : SignedViolations) : ¬ BddAbove AbsoluteRatios := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, f, hf, hnon, hlt⟩ := h (max M 0 + 1) (by positivity)
  obtain ⟨g, hgb, hgn, hdeg, hsum⟩ := coordinate_reflection f hf hnon
  have hd := positive_degree_of_nonconstant g hgn
  have hs : 0 < Real.sqrt (fourierDegree g : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hm : absoluteSingletonSum g / Real.sqrt (fourierDegree g) ≤ M :=
    hM ⟨n, hn, g, hgb, hd, rfl⟩
  have hcompare : singletonSum f ≤ absoluteSingletonSum g :=
    calc singletonSum f ≤ absoluteSingletonSum f := singletonSum_le_absoluteSingletonSum f
      _ = singletonSum g := hsum.symm
      _ ≤ absoluteSingletonSum g := singletonSum_le_absoluteSingletonSum g
  have hlt' : max M 0 + 1 < absoluteSingletonSum g / Real.sqrt (fourierDegree g) := by
    apply (lt_div_iff₀ hs).mpr
    rw [hdeg]
    exact hlt.trans_le hcompare
  have := le_max_left M 0
  linarith


/-! ### Degree calculus for finite observations -/

def DependsOn {ι : Type*} (s : Finset ι) (f : Cube ι → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem fourierCoeff_add {ι : Type*} [Fintype ι] (f g : Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => f x + g x) s = fourierCoeff f s + fourierCoeff g s := by
  simp only [fourierCoeff, add_mul, average_add]

theorem fourierCoeff_const_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => c * f x) s = c * fourierCoeff f s := by
  simp only [fourierCoeff, mul_assoc, average_const_mul]

theorem fourierCoeff_sum {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => ∑ j ∈ t, f j x) s = ∑ j ∈ t, fourierCoeff (f j) s := by
  simp only [fourierCoeff, Finset.sum_mul, average_sum]

theorem fourierDegree_sum_le {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (d : ℕ)
    (h : ∀ j ∈ t, fourierDegree (f j) ≤ d) :
    fourierDegree (fun x => ∑ j ∈ t, f j x) ≤ d := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_sum]
  exact Finset.sum_eq_zero fun j hj =>
    fourierCoeff_eq_zero_of_degree_lt _ (lt_of_le_of_lt (h j hj) hs)

theorem fourierDegree_const_mul_le {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) : fourierDegree (fun x => c * f x) ≤ fourierDegree f := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_const_mul, fourierCoeff_eq_zero_of_degree_lt _ hs, mul_zero]

theorem fourierCoeff_eq_zero_of_not_subset {ι : Type*} [Fintype ι]
    {f : Cube ι → ℝ} {s t : Finset ι} (hf : DependsOn t f) (hst : ¬ s ⊆ t) :
    fourierCoeff f s = 0 := by
  classical
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hst
  let a : Cube ι := fun j => decide (j = i)
  have hfa : (fun x => f (reflection a x)) = f := by
    funext x
    apply hf
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hit hj
    simp [reflection, a, hji]
  have hca : character s a = -1 := by
    simp [character, a, sign, Finset.prod_ite_eq', hi]
  have h := fourierCoeff_reflection f a s
  rw [hfa, hca] at h
  linarith

theorem fourierDegree_le_card_of_dependsOn {ι : Type*} [Fintype ι]
    {f : Cube ι → ℝ} {t : Finset ι} (hf : DependsOn t f) : fourierDegree f ≤ t.card := by
  rw [fourierDegree_le_iff]
  intro s hs
  apply fourierCoeff_eq_zero_of_not_subset hf
  exact fun hst => (not_le_of_gt hs) (Finset.card_le_card hst)

theorem character_dependsOn {ι : Type*} (s : Finset ι) : DependsOn s (character s) := by
  intro x y h
  exact Finset.prod_congr rfl fun i hi => congrArg sign (h i hi)

theorem dependsOn_mul {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    {f g : Cube ι → ℝ} (hf : DependsOn s f) (hg : DependsOn t g) :
    DependsOn (s ∪ t) (fun x => f x * g x) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem fourierDegree_mul_le {ι : Type*} [Fintype ι] (f g : Cube ι → ℝ) :
    fourierDegree (fun x => f x * g x) ≤ fourierDegree f + fourierDegree g := by
  classical
  let sf : Finset (Finset ι) := Finset.univ.filter (fun s => fourierCoeff f s ≠ 0)
  let sg : Finset (Finset ι) := Finset.univ.filter (fun s => fourierCoeff g s ≠ 0)
  have hexp (h : Cube ι → ℝ) (x : Cube ι) :
      h x = ∑ s ∈ Finset.univ.filter (fun s => fourierCoeff h s ≠ 0),
        fourierCoeff h s * character s x := by
    rw [fourier_inversion h x]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hz : fourierCoeff h s = 0 := by simpa [Finset.mem_filter, hs] using hnot
    simp [hz]
  have heq : (fun x => f x * g x) = fun x =>
      ∑ s ∈ sf, ∑ t ∈ sg,
        (fourierCoeff f s * fourierCoeff g t) * (character s x * character t x) := by
    funext x
    rw [hexp f x, hexp g x]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, sf, sg]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [heq]
  apply fourierDegree_sum_le
  intro s hs
  apply fourierDegree_sum_le
  intro t ht
  apply (fourierDegree_const_mul_le _ _).trans
  apply (fourierDegree_le_card_of_dependsOn
    (dependsOn_mul (character_dependsOn s) (character_dependsOn t))).trans
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (Finset.le_sup (f := Finset.card) hs)
    (Finset.le_sup (f := Finset.card) ht)


theorem fourierDegree_const {ι : Type*} [Fintype ι] (c : ℝ) :
    fourierDegree (fun _ : Cube ι => c) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact fourierDegree_le_card_of_dependsOn (t := ∅) (by intro x y _; rfl)

theorem fourierDegree_prod_le {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (f : κ → Cube ι → ℝ) :
    fourierDegree (fun x => ∏ j ∈ s, f j x) ≤ ∑ j ∈ s, fourierDegree (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierDegree_const]
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (fourierDegree_mul_le _ _).trans (Nat.add_le_add_left ih _)

end SquareRootDegree

end

end OAI
