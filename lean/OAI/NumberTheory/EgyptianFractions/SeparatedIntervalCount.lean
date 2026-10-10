import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
open Classical
namespace Problem337

/-- Packing bound for integer-indexed values separated at a positive linear rate. -/
theorem separated_interval_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam u v : ℝ) (hlam : 0 < lam) (huv : u ≤ v)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, u ≤ f i ∧ f i ≤ v) :
    (s.card : ℝ) ≤ (v - u) / lam + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.min'_le b hb
    have hsub : s ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
    have hcard : (s.card : ℝ) ≤ (b : ℝ) - a + 1 := by
      calc
        (s.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = (b : ℝ) - a + 1 := by
          have h := Int.card_Icc_of_le a b (by omega)
          exact_mod_cast (show ((Finset.Icc a b).card : ℤ) = b - a + 1 by omega)
    have hg := hsep a ha b hb hab
    have ha' := (hrange a ha).1
    have hb' := (hrange b hb).2
    have hdiff : (b : ℝ) - a ≤ (v - u) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The number of separated samples near integers is controlled by the number
of integer centers and the packing bound in each short interval. -/
theorem separated_near_integer_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, L ≤ f i ∧ f i ≤ U) :
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  let centers : Finset ℤ := Finset.Icc ⌈L - β⌉ ⌊U + β⌋
  let fiber (q : ℤ) : Finset ℤ := s.filter fun i => |f i - q| ≤ β
  have hcover : (s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β) ⊆ centers.biUnion fiber := by
    intro i hi
    obtain ⟨his, q, hq⟩ := Finset.mem_filter.mp hi
    have hq' := abs_le.mp hq
    have hi' := hrange i his
    apply Finset.mem_biUnion.mpr
    refine ⟨q, ?_, Finset.mem_filter.mpr ⟨his, hq⟩⟩
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      linarith
    · apply Int.le_floor.mpr
      linarith
  have hfiber (q : ℤ) : ((fiber q).card : ℝ) ≤ 2 * β / lam + 1 := by
    have h := separated_interval_card (fiber q) f lam ((q : ℝ) - β) ((q : ℝ) + β)
      hlam (by linarith)
      (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
      (fun i hi => by
        have h := abs_le.mp (Finset.mem_filter.mp hi).2
        constructor <;> linarith)
    convert h using 1; ring
  have hcenters : (centers.card : ℝ) ≤ U - L + 2 * β + 1 := by
    have h := separated_interval_card centers (fun q => (q : ℝ)) 1 (L - β) (U + β)
      (by norm_num) (by linarith) (fun i _ j _ _ => by ring_nf; exact le_rfl)
      (fun q hq => by
        have hq' := Finset.mem_Icc.mp hq
        exact ⟨Int.ceil_le.mp hq'.1, Int.le_floor.mp hq'.2⟩)
    convert h using 1; ring
  calc
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
        ((centers.biUnion fiber).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ centers, ((fiber q).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := centers) (t := fiber))
    _ ≤ ∑ _q ∈ centers, (2 * β / lam + 1) :=
      Finset.sum_le_sum (fun q _ => hfiber q)
    _ = (centers.card : ℝ) * (2 * β / lam + 1) := by
      simp
      ring
    _ ≤ (U - L + 2 * β + 1) * (2 * β / lam + 1) :=
      mul_le_mul_of_nonneg_right hcenters (by positivity)

/-- Natural-index version for finite exponential-sum blocks. -/
theorem separated_near_integer_card_nat (s : Finset ℕ) (f : ℕ → ℝ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, L ≤ f i ∧ f i ≤ U) :
    ((s.filter fun i : ℕ => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  let t : Finset ℤ := s.image (fun i : ℕ => (i : ℤ))
  have h := separated_near_integer_card t (fun z => f z.toNat) lam β L U hlam hβ hLU
    (by
      intro i hi j hj hij
      obtain ⟨ii, hii, rfl⟩ := Finset.mem_image.mp (show i ∈ s.image (fun i : ℕ => (i : ℤ)) from hi)
      obtain ⟨jj, hjj, rfl⟩ := Finset.mem_image.mp (show j ∈ s.image (fun i : ℕ => (i : ℤ)) from hj)
      simpa using hsep ii hii jj hjj (by exact_mod_cast hij))
    (by
      intro i hi
      obtain ⟨ii, hii, rfl⟩ := Finset.mem_image.mp (show i ∈ s.image (fun i : ℕ => (i : ℤ)) from hi)
      simpa using hrange ii hii)
  simpa only [t, Finset.filter_image, Int.toNat_natCast,
    Finset.card_image_of_injective _ (Nat.cast_injective (R := ℤ))] using h

/-- Adjacent slope bounds telescope to bounds between arbitrary indices. -/
theorem slope_bounds_of_adjacent (f : ℕ → ℝ) (N : ℕ) (lam B : ℝ)
    (hstep : ∀ j < N, lam ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ B) :
    ∀ j ≤ N, ∀ i ≤ j,
      lam * ((j : ℝ) - i) ≤ f j - f i ∧
      f j - f i ≤ B * ((j : ℝ) - i) := by
  intro j
  induction j with
  | zero =>
    intro hj i hi
    have : i = 0 := by omega
    subst i
    simp
  | succ j ih =>
    intro hj i hi
    by_cases hij : i = j + 1
    · subst i
      simp
    · have hi' : i ≤ j := by omega
      obtain ⟨hl, hu⟩ := ih (by omega) i hi'
      obtain ⟨hsl, hsu⟩ := hstep j (by omega)
      push_cast
      constructor <;> nlinarith

/-- Direct interface for the bad part of the discrete second-derivative test. -/
theorem adjacent_near_integer_card (f : ℕ → ℝ) (N : ℕ) (lam B β : ℝ)
    (hlam : 0 < lam) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hstep : ∀ j < N, lam ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ B) :
    (((Finset.range N).filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
      (B * N + 2 * β + 1) * (2 * β / lam + 1) := by
  have hslope := slope_bounds_of_adjacent f N lam B hstep
  have h := separated_near_integer_card_nat (Finset.range N) f lam β (f 0) (f 0 + B * N)
    hlam hβ (by
      have hBN : 0 ≤ B * (N : ℝ) := by positivity
      linarith)
    (fun i hi j hj hij => (hslope j (by simpa using (Finset.mem_range.mp hj).le) i hij).1)
    (by
      intro i hi
      have hi' : i ≤ N := (Finset.mem_range.mp hi).le
      obtain ⟨hl, hu⟩ := hslope i hi' 0 (Nat.zero_le i)
      have hmul : B * (i : ℝ) ≤ B * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hi') hB
      have hnonneg : 0 ≤ lam * (i : ℝ) := by positivity
      norm_num at hl hu
      constructor <;> linarith)
  convert h using 1; ring

/-- Continuous derivative hypotheses imply the discrete separation needed for
near-integer counting on any finite set of integer sample points. -/
theorem derivative_near_integer_card (s : Finset ℤ) (g : ℝ → ℝ)
    (a b lam B β : ℝ) (hab : a ≤ b) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (hg : ContinuousOn g (Set.Icc a b))
    (hg' : DifferentiableOn ℝ g (interior (Set.Icc a b)))
    (hderiv : ∀ x ∈ interior (Set.Icc a b), lam ≤ deriv g x ∧ deriv g x ≤ B)
    (hs : ∀ i ∈ s, (i : ℝ) ∈ Set.Icc a b) :
    ((s.filter fun i : ℤ => ∃ q : ℤ, |g (i : ℝ) - q| ≤ β).card : ℝ) ≤
      (B * (b - a) + 2 * β + 1) * (2 * β / lam + 1) := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hlow (x : ℝ) (hx : x ∈ Set.Icc a b) (y : ℝ) (hy : y ∈ Set.Icc a b)
      (hxy : x ≤ y) : lam * (y - x) ≤ g y - g x :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hg hg'
      (fun x hx => (hderiv x hx).1) x hx y hy hxy
  have hmono : MonotoneOn g (Set.Icc a b) := by
    intro x hx y hy hxy
    have h := hlow x hx y hy hxy
    have hp : 0 ≤ lam * (y - x) := mul_nonneg hlam.le (sub_nonneg.mpr hxy)
    linarith
  have hu := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hg hg'
    (fun x hx => (hderiv x hx).2) a ha b hb hab
  have h := separated_near_integer_card s (fun i => g i) lam β (g a) (g b)
    hlam hβ (hmono ha hb hab)
    (fun i hi j hj hij => hlow i (hs i hi) j (hs j hj) (by exact_mod_cast hij))
    (fun i hi => ⟨hmono ha (hs i hi) (hs i hi).1, hmono (hs i hi) hb (hs i hi).2⟩)
  calc
    _ ≤ (g b - g a + 2 * β + 1) * (2 * β / lam + 1) := h
    _ ≤ (B * (b - a) + 2 * β + 1) * (2 * β / lam + 1) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity

/-- The square-root choice in the second-derivative estimate gives the expected
three-term shape, with explicit harmless constants. -/
theorem near_integer_sqrt_budget (A T lam : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * Real.sqrt lam / lam + 1) ≤
      3 * A * T * Real.sqrt lam + 2 / Real.sqrt lam + 7 := by
  have hx : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hx1 : Real.sqrt lam ≤ 1 := by simpa using Real.sqrt_le_sqrt hlam1
  have hsq := Real.sq_sqrt hlam.le
  have hlamx : lam ≤ Real.sqrt lam := by nlinarith
  have hal : A * T * lam ≤ A * T * Real.sqrt lam :=
    mul_le_mul_of_nonneg_left hlamx (mul_nonneg hA hT)
  have heq : (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * Real.sqrt lam / lam + 1) =
      2 * A * T * Real.sqrt lam + A * T * lam + 5 + 2 * Real.sqrt lam + 2 / Real.sqrt lam := by
    field_simp
    nlinarith [hsq]
  rw [heq]
  linarith

end Problem337

end

end OAI
