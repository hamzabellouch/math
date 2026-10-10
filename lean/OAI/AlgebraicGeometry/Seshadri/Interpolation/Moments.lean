import Mathlib

namespace OAI


                                              
section
namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

theorem zero_of_moments {α K : Type*} [DecidableEq α] [Field K]
    (s : Finset α) (x c : α → K) (hx : Set.InjOn x s)
    (hm : ∀ n < s.card, ∑ a ∈ s, c a * (x a) ^ n = 0) :
    ∀ a ∈ s, c a = 0 := by
  classical
  let E : Fin s.card ≃ s := (s.equivFin).symm
  have hE : Function.Injective (fun i : Fin s.card => x (E i)) := by
    intro i j hij
    apply E.injective
    apply Subtype.ext
    exact hx (E i).property (E j).property hij
  have hsum (n : Fin s.card) :
      ∑ j : Fin s.card, c (E j) * x (E j) ^ (n : ℕ) = 0 := by
    rw [show (∑ j : Fin s.card, c (E j) * x (E j) ^ (n : ℕ)) =
        ∑ j : s, c j * x j ^ (n : ℕ) from
      E.sum_comp (fun j : s => c j * x j ^ (n : ℕ))]
    rw [show (∑ j : s, c j * x j ^ (n : ℕ)) =
        ∑ j ∈ s, c j * x j ^ (n : ℕ) from
      Finset.sum_coe_sort s (fun j => c j * x j ^ (n : ℕ))]
    exact hm n n.isLt
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hE hsum
  intro a ha
  have h := congrFun hzero (E.symm ⟨a, ha⟩)
  simpa using h

def rows (s : Finset (ℤ × ℤ)) : Finset ℤ := s.image Prod.snd

def row (s : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (s.filter (fun p => p.2 = y)).image Prod.fst

@[simp] theorem mem_row (s : Finset (ℤ × ℤ)) (x y : ℤ) :
    x ∈ row s y ↔ (x, y) ∈ s := by
  simp only [row, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩

theorem row_nonempty {s : Finset (ℤ × ℤ)} {y : ℤ} (hy : y ∈ rows s) :
    (row s y).Nonempty := by
  obtain ⟨⟨x, z⟩, h, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x, (mem_row s x z).mpr h⟩

def rowMoment (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (a : ℕ) (y : ℤ) : ℂ :=
  ∑ x ∈ row s y, c (x, y) * (x : ℂ) ^ a

def EulerJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, rowMoment s c a y * (y : ℂ) ^ b = 0

theorem row_zero_of_euler_jet (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (m : ℕ) (y : ℤ) (hy : y ∈ rows s)
    (hsize : (row s y).card + (rows s).card ≤ m + 1)
    (hjet : EulerJetZero s c m) : ∀ x ∈ row s y, c (x, y) = 0 := by
  apply zero_of_moments (row s y) (fun x : ℤ => (x : ℂ)) (fun x => c (x, y))
  · exact (Int.cast_injective).injOn
  intro a ha
  apply zero_of_moments (rows s) (fun y : ℤ => (y : ℂ)) (rowMoment s c a)
    (Int.cast_injective.injOn) _ y hy
  intro b hb
  exact hjet a b (by omega)

theorem card_sub_one_le_span (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℝ) - 1 ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) := by
  have hle : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hi : (s.card : ℤ) ≤ s.max' hs + 1 - s.min' hs := by
    rw [← Int.card_Icc_of_le _ _ (by omega)]
    exact_mod_cast hc
  have hr : (s.card : ℝ) ≤ (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by
    exact_mod_cast hi
  linarith

def planeForm (a b c : ℝ) (p : ℝ × ℝ) : ℝ := a * p.1 + b * p.2 + c

theorem planeForm_nonneg_on_hull (a b c : ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ p ∈ s, 0 ≤ planeForm a b c p) :
    ∀ p ∈ convexHull ℝ s, 0 ≤ planeForm a b c p := by
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 ≤ planeForm a b c p} := by
    intro p hp q hq u v hu hv huv
    change 0 ≤ a * (u * p.1 + v * q.1) + b * (u * p.2 + v * q.2) + c
    have hmul := add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)
    dsimp [planeForm] at hmul
    calc
      0 ≤ u * (a * p.1 + b * p.2 + c) + v * (a * q.1 + b * q.2 + c) := hmul
      _ = a * (u * p.1 + v * q.1) + b * (u * p.2 + v * q.2) + c := by
        nlinarith [congrArg (fun z : ℝ => z * c) huv]
  exact convexHull_min h hconv

def transverse (x₀ y₀ shear sign : ℝ) (p : ℝ × ℝ) : ℝ :=
  sign * (p.1 - x₀ - shear * (p.2 - y₀))

def balancedStrip (ρ h x₀ y₀ shear sign : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ transverse x₀ y₀ shear sign p ∧
    h * transverse x₀ y₀ shear sign p ≤ ρ * (p.2 - y₀) ∧
    (ρ - h) * transverse x₀ y₀ shear sign p ≤ ρ * (y₀ + ρ - p.2)}

theorem balanced_row_constraints (ρ h x₀ y₀ shear sign : ℝ)
    (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (xs : Finset ℤ) (hxs : xs.Nonempty) (y : ℤ)
    (hs : ∀ x ∈ xs, ((x : ℝ), (y : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign) :
    h * ((xs.card : ℝ) - 1) ≤ ρ * ((y : ℝ) - y₀) ∧
    (ρ - h) * ((xs.card : ℝ) - 1) ≤ ρ * (y₀ + ρ - (y : ℝ)) := by
  let lo := xs.min' hxs
  let hi := xs.max' hxs
  have hlo := hs lo (xs.min'_mem hxs)
  have hhi := hs hi (xs.max'_mem hxs)
  have hw := card_sub_one_le_span xs hxs
  change (xs.card : ℝ) - 1 ≤ (hi : ℝ) - (lo : ℝ) at hw
  have hwidth : ∃ x ∈ xs, (hi : ℝ) - (lo : ℝ) ≤
      transverse x₀ y₀ shear sign ((x : ℝ), (y : ℝ)) := by
    have hc : sign = 1 ∨ sign = -1 := sq_eq_one_iff.mp hsign
    rcases hc with rfl | rfl
    · refine ⟨hi, xs.max'_mem hxs, ?_⟩
      have h := hlo.1
      dsimp [transverse] at h ⊢
      linarith
    · refine ⟨lo, xs.min'_mem hxs, ?_⟩
      have h := hhi.1
      dsimp [transverse] at h ⊢
      linarith
  obtain ⟨x, hx, hxx⟩ := hwidth
  have hp := hs x hx
  constructor
  · exact (mul_le_mul_of_nonneg_left (hw.trans hxx) hh).trans hp.2.1
  · exact (mul_le_mul_of_nonneg_left (hw.trans hxx) (sub_nonneg.mpr hhρ)).trans hp.2.2

theorem balanced_diagram_card (ρ h x₀ y₀ shear sign : ℝ)
    (hρ : 0 < ρ) (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign) :
    ∃ y ∈ rows s, ((row s y).card : ℝ) + ((rows s).card : ℝ) ≤ ρ + 2 := by
  have hrows : (rows s).Nonempty := hs.image _
  obtain ⟨y, hy, hmin⟩ := (rows s).exists_min_image (fun y => (row s y).card) hrows
  refine ⟨y, hy, ?_⟩
  let k : ℝ := (row s y).card
  have hb (z : ℤ) (hz : z ∈ rows s) :
      h * (k - 1) ≤ ρ * ((z : ℝ) - y₀) ∧
      (ρ - h) * (k - 1) ≤ ρ * (y₀ + ρ - (z : ℝ)) := by
    have hk : k ≤ ((row s z).card : ℝ) := by
      dsimp [k]
      exact_mod_cast hmin z hz
    have hc := balanced_row_constraints ρ h x₀ y₀ shear sign hh hhρ hsign
      (row s z) (row_nonempty hz) z (fun x hx => hsupp (x, z) ((mem_row s x z).mp hx))
    constructor
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hk _) hh).trans hc.1
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hk _) (sub_nonneg.mpr hhρ)).trans hc.2
  have hlo := (hb ((rows s).min' hrows) ((rows s).min'_mem hrows)).1
  have hhi := (hb ((rows s).max' hrows) ((rows s).max'_mem hrows)).2
  have hspan := card_sub_one_le_span (rows s) hrows
  have hprod := mul_le_mul_of_nonneg_left hspan hρ.le
  change k + ((rows s).card : ℝ) ≤ ρ + 2
  nlinarith

theorem balanced_triangle_euler_test (ρ h x₀ y₀ shear sign : ℝ)
    (hρ : 0 < ρ) (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign)
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ EulerJetZero s c m := by
  intro hj
  obtain ⟨y, hy, hsize⟩ := balanced_diagram_card ρ h x₀ y₀ shear sign hρ hh hhρ hsign s hs hsupp
  have hint : (row s y).card + (rows s).card ≤ m + 1 := by
    have hh : (((row s y).card + (rows s).card : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hn : (row s y).card + (rows s).card < m + 2 := by exact_mod_cast hh
    omega
  obtain ⟨x, hx⟩ := row_nonempty hy
  exact hc (x, y) ((mem_row s x y).mp hx) (row_zero_of_euler_jet s c m y hy hint hj x hx)

theorem transverse_affine (x₀ y₀ shear sign : ℝ) (p q : ℝ × ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    transverse x₀ y₀ shear sign (a • p + b • q) =
      a * transverse x₀ y₀ shear sign p + b * transverse x₀ y₀ shear sign q := by
  dsimp [transverse]
  linear_combination sign * (x₀ - shear * y₀) * hab

theorem convex_balancedStrip (ρ h x₀ y₀ shear sign : ℝ) :
    Convex ℝ (balancedStrip ρ h x₀ y₀ shear sign) := by
  intro p hp q hq a b ha hb hab
  have ht := transverse_affine x₀ y₀ shear sign p q a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  · calc
      h * transverse x₀ y₀ shear sign (a • p + b • q) =
          a * (h * transverse x₀ y₀ shear sign p) +
          b * (h * transverse x₀ y₀ shear sign q) := by rw [ht]; ring
      _ ≤ a * (ρ * (p.2 - y₀)) + b * (ρ * (q.2 - y₀)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.1 ha)
          (mul_le_mul_of_nonneg_left hq.2.1 hb)
      _ = ρ * ((a • p + b • q).2 - y₀) := by
        dsimp
        linear_combination -(ρ * y₀) * hab
  · calc
      (ρ - h) * transverse x₀ y₀ shear sign (a • p + b • q) =
          a * ((ρ - h) * transverse x₀ y₀ shear sign p) +
          b * ((ρ - h) * transverse x₀ y₀ shear sign q) := by rw [ht]; ring
      _ ≤ a * (ρ * (y₀ + ρ - p.2)) + b * (ρ * (y₀ + ρ - q.2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.2 ha)
          (mul_le_mul_of_nonneg_left hq.2.2 hb)
      _ = ρ * (y₀ + ρ - (a • p + b • q).2) := by
        dsimp
        linear_combination ρ * (y₀ + ρ) * hab


end MaximalSeshadri.Interpolation
end

end OAI
