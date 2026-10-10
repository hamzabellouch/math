import Mathlib.Algebra.Order.Floor.Ring
import OAI.NumberTheory.Ostmann.Construction.GoodCellSums

namespace OAI

/-! # Shifted cell indices and target sums -/

namespace Ostmann

/-- The nonnegative differences of a set of cell indices from its first index. -/
def cellDifferences (I : Finset ℕ) (a : ℕ) : Finset ℕ :=
  I.image (fun x => x - a)

theorem cellDifferences_card (I : Finset ℕ) (a : ℕ) (hlo : ∀ x ∈ I, a ≤ x) :
    (cellDifferences I a).card = I.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy h
  have hx' := hlo x hx
  have hy' := hlo y hy
  change x - a = y - a at h
  omega

/-- A dense interval set realizes every interior target in the appropriate
residue class, with an exact prescribed number of cell labels. -/
theorem dense_cell_exact_sum (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * (b - a : ℕ) + 1 ≤ I.card → ∀ n : ℕ, r ≤ n → ∀ t : ℕ,
      (cellDifferences I a).gcd id ∣ t - n * a →
      n * a + r * (b - a) ≤ t → t ≤ n * a + (n - r) * (b - a) →
      ∃ w : List ℕ, w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧ w.sum = t := by
  classical
  obtain ⟨r, hr, hcover⟩ := dense_difference_sum_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro I a b hab ha hb hbounds hdensity n hrn t hdiv htlo hthi
  let A := cellDifferences I a
  have h0 : 0 ∈ A := Finset.mem_image.mpr ⟨a, ha, Nat.sub_self _⟩
  have hs : b - a ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ b - a := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  obtain ⟨w, hwlen, hwmem, hwsum⟩ := hcover A (b - a) (Nat.sub_pos_of_lt hab)
    h0 hs hbound (by rwa [hcard]) n hrn (t - n * a) hdiv (by omega) (by omega)
  refine ⟨w.map (fun x => a + x), by simpa using hwlen, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hwmem y hy)
    rwa [Nat.add_sub_of_le (hbounds z hz).1]
  · have ht : n * a ≤ t := by omega
    have hsum (v : List ℕ) : (v.map (fun x => a + x)).sum = v.length * a + v.sum := by
      induction v with
      | nil => simp
      | cons x v ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_mul, Nat.one_mul]
          omega
    rw [hsum w, hwlen, hwsum]
    omega

/-- Density bounds the lattice spacing of the cell differences. -/
theorem dense_difference_gcd_bound (A : Finset ℕ) (s : ℕ) (hs : 0 < s)
    (hend : s ∈ A) (hbound : ∀ a ∈ A, a ≤ s) (δ : ℝ)
    (hdensity : δ * s + 1 ≤ A.card) :
    δ * (A.gcd id : ℕ) ≤ 1 := by
  classical
  let g : ℕ := A.gcd id
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  let U := A.image (fun a => a / g)
  have hUcard : U.card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have haeq : g * (a / g) = a := Nat.mul_div_cancel' (Finset.gcd_dvd ha)
    have hbeq : g * (b / g) = b := Nat.mul_div_cancel' (Finset.gcd_dvd hb)
    exact haeq.symm.trans ((congrArg (fun x => g * x) hab).trans hbeq)
  have hsubset : U ⊆ Finset.range (s / g + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hbound y hy)))
  have hc : A.card ≤ s / g + 1 := by
    simpa only [hUcard, Finset.card_range] using Finset.card_le_card hsubset
  have hcount : g * A.card ≤ s + g := by
    have hh := Nat.mul_le_mul_left g hc
    rw [Nat.mul_add, Nat.mul_div_cancel' hgs, Nat.mul_one] at hh
    exact hh
  have hr : (g : ℝ) * A.card ≤ s + g := by exact_mod_cast hcount
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  change δ * (g : ℝ) ≤ 1
  nlinarith [mul_le_mul_of_nonneg_left hdensity hgr.le]

end Ostmann

end OAI
