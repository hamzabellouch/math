import OAI.NumberTheory.Ostmann.Arithmetic.CellDifferenceGCD
import OAI.NumberTheory.Ostmann.Preliminaries.IntegerSumsetCover

namespace OAI

/-! # Exact interior sums of dense sets of cell differences

The covering length depends only on the density. Every admissible multiple of
the actual gcd in the interior interval has an ordered representation.
-/

namespace Ostmann

open scoped BigOperators

/-- Uniform exact covering of the interior by sums of a dense set of differences. -/
theorem dense_difference_sum_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (A : Finset ℕ) (s : ℕ),
      0 < s → 0 ∈ A → s ∈ A → (∀ a ∈ A, a ≤ s) →
      δ * s + 1 ≤ A.card → ∀ n : ℕ, r ≤ n → ∀ t : ℕ,
      A.gcd id ∣ t → r * s ≤ t → t ≤ (n - r) * s →
      ∃ w : List ℕ, w.length = n ∧ (∀ a ∈ w, a ∈ A) ∧ w.sum = t := by
  classical
  obtain ⟨r, hr, hcover⟩ := exists_uniform_cyclic_sum_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro A s hs h0 hend hbound hdensity n hrn t hdiv hlo hhi
  let g : ℕ := A.gcd id
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  let q := s / g
  have hgqs : g * q = s := Nat.mul_div_cancel' hgs
  have hq : 0 < q := by nlinarith
  have hqs : q ≤ s := Nat.div_le_self _ _
  let U := A.image (fun a => a / g)
  have hU0 : 0 ∈ U := Finset.mem_image.mpr ⟨0, h0, by simp⟩
  have hUq : q ∈ U := Finset.mem_image.mpr ⟨s, hend, rfl⟩
  have hUbound : ∀ a ∈ U, a ≤ q := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Nat.div_le_div_right (hbound b hb)
  have hUcard : U.card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have haeq : g * (a / g) = a := Nat.mul_div_cancel' (Finset.gcd_dvd ha)
    have hbeq : g * (b / g) = b := Nat.mul_div_cancel' (Finset.gcd_dvd hb)
    exact haeq.symm.trans ((congrArg (fun x => g * x) hab).trans hbeq)
  let V := U.image (fun a : ℕ => (a : ZMod q))
  have hV0 : (0 : ZMod q) ∈ V := Finset.mem_image.mpr ⟨0, hU0, by simp⟩
  have hVgen : AddSubgroup.closure (V : Set (ZMod q)) = ⊤ :=
    normalized_cyclic_closure A s hend hs.ne' q
  have hVcard : U.card ≤ V.card + 1 := card_residue_image_lower U q hq hUbound
  have hVdensity : δ * q ≤ V.card := by
    have hh : (q : ℝ) ≤ s := by exact_mod_cast hqs
    have hc : (U.card : ℝ) ≤ V.card + 1 := by exact_mod_cast hVcard
    rw [hUcard] at hc
    nlinarith
  let : NeZero q := ⟨hq.ne'⟩
  have hwords := lift_cyclic_sum_cover U q r (hcover q V hV0 hVgen hVdensity)
  have htlo : r * q ≤ t / g := by
    apply (Nat.le_div_iff_mul_le hg).mpr
    calc
      r * q * g = r * s := by rw [mul_assoc, mul_comm q g, hgqs]
      _ ≤ t := hlo
  have hthi : t / g ≤ (n - r) * q := by
    calc
      t / g ≤ ((n - r) * s) / g := Nat.div_le_div_right hhi
      _ = (n - r) * q := Nat.mul_div_assoc (n - r) hgs
  obtain ⟨w, hwlen, hwmem, hwsum⟩ :=
    integer_interval_sum_cover U q r n hq hU0 hUq hUbound hrn hwords (t / g) htlo hthi
  refine ⟨w.map (fun a => g * a), by simpa using hwlen, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hwmem b hb)
    have heq : g * (c / g) = c := Nat.mul_div_cancel' (Finset.gcd_dvd hc)
    rwa [heq]
  · rw [List.sum_map_mul_left]
    simp only [List.map_id', hwsum]
    exact Nat.mul_div_cancel' hdiv

end Ostmann

end OAI
