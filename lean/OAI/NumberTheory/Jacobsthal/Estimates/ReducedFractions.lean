import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open Set
open scoped BigOperators

namespace AdditiveLargeSieve

def reducedFractions (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ Finset.range Q).filter fun z => z.2 < z.1 ∧ z.2.Coprime z.1

@[simp] theorem mem_reducedFractions {Q : ℕ} {z : ℕ × ℕ} :
    z ∈ reducedFractions Q ↔ 1 ≤ z.1 ∧ z.1 ≤ Q ∧ z.2 < z.1 ∧ z.2.Coprime z.1 := by
  simp only [reducedFractions, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hq, hQ⟩, _⟩, ha, hc⟩
    exact ⟨hq, hQ, ha, hc⟩
  · rintro ⟨hq, hQ, ha, hc⟩
    exact ⟨⟨⟨hq, hQ⟩, ha.trans_le hQ⟩, ha, hc⟩

noncomputable def fractionValue (z : ℕ × ℕ) : ℝ := (z.2 : ℝ) / z.1

theorem fractionValue_mem {Q : ℕ} {z : ℕ × ℕ} (hz : z ∈ reducedFractions Q) :
    fractionValue z ∈ Ico (0 : ℝ) 1 := by
  rcases mem_reducedFractions.mp hz with ⟨hq, _, ha, _⟩
  have hq' : 0 < (z.1 : ℝ) := by exact_mod_cast (show 0 < z.1 by omega)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq'.le,
    (div_lt_one hq').2 (by exact_mod_cast ha)⟩

theorem reduced_cross_injective {x y : ℕ × ℕ}
    (_hx : 0 < x.1) (hy : 0 < y.1) (hcx : x.2.Coprime x.1) (hcy : y.2.Coprime y.1)
    (h : x.2 * y.1 = y.2 * x.1) : x = y := by
  have hxy : x.1 ∣ y.1 := hcx.symm.dvd_of_dvd_mul_left (h ▸ Nat.dvd_mul_left x.1 y.2)
  have hyx : y.1 ∣ x.1 := hcy.symm.dvd_of_dvd_mul_left (h.symm ▸ Nat.dvd_mul_left y.1 x.2)
  have hq : x.1 = y.1 := Nat.dvd_antisymm hxy hyx
  have ha : x.2 = y.2 := by
    rw [hq] at h
    exact Nat.eq_of_mul_eq_mul_right hy h
  exact Prod.ext hq ha

theorem one_le_abs_cast_sub {a b : ℕ} (hab : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem reduced_fraction_separation {Q : ℕ} (hQ : 0 < Q)
    {x y : ℕ × ℕ} (hx : x ∈ reducedFractions Q) (hy : y ∈ reducedFractions Q) (hne : x ≠ y) :
    ((Q : ℝ) ^ 2)⁻¹ ≤ |fractionValue x - fractionValue y| := by
  rcases mem_reducedFractions.mp hx with ⟨hx0, hxQ, _, hcx⟩
  rcases mem_reducedFractions.mp hy with ⟨hy0, hyQ, _, hcy⟩
  have hxpos : 0 < (x.1 : ℝ) := by exact_mod_cast (show 0 < x.1 by omega)
  have hypos : 0 < (y.1 : ℝ) := by exact_mod_cast (show 0 < y.1 by omega)
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hcross : x.2 * y.1 ≠ y.2 * x.1 := by
    intro h
    exact hne (reduced_cross_injective (by omega) (by omega) hcx hcy h)
  have hnum := one_le_abs_cast_sub hcross
  simp only [Nat.cast_mul] at hnum
  have hformula : fractionValue x - fractionValue y =
      ((x.2 : ℝ) * y.1 - y.2 * x.1) / ((x.1 : ℝ) * y.1) := by
    dsimp [fractionValue]
    field_simp
  rw [hformula, abs_div, abs_of_pos (mul_pos hxpos hypos)]
  have hprod : (x.1 : ℝ) * y.1 ≤ (Q : ℝ) ^ 2 := by
    have hxQ' : (x.1 : ℝ) ≤ Q := by exact_mod_cast hxQ
    have hyQ' : (y.1 : ℝ) ≤ Q := by exact_mod_cast hyQ
    nlinarith
  calc
    ((Q : ℝ) ^ 2)⁻¹ = 1 / (Q : ℝ) ^ 2 := by rw [one_div]
    _ ≤ 1 / ((x.1 : ℝ) * y.1) := one_div_le_one_div_of_le (mul_pos hxpos hypos) hprod
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hxpos hypos).le

theorem sum_reducedFractions {E : Type*} [AddCommMonoid E] (Q : ℕ) (f : ℕ × ℕ → E) :
    ∑ z ∈ reducedFractions Q, f z =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f (q, a) := by
  classical
  simp only [reducedFractions, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  have hsets : (Finset.range Q).filter (fun a => a < q ∧ a.Coprime q) =
      (Finset.range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    have := (Finset.mem_Icc.mp hq).2
    omega
  rw [hsets, Finset.sum_filter]

end AdditiveLargeSieve

end

end Erdos970

end OAI
