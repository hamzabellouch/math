import Mathlib
import OAI.Computability.VertexCover.Information.Conditionals
import OAI.Computability.VertexCover.Repetition.Variation

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Information

private theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self {«c» t : ℝ} (hc : 0 ≤ «c») (ht : 0 ≤ t) :
    «c» / (1 + t) ≤ «c» := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul {«c» t : ℝ} (hc : 0 ≤ «c») (ht : 0 ≤ t) :
    «c» - «c» / (1 + t) ≤ «c» * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : «c» - «c» / (1 + t) = «c» * t / (1 + t) := by
    field_simp [hd.ne']
    ; ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
