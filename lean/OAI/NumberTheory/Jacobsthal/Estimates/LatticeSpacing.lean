import OAI.NumberTheory.Jacobsthal.Estimates.FactorDividesAbscissa

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine

theorem congruent_integer_set_card (A : Finset ℤ) (S : ℝ) (hS : 0 ≤ S)
    (d : ℕ) (hd : 0 < d) (hbox : ∀ x ∈ A, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S)
    (hdiv : ∀ x ∈ A, ∀ y ∈ A, (d : ℤ) ∣ x-y) :
    (A.card : ℝ) ≤ S/(d : ℝ)+1 := by
  classical
  by_cases hA : A.Nonempty
  · let x0 : ℤ := A.min' hA
    have hx0 : x0 ∈ A := Finset.min'_mem A hA
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    let f : ℤ → ℤ := fun x => (x-x0)/(d : ℤ)
    have he (x : ℤ) (hx : x ∈ A) : (d : ℤ)*f x = x-x0 := by
      exact Int.mul_ediv_cancel' (hdiv x hx x0 hx0)
    have hinj : Set.InjOn f (A : Set ℤ) := by
      intro x hx y hy hxy
      have hh : x-x0 = y-x0 := by rw [← he x hx,← he y hy,hxy]
      omega
    have hfloor : 0 ≤ ⌊S/(d : ℝ)⌋ := Int.floor_nonneg.mpr (div_nonneg hS hdR.le)
    have hsubset : A.image f ⊆ Finset.Icc 0 ⌊S/(d : ℝ)⌋ := by
      intro t ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
      have hmin : x0 ≤ x := Finset.min'_le A x hx
      have hf0 : 0 ≤ f x := Int.ediv_nonneg (sub_nonneg.mpr hmin) hdZ.le
      have heR : (d : ℝ)*(f x : ℝ) = (x : ℝ)-(x0 : ℝ) := by exact_mod_cast he x hx
      have hfS : (f x : ℝ) ≤ S/(d : ℝ) := by
        apply (le_div_iff₀ hdR).mpr
        have hb := hbox x hx
        have hb0 := (hbox x0 hx0).1
        nlinarith
      exact Finset.mem_Icc.mpr ⟨hf0,Int.le_floor.mpr hfS⟩
    have hc : A.card ≤ (Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsubset
    have hi : ((Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card : ℝ) =
        (⌊S/(d : ℝ)⌋ : ℝ)+1 := by
      have hh := Int.card_Icc_of_le 0 ⌊S/(d : ℝ)⌋ (show (0 : ℤ) ≤ ⌊S/(d : ℝ)⌋+1 by omega)
      simp only [sub_zero] at hh
      exact_mod_cast hh
    calc
      (A.card : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊S/(d : ℝ)⌋).card : ℝ) := by exact_mod_cast hc
      _ = (⌊S/(d : ℝ)⌋ : ℝ)+1 := hi
      _ ≤ S/(d : ℝ)+1 := add_le_add (Int.floor_le _) le_rfl
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem PrimitiveIntegerLine.denominator_dvd_x_difference (l : PrimitiveIntegerLine)
    (p q : ℤ × ℤ) (hp : l.Contains p) (hq : l.Contains q) :
    (l.denominator : ℤ) ∣ p.1-q.1 := by
  have he : l.slope*(p.1-q.1) = (l.denominator : ℤ)*(p.2-q.2) := by
    unfold Contains at hp hq
    linear_combination hq-hp
  have hg : Int.gcd (l.denominator : ℤ) l.slope = 1 := by
    simpa [Int.gcd_def] using l.reduced.symm.gcd_eq_one
  apply Int.dvd_of_dvd_mul_right_of_gcd_one (a := (l.denominator : ℤ)) (b := l.slope)
  · rw [he]
    exact dvd_mul_right _ _
  · exact hg

end ErdosRichLine

end

end Erdos970

end OAI
