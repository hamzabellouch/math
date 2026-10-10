import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainWeightBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveDivisibility

namespace OAI

/-! # Removing the actual gcd from the quadratic pair family -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_gcd_pair_reindex {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D, F z.1 z.2) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
  let P := (quadraticGcdPairs (N / D) 1).filter
    (fun z => D.Coprime z.1 ∧ D.Coprime z.2)
  have hsum : (∑ z ∈ P, F (D * z.1) (D * z.2)) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
    exact Finset.sum_filter _ _
  rw [← hsum]
  symm
  apply Finset.sum_bij (fun z _ => (D * z.1, D * z.2))
  · intro z hz
    obtain ⟨hz, hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₁, hcop.1⟩,
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₂, hcop.2⟩⟩, ?_⟩
    simp only [Nat.gcd_mul_left, hg, mul_one]
  · intro z _ y _ heq
    apply Prod.ext
    · have hh := congrArg Prod.fst heq
      exact mul_left_cancel₀ hD.ne_zero hh
    · have hh := congrArg Prod.snd heq
      exact mul_left_cancel₀ hD.ne_zero hh
  · intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    have hd₁ : D ∣ z.1 := hg ▸ Nat.gcd_dvd_left z.1 z.2
    have hd₂ : D ∣ z.2 := hg ▸ Nat.gcd_dvd_right z.1 z.2
    have he₁ : D * (z.1 / D) = z.1 := Nat.mul_div_cancel' hd₁
    have he₂ : D * (z.2 / D) = z.2 := Nat.mul_div_cancel' hd₂
    have hr₁ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₁ ▸ h₁)
    have hr₂ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₂ ▸ h₂)
    refine ⟨(z.1 / D, z.2 / D), ?_, Prod.ext he₁ he₂⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr₁.1, hr₂.1⟩, ?_⟩,
      hr₁.2, hr₂.2⟩
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left z.2 (Finset.mem_Icc.mp (Finset.mem_filter.mp h₁).1).1)
    rwa [hg] at hc
  · intro _ _
    rfl

 theorem quadraticPairKernel_mul_coprime {D a b : ℕ} (hD : D ≠ 0)
    (hab : a.Coprime b) : quadraticPairKernel (D * a) (D * b) = a * b := by
  have hg : (D * a).gcd (D * b) = D := by simp [Nat.gcd_mul_left, hab.gcd_eq_one]
  rw [quadraticPairKernel, hg]
  simp only [Nat.mul_div_right _ (Nat.pos_of_ne_zero hD)]

end Ostmann

end OAI
