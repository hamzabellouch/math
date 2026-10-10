import OAI.NumberTheory.DirichletL.Descent.Quotients

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal Eis)
    (hP : primaryGenerator P ≠ 0) (hcm : primaryGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := by
  apply inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal Eis)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal Eis) (hRr : IsCoprime R r) (F : Ideal Eis → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal Eis) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

theorem double_column_divisor_reindex {A : Type*} [AddCommMonoid A]
    (Pset cset : Finset (Ideal Eis)) (R r : Ideal Eis)
    (F : Ideal Eis → Ideal Eis → A) :
    (∑ P ∈ Pset, ∑ c ∈ cset, if R ∣ P ∧ r ∣ c then F P c else 0) =
      ∑ P ∈ quotientSupport R Pset, ∑ c ∈ quotientSupport r cset, F (R * P) (r * c) := by
  calc
    _ = ∑ P ∈ Pset with R ∣ P, ∑ c ∈ cset with r ∣ c, F P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : R ∣ P
      · simp only [hd, true_and, ite_true]
      · simp [hd]
    _ = ∑ P ∈ quotientSupport R Pset, ∑ c ∈ cset with r ∣ c, F (R * P) c :=
      sum_quotientSupport R Pset (fun P => ∑ c ∈ cset with r ∣ c, F P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cset (F (R * P))

end
end SevenEighths.InverseMoment

end OAI
