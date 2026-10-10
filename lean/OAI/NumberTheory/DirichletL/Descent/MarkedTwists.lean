import OAI.NumberTheory.DirichletL.Descent.MarkedFourier

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_monoid (Ψ φ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun A => φ (primaryGenerator A)) = completedT (φ * Ψ) W X := by
  unfold markedCompletedT completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  change summand Ψ W X I J * φ (primaryGenerator (I * J ^ 3)) = _
  rw [summand_mul_fixed_twist, primaryGenerator_mul,
    show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from map_pow primaryGeneratorHom J 3]
  exact mul_comm _ _

theorem whole_prime_mark_eq_mask_complement (p : Eis) (hp : Prime p)
    (A : Ideal Eis) (hA : primaryGenerator A ≠ 0) :
    (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
      1 - coprimalityMask p (primaryGenerator A) := by
  have hd : Ideal.span {p} ∣ A ↔ p ∣ primaryGenerator A := by
    calc
      _ ↔ A ≤ Ideal.span {p} := Ideal.dvd_iff_le
      _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {p} := by
        rw [(primaryGenerator_spec A hA).1]
      _ ↔ _ := by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  change (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
    1 - (if IsCoprime p (primaryGenerator A) then 1 else 0)
  rw [hp.coprime_iff_not_dvd]
  by_cases h : p ∣ primaryGenerator A <;> simp [hd, h]

theorem markedCompletedT_prime_product_twists {ι : Type*}
    (S : Finset ι) (p : ι → Eis) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        completedT ((∏ i ∈ T, coprimalityMask (p i)) * Ψ) W X := by
  have he : markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          (∏ i ∈ T, coprimalityMask (p i)) (primaryGenerator A)) := by
    apply markedCompletedT_congr_primary
    intro A hA
    calc
      _ = ∏ i ∈ S, (1 - coprimalityMask (p i) (primaryGenerator A)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (p i) (hp i hi) A hA
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  rw [he, markedCompletedT_finset_sum S.powerset Ψ W hW X hX]
  apply Finset.sum_congr rfl
  intro T hT
  rw [markedCompletedT_const_mul, markedCompletedT_monoid]

end
end SevenEighths.InverseMoment

end OAI
