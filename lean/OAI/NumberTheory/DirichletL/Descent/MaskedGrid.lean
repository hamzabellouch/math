import OAI.NumberTheory.DirichletL.Descent.ExtractedGrid

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def maskedGridHybridRow (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) : ℂ :=
  ∑ u ∈ T, ∑ P ∈ Pset, (if IsCoprime k (P * u.2) then 1 else 0) *
    (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (quadraticRow k (primaryGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0))

theorem maskedGridHybridRow_mobius (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) (hk : k ≠ 0) :
    maskedGridHybridRow T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (hT : ∀ u ∈ T, primaryGenerator (u.2 * u.1.1) ≠ 0) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (T : Grid) (Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (t : Ideal Eis),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖maskedGridHybridRow T Pset a beta t k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows T Pset a beta t hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock T Pset a beta t k D.1 D.2) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end
end SevenEighths.InverseMoment

end OAI
