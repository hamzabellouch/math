import OAI.NumberTheory.DirichletL.Descent.DyadicBlock
import OAI.NumberTheory.DirichletL.Descent.MaskedGrid
import OAI.NumberTheory.DirichletL.Descent.DivisorSum

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_fixed_square_grid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (t : Ideal Eis), T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ rows, ‖maskedGridHybridRow (hybridGridSupport D) Pset a beta t k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_extracted_dyadic_block ε hε
  obtain ⟨C₂, hC₂, hmask⟩ := maskedGridHybridRow_divisor_energy ε hε
  refine ⟨C₁ * C₂ * 256 ^ 2, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT t ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  have hr0 : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K :=
    fun k hk => ⟨(hrows k hk).1.1, (hrows k hk).2⟩
  let E := C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
    CubicSieve.sieveNorm N (2 * L)
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hTprim : ∀ u ∈ hybridGridSupport D, primaryGenerator (u.2 * u.1.1) ≠ 0 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact (hn _ (hD d hd).2.2.2.1).1.2
  have hterm (v : Ideal Eis × Ideal Eis) (hv : v ∈ hybridDivisorPairPool rows) :
      (∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) := by
    have hp := Finset.mem_product.mp (hybridDivisorPairPool_subset rows hv)
    have hR := (hybridDivisorPool_bounds rows K hr0 v.1 hp.1).1
    have hr := (hybridDivisorPool_bounds rows K hr0 v.2 hp.2).1
    by_cases hcop : IsCoprime v.1 v.2
    · rw [double_divisor_row_reindex rows (fun k hk => (hr0 k hk).1) v.1 v.2 hcop]
      have he := hblock K N B L C T hK hN hB hC hT v.1 v.2 t hR hr ht
        rows nset Pset D a beta hrows hn hP ha hD hbeta
      convert he using 1
      dsimp only [E]
      field_simp
    · simp only [gridDivisorHybridBlock_zero_of_not_coprime _ _ _ _ _ _ _ _ hcop
          (fun P hPP => (hP P hPP).1.2) hTprim,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0), ite_self, Finset.sum_const_zero]
      exact mul_nonneg hE (by positivity)
  have he := hmask K hK rows (hybridGridSupport D) Pset a beta t hr0
  have hsum : (∑ v ∈ hybridDivisorPairPool rows,
      ∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ hybridDivisorPairPool rows,
          E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = E * ∑ v ∈ hybridDivisorPairPool rows,
          1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hybrid_divisor_pair_inverse_norm_sum rows K hr0) hE
  apply he.trans
  calc
    _ ≤ C₂ * K ^ ε * (E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [E]; ring

end
end SevenEighths.InverseMoment

end OAI
