import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdRemainder

namespace OAI

/-! # The complete small-kernel moment has a uniformly controlled Poisson error -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticSmallMomentCore (M N K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
    v z.1 * conj (v z.2) *
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallDyadicCore quadraticSieveWeight M b J
          (2 * (quadraticPairKernel z.1 z.2 * D)) b

theorem quadratic_small_dyadic_uniform (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M J : ℝ), 0 < M → 1 ≤ J →
      ∀ q : ℕ, [NeZero q] → q ≠ 1 → ∀ b : ℕ, 0 < b →
      ‖(∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
          quadraticSmallDyadicCore quadraticSieveWeight M b J q b‖ ≤
        C * Real.sqrt M / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_dyadic quadraticSieveWeight quadraticSieveWeight_zero A
  refine ⟨C, hC, ?_⟩
  intro M J hM hJ q _ hq b hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast hb
  apply (hc M b J hM hbR hJ q b hq le_rfl (by linarith)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.sqrt_le_sqrt (div_le_self hM.le hb₁)

theorem quadratic_small_moment_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ,
      ‖(quadraticSmallEnergy M N K v : ℂ) - quadraticSmallMomentCore M N K J v‖ ≤
        (C * Real.sqrt M * K / J ^ A) * N * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_dyadic_uniform A
  refine ⟨C, hC, ?_⟩
  intro M N K hM J hJ v
  let E (D : ℕ) (z : ℕ × ℕ) : ℂ :=
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        ((∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
          (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
          quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
        quadraticSmallDyadicCore quadraticSieveWeight M b J
          (2 * (quadraticPairKernel z.1 z.2 * D)) b)
  have heq : (quadraticSmallEnergy M N K v : ℂ) - quadraticSmallMomentCore M N K J v =
      quadraticGcdRemainder N v E := by
    rw [quadratic_small_moment_transform hM]
    unfold quadraticSmallMomentCore quadraticGcdRemainder E
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
  rw [heq]
  apply quadratic_gcd_remainder_bound N v E (by positivity)
  intro D hD z hz
  have hD₀ : 0 < D := (Finset.mem_Icc.mp hD).1
  have hz' := (Finset.mem_filter.mp hz).1
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hq₀ : 0 < quadraticPairKernel z.1 z.2 :=
    Nat.pos_of_ne_zero (quadraticPairKernel_squarefree
      (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
  have hmod : 0 < 2 * (quadraticPairKernel z.1 z.2 * D) := by positivity
  have : NeZero (2 * (quadraticPairKernel z.1 z.2 * D)) := ⟨Nat.ne_of_gt hmod⟩
  have hmod₁ : 2 * (quadraticPairKernel z.1 z.2 * D) ≠ 1 := by omega
  let T : ℝ := C * Real.sqrt M / J ^ A
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoint (b : ℕ) (hb : b ∈ (oddSquarefreeRange K).filter (D.Coprime ·)) :
      ‖(jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        ((∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
          (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
          quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) -
        quadraticSmallDyadicCore quadraticSieveWeight M b J
          (2 * (quadraticPairKernel z.1 z.2 * D)) b)‖ ≤ T := by
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
    have hh := hc M J (by exact_mod_cast hM) hJ _ hmod₁ b hb₀
    have hJac : ‖(jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy (b : ℤ) (quadraticPairKernel z.1 z.2) with h | h | h <;>
        rw [h] <;> norm_num
    rw [norm_mul]
    exact (mul_le_mul hJac hh (norm_nonneg _) zero_le_one).trans_eq (one_mul T)
  calc
    ‖E D z‖ ≤ ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = (((oddSquarefreeRange K).filter (D.Coprime ·)).card : ℝ) * T := by simp
    _ ≤ (K : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast (Finset.card_filter_le _ _).trans (oddSquarefreeRange_card_le K)
    _ = C * Real.sqrt M * K / J ^ A := by dsimp [T]; ring

end Ostmann

end OAI
