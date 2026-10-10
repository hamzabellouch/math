import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(IdealMobiusDivisorSum.primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C^n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(IdealMobiusDivisorSum.primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(IdealMobiusDivisorSum.primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C^n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

def radical (M : Ideal O) : Ideal O :=
  SmoothMobiusCorrection.primeProduct (SmoothMobiusCorrection.primeSet M)

theorem radical_ne_zero (M : Ideal O) : radical M ≠ 0 :=
  SmoothMobiusCorrection.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).card =
      (IdealMobiusDivisorSum.primeSupport M).card := by
  unfold SmoothMobiusCorrection.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : SmoothMobiusCorrection.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end SevenEighths.HeckeDeletionBounds

end

end OAI
