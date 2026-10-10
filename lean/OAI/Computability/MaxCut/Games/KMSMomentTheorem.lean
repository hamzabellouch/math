import Mathlib
import OAI.Computability.MaxCut.Machines.RuntimeSpace
import OAI.Computability.MaxCut.Encoding.PositiveMultiplier
import OAI.Computability.MaxCut.Games.A5Induction
import OAI.Computability.MaxCut.Games.KMSBasisComparisonPseudorandomTupleMap

namespace OAI

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace MaxCutGames.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

/-- The upper moment has a constant depending only on the cutoff. Its tuple
budget is 2r and its domain threshold is r, both fixed before the dimensions. -/
theorem lifted_fourth_moment_bound
    (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
    (i : ℕ) (hi : i ≤ r) :
    (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
      fourthMomentConstant r *
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε := by
  have hf := liftedIndicator_basisInvariant S
  have hd : AffineDensityBound i ε (liftedIndicator S) :=
    AffineDensityBound.mono hi ε (liftedIndicator S)
      (KMSBasisComparisonAffineDensity.lifted_affineDensityBound_of_tuple S hS)
  have hidim : i ≤ Module.finrank F2 (Ambient ell) := by
    simpa [KMS.Ambient] using hi.trans hell
  have hm := rankComponent_fourth_moment_le_of_hybrid i (liftedIndicator S)
    (mixedRankConstant i * ε) (mul_nonneg (mixedRankConstant_nonneg i) hε)
    (by
      intro A B T _
      have hh := KMSAnalyticHybridEnergy.hybridDerivative_energy_bound
        i ε hε (liftedIndicator S) hf hd hidim A B T
      have hp : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient ell) (W := Ambient n) = basisMapFintype n ell :=
        Subsingleton.elim _ _
      have hq : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient n) (W := Ambient ell) = basisMapFintype ell n :=
        Subsingleton.elim _ _
      rw [hp, hq] at hh
      exact hh)
  exact hm.trans (a5_mixed_bound hi ε _ hε
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)))

end
end MaxCutGames.Inverse.KMSMomentTheorem

namespace MaxCutGames.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

def IsBoolean (f : X → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

omit [Fintype X] in
theorem boolean_nonneg {f : X → ℝ} (hf : IsBoolean f) (x : X) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype X] in
theorem boolean_sq {f : X → ℝ} (hf : IsBoolean f) (x : X) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_average_nonneg {f : X → ℝ} (hf : IsBoolean f) : 0 ≤ 𝔼 x, f x :=
  Finset.expect_nonneg fun x _ => boolean_nonneg hf x

theorem boolean_squared_average {f : X → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  exact boolean_sq hf x

/-- Two finite Cauchy–Schwarz steps, with the Boolean support kept explicitly. -/
theorem boolean_fourth_holder {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ) :
    (𝔼 x, g x * f x) ^ 4 ≤ (𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have h₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => g x * f x) f
  have hleft : (𝔼 x, (g x * f x) * f x) = 𝔼 x, g x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = g x * f x ^ 2 := by ring
      _ = _ := by rw [boolean_sq hf]
  have hright : (𝔼 x, (g x * f x) ^ 2) = 𝔼 x, g x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [hleft, hright, boolean_squared_average hf] at h₁
  have h₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => g x ^ 2) f
  have hpow : (𝔼 x, (g x ^ 2) ^ 2) = 𝔼 x, g x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hpow, boolean_squared_average hf] at h₂
  have hδ := boolean_average_nonneg hf
  have hweighted : 0 ≤ 𝔼 x, g x ^ 2 * f x :=
    Finset.expect_nonneg fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x)
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, g x * f x)) h₁
  have hscaled := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The squared norm of an orthogonal component is bounded by the Boolean
function's density. The projection identity is the only needed property. -/
theorem projection_energy_le_density {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ≤ 𝔼 x, f x := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ g f
  rw [← hprojection, boolean_squared_average hf] at h
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ := boolean_average_nonneg hf
  nlinarith

/-- A stronger lower fourth-moment estimate than KMS Lemma 2.14, avoiding
division by the density and remaining valid at density zero. -/
theorem projection_fifth_le_density_fourth_moment {f : X → ℝ} (hf : IsBoolean f)
    (g : X → ℝ) (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ^ 5 ≤ (𝔼 x, f x) ^ 4 * (𝔼 x, g x ^ 4) := by
  have hholder := boolean_fourth_holder hf g
  rw [← hprojection] at hholder
  have hηδ := projection_energy_le_density hf g hprojection
  have hδ := boolean_average_nonneg hf
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hηδ (pow_nonneg hη 4)
  have hscale := mul_le_mul_of_nonneg_right hholder hδ
  calc
    _ ≤ (𝔼 x, g x ^ 2) ^ 4 * (𝔼 x, f x) := by nlinarith only [hmul]
    _ ≤ ((𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3) * (𝔼 x, f x) := hscale
    _ = _ := by ring

theorem fourth_root_power {ε : ℝ} (hε : 0 ≤ ε) :
    (ε ^ ((1 : ℝ) / 4)) ^ 4 = ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε]
  norm_num

theorem le_of_fourth_power_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  have := pow_lt_pow_left₀ hlt hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) this

theorem lowLevel_bound_of_fourthMoment {f : X → ℝ} (hf : IsBoolean f)
    (g : X → ℝ) (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x)
    (hupper : (𝔼 x, g x ^ 4) ≤
      (2 : ℝ) ^ (25 * r ^ 3) * (𝔼 x, g x ^ 2) * ε) :
    (𝔼 x, g x ^ 2) ≤
      (2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4) * (𝔼 x, f x) := by
  let η : ℝ := 𝔼 x, g x ^ 2
  let δ : ℝ := 𝔼 x, f x
  have hη : 0 ≤ η := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ : 0 ≤ δ := boolean_average_nonneg hf
  have hlow := projection_fifth_le_density_fourth_moment hf g hprojection
  change η ^ 5 ≤ δ ^ 4 * (𝔼 x, g x ^ 4) at hlow
  have hupper' := mul_le_mul_of_nonneg_left hupper (pow_nonneg hδ 4)
  have hsmall : η ^ 4 ≤ (2 : ℝ) ^ (25 * r ^ 3) * ε * δ ^ 4 := by
    by_cases hz : η = 0
    · simpa only [hz, zero_pow (by decide : (4 : ℕ) ≠ 0)] using
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hε)
          (pow_nonneg hδ 4)
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hηpos).mp
      nlinarith only [hlow, hupper']
  have hexponent : 25 * r ^ 3 ≤ (7 * r ^ 3 + 3) * 4 := by omega
  have hconstant : (2 : ℝ) ^ (25 * r ^ 3) ≤
      ((2 : ℝ) ^ (7 * r ^ 3 + 3)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hexponent
  apply le_of_fourth_power_le hη (by positivity)
  calc
    η ^ 4 ≤ (2 : ℝ) ^ (25 * r ^ 3) * ε * δ ^ 4 := hsmall
    _ ≤ ((2 : ℝ) ^ (7 * r ^ 3 + 3)) ^ 4 * ε * δ ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hε) (pow_nonneg hδ 4)
    _ = _ := by rw [mul_pow, mul_pow, fourth_root_power hε]

end
end MaxCutGames.Inverse.KMSMomentScalar

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace MaxCutGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixNoise
open MaxCutGames.Decoder.PositiveMultiplier
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

def rankEnergy (rank : I → ℕ) (a : I → ℝ) (i : ℕ) : ℝ :=
  ∑ s, if rank s = i then a s ^ 2 else 0

theorem sum_rankEnergy (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) =
      ∑ s, if rank s ≤ r then a s ^ 2 else 0 := by
  unfold rankEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rank s ≤ r
  · simp [eq_comm, Finset.mem_range, hs]
  · simp [eq_comm, Finset.mem_range, hs]

/-- Exact rank multiplier cutoff, without dimension-dependent constants. -/
theorem spectral_cutoff (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) +
        ((2 : ℝ) ^ (r + 1))⁻¹ * ∑ s, a s ^ 2 := by
  rw [sum_rankEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have ht : 0 ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * a s ^ 2 := by positivity
  by_cases hs : rank s ≤ r
  · rw [ite_eq_left hs]
    have hinv : ((2 : ℝ) ^ rank s)⁻¹ ≤ 1 := by
      rw [← one_div]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hm := mul_le_mul_of_nonneg_right hinv (sq_nonneg (a s))
    nlinarith
  · rw [ite_eq_right hs, zero_add]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (a s))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem spectral_cutoff_of_level_bounds (rank : I → ℕ) (a : I → ℝ)
    (r : ℕ) (C δ : ℝ) (htotal : (∑ s, a s ^ 2) = δ)
    (hlevels : ∀ i ≤ r, rankEnergy rank a i ≤ C * δ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      ((r + 1 : ℕ) * C + ((2 : ℝ) ^ (r + 1))⁻¹) * δ := by
  have hsum : (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) ≤
      (r + 1 : ℕ) * C * δ := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), C * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlevels i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = _ := by simp; ring
  have hcut := spectral_cutoff rank a r
  rw [htotal] at hcut
  nlinarith only [hcut, hsum]
end FiniteCutoff

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual operator samples both rank-one factors uniformly, including zero. -/
def uniformNoise (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  linearRealNoiseOperator (subspaceLaw (LinearMap.id : F →ₗ[F2] F)) f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniformNoise_apply (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    uniformNoise f X = 𝔼 v : F, 𝔼 l : E →ₗ[F2] F2, f (X + l.smulRight v) := by
  unfold uniformNoise linearRealNoiseOperator
  rw [subspaceLaw_sum]
  simp only [LinearMap.id_apply, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  ring

theorem uniformNoise_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * uniformNoise f X) =
      ∑ S : F →ₗ[F2] E, ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        linearCoeff f S ^ 2 := by
  unfold uniformNoise
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [subspaceLaw_eigenvalue, LinearMap.comp_id]

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
theorem rankEnergy_eq (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    rankEnergy (fun S : F →ₗ[F2] E => Module.finrank F2 S.range)
      (linearCoeff f) i = 𝔼 X, rankComponent i f X ^ 2 := by
  rw [rankComponent_energy, Finset.sum_filter]
  rfl

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
/-- The scalar fourth-moment argument applied to genuine rank projections. -/
theorem rankComponent_bound (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hupper : (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (25 * r ^ 3) * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, rankComponent i f X ^ 2) ≤
      (2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4) * (𝔼 X, f X) := by
  apply lowLevel_bound_of_fourthMoment hf (rankComponent i f) r ε hε _ hupper
  exact (component_inner_self _ f).symm

/-- The KMS spectral conclusion once the actual pseudorandom upper fourth
moments have been proved. The error, cutoff and constants precede dimensions. -/
theorem uniformNoise_bound_of_fourthMoments (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBoolean f) (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (25 * r ^ 3) * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    exact rankComponent_bound f hf r i ε hε (hupper i hi)

end
end MaxCutGames.Inverse.KMSLowLevel

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

namespace MaxCutGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open KMSMomentScalar KMSAnalytic
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

/-- No particular polynomial in the cutoff is required for the scalar step. -/
theorem projection_bound_of_general_fourthMoment {X : Type*} [Fintype X]
    {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x)
    (hupper : (𝔼 x, g x ^ 4) ≤ C * (𝔼 x, g x ^ 2) * ε) :
    (𝔼 x, g x ^ 2) ≤ (C + 1) * ε ^ ((1 : ℝ) / 4) * (𝔼 x, f x) := by
  let η : ℝ := 𝔼 x, g x ^ 2
  let δ : ℝ := 𝔼 x, f x
  have hη : 0 ≤ η := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ : 0 ≤ δ := boolean_average_nonneg hf
  have hlow := projection_fifth_le_density_fourth_moment hf g hprojection
  change η ^ 5 ≤ δ ^ 4 * (𝔼 x, g x ^ 4) at hlow
  have hupper' := mul_le_mul_of_nonneg_left hupper (pow_nonneg hδ 4)
  have hsmall : η ^ 4 ≤ C * ε * δ ^ 4 := by
    by_cases hz : η = 0
    · simpa only [hz, zero_pow (by decide : (4 : ℕ) ≠ 0)] using
        mul_nonneg (mul_nonneg hC hε) (pow_nonneg hδ 4)
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hηpos).mp
      nlinarith only [hlow, hupper']
  have hconstant : C ≤ (C + 1) ^ 4 := by
    nlinarith [sq_nonneg C, pow_nonneg hC 3, pow_nonneg hC 4]
  apply le_of_fourth_power_le hη (by positivity)
  calc
    η ^ 4 ≤ C * ε * δ ^ 4 := hsmall
    _ ≤ (C + 1) ^ 4 * ε * δ ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hε) (pow_nonneg hδ 4)
    _ = _ := by rw [mul_pow, mul_pow, fourth_root_power hε]

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual full-uniform rank-one correlation, with a general moment constant. -/
theorem uniformNoise_bound_of_general_fourthMoments
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      C * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((C + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    apply projection_bound_of_general_fourthMoment hf (rankComponent i f)
      C ε hC hε _ (hupper i hi)
    exact (component_inner_self _ f).symm
end ActualFourier

/-- Even an arbitrarily large constant depending on r alone permits the
cutoff and tolerance to be chosen before both dimensions. -/
theorem exists_general_cutoff_parameters (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹ ≤ ζ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ζ / 4 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  let r := max 1 N
  let D : ℝ := C r + 1
  let t : ℝ := min 1 (ζ / (4 * (r + 1 : ℕ) * D))
  let ε : ℝ := t ^ 4
  have hD : 0 < D := by dsimp [D]; linarith [hC r]
  have hr : 1 ≤ r := le_max_left _ _
  have hden : 0 < 4 * (r + 1 : ℕ) * D := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hζ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hε : 0 < ε := pow_pos ht _
  have hε1 : ε ≤ 1 := pow_le_one₀ ht.le ht1
  have hroot : ε ^ ((1 : ℝ) / 4) = t := by
    have hpow : (ε ^ ((1 : ℝ) / 4)) ^ 4 = t ^ 4 := fourth_root_power hε.le
    have hn : 0 ≤ ε ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hε.le _
    exact le_antisymm (le_of_fourth_power_le hn ht.le hpow.le)
      (le_of_fourth_power_le ht.le hn hpow.symm.le)
  have hlow : (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) ≤ ζ / 4 := by
    rw [hroot]
    have ht' : t ≤ ζ / (4 * (r + 1 : ℕ) * D) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp ht'
    nlinarith only [hm]
  have htail : ((2 : ℝ) ^ (r + 1))⁻¹ < ζ / 4 := by
    have hmon : (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right 1 N) (Nat.le_succ r))
    simpa only [one_div, inv_pow] using hmon.trans_lt hN
  refine ⟨r, hr, ε, hε, hε1, ?_⟩
  change (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) + _ ≤ ζ / 2
  linarith

end
end MaxCutGames.Inverse.KMSLowLevel

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
/-- Finset conditioning and uniform sampling from its membership subtype are
the same normalized finite sum, including the empty event. -/
theorem expect_coe_eq (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x : s, f x.val) = s.expect f := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, Finset.sum_coe_sort]

omit [Fintype Ω] in
theorem expect_unit_interval (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ s.expect f ∧ s.expect f ≤ 1 := by
  refine ⟨Finset.expect_nonneg (fun x _ => hf0 x), ?_⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · exact Finset.expect_le hs (fun x _ => hf1 x)

/-- The weighted conditional expectation is the unnormalized sum divided by
the ambient cardinality, also for an empty conditioning event. -/
theorem mass_mul_expect (s : Finset Ω) (f : Ω → ℝ) :
    (s.card : ℝ) / Fintype.card Ω * s.expect f =
      (∑ x ∈ s, f x) / Fintype.card Ω := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [Finset.expect_eq_sum_div_card]
    have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
    by_cases hN : (Fintype.card Ω : ℝ) = 0
    · simp [hN]
    · field_simp

/-- Exact two-event total expectation, with the same zero convention on both
conditional expectations as mathlib's finite expectation. -/
theorem expect_partition (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x, f x) =
      (s.card : ℝ) / Fintype.card Ω * s.expect f +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω *
        (Finset.univ \ s).expect f := by
  rw [mass_mul_expect, mass_mul_expect, ← add_div, Fintype.expect_eq_sum_div_card]
  congr 1
  exact (Finset.sum_sdiff (Finset.subset_univ s)).symm.trans (add_comm _ _)

/-- Conditioning a bounded function changes its expectation by at most the
discarded probability mass. No independence assumption is used here. -/
theorem abs_expect_sub_restrict_le [Nonempty Ω] (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(𝔼 x, f x) - s.expect f| ≤
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by
  have hB := expect_unit_interval s f hf0 hf1
  have hC := expect_unit_interval (Finset.univ \ s) f hf0 hf1
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (s.card : ℝ) / Fintype.card Ω +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω = 1 := by
    rw [← add_div]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcast : ((Finset.univ \ s).card : ℝ) + (s.card : ℝ) =
        Fintype.card Ω := by exact_mod_cast hc.trans (Finset.card_univ)
    rw [add_comm, hcast, div_self hN]
  have hq : 0 ≤ ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by positivity
  have hp : (s.card : ℝ) / Fintype.card Ω =
      1 - ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by linarith
  rw [expect_partition]
  rw [hp]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hB.2)]
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hC.2)]

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev Functional (ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.F2

instance functionalFinite (ell : ℕ) : Finite (Functional ell) :=
  Finite.of_injective (fun a : Functional ell => (a : KMS.Ambient ell → KMS.F2))
    DFunLike.coe_injective

instance functionalFintype (ell : ℕ) : Fintype (Functional ell) := Fintype.ofFinite _

theorem card_functional (ell : ℕ) : Fintype.card (Functional ell) = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2)]
  change Fintype.card (ZMod 2) ^ Module.finrank KMS.F2 (Module.Dual KMS.F2
    (KMS.Ambient ell)) = _
  rw [Subspace.dual_finrank_eq]
  simp [KMS.Ambient, KMS.F2]

theorem card_ambient (n : ℕ) : Fintype.card (KMS.Ambient n) = 2 ^ n := by
  simp [KMS.Ambient, KMS.F2]

/-- Actual good pairs in the unconditioned product sample space. -/
def goodParameters {n ell : ℕ} (X : BasisMap n ell) :
    Finset (Functional ell × KMS.Ambient n) :=
  (Finset.univ.filter (fun a : Functional ell => a ≠ 0)) ×ˢ
    (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range))

@[simp] theorem mem_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (p : Functional ell × KMS.Ambient n) :
    p ∈ goodParameters X ↔ p.1 ≠ 0 ∧ p.2 ∉ X.range := by
  simp [goodParameters]

theorem card_range {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    Fintype.card X.range = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2), LinearMap.finrank_range_of_inj hX]
  simp [KMS.Ambient, KMS.F2]

/-- The exact good-event count, including the zero-dimensional boundary. -/
theorem card_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (goodParameters X).card = (2 ^ ell - 1) * (2 ^ n - 2 ^ ell) := by
  rw [goodParameters, Finset.card_product]
  have ha : (Finset.univ.filter (fun a : Functional ell => a ≠ 0)).card =
      2 ^ ell - 1 := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_functional]
    simp
  have hy : (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range)).card =
      2 ^ n - 2 ^ ell := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_ambient]
    rw [card_range X hX]
  rw [ha, hy]

/-- Exceptional mass is bounded by the sum of the two factor exceptions. -/
theorem badParameters_mass_le {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    1 - ((goodParameters X).card : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hcard : 2 ^ ell ≤ 2 ^ n := by
    rw [← card_ambient ell, ← card_ambient n]
    exact Fintype.card_le_of_injective X hX
  have hone : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by decide)
  rw [card_goodParameters X hX, Fintype.card_prod, card_functional, card_ambient]
  push_cast [Nat.cast_sub hone, Nat.cast_sub hcard]
  have he : (0 : ℝ) < 2 ^ ell := pow_pos (by norm_num) _
  have hn : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  field_simp
  nlinarith

/-- The same estimate in the complement-cardinality form used for deleting
the bad event from a finite expectation. -/
theorem badParameters_mass_le_compl {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (((Finset.univ \ goodParameters X).card : ℕ) : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have ht : (0 : ℝ) < Fintype.card (Functional ell × KMS.Ambient n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsub := Finset.card_le_card (Finset.subset_univ (goodParameters X))
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub hsub,
    Finset.card_univ, sub_div, div_self (ne_of_gt ht)]
  exact badParameters_mass_le X hX

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- One-dimensional vector subspaces. -/
abbrev Lines (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {L : Submodule K E // finrank K L = 1}

/-- Hyperplanes, expressed without truncated dimension subtraction. -/
abbrev Hyperplanes (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {H : Submodule K E // finrank K H + 1 = finrank K E}

/-- Dual annihilation bijects hyperplanes with lines in the dual space. -/
noncomputable def hyperplanesEquivDualLines [FiniteDimensional K E] :
    Hyperplanes K E ≃ Lines K (Module.Dual K E) where
  toFun H := ⟨H.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq H.val
    have hH := H.property
    omega⟩
  invFun L := ⟨L.val.dualCoannihilator, by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq L.val
    rw [L.property] at h
    omega⟩
  left_inv H := by
    apply Subtype.ext
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv L := by
    apply Subtype.ext
    exact Subspace.dualCoannihilator_dualAnnihilator_eq

theorem card_lines_binary [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] :
    Nat.card (Lines (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  classical
  let spanMap : {v : E // v ≠ 0} → Lines (ZMod 2) E := fun v =>
    ⟨Submodule.span (ZMod 2) {v.val}, finrank_span_singleton v.property⟩
  have hinj : Function.Injective spanMap := by
    intro v w h
    have hv : v.val ∈ Submodule.span (ZMod 2) {w.val} := by
      have hs : Submodule.span (ZMod 2) {v.val} =
          Submodule.span (ZMod 2) {w.val} := congrArg Subtype.val h
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · exact False.elim (v.property (by simpa [hc0] using hc.symm))
    · exact Subtype.ext (by simpa [hc1] using hc.symm)
  have hsurj : Function.Surjective spanMap := by
    intro L
    obtain ⟨v, hv0, _⟩ := (finrank_eq_one_iff').mp L.property
    have hv : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one L.property v.property hv).symm
  let e : {v : E // v ≠ 0} ≃ Lines (ZMod 2) E := Equiv.ofBijective spanMap ⟨hinj, hsurj⟩
  let coords : E ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) E) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let : Finite E := Finite.of_equiv _ coords.symm.toEquiv
  let : Fintype E := Fintype.ofFinite E
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem card_hyperplanes_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] :
    Nat.card (Hyperplanes (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  rw [Nat.card_congr (hyperplanesEquivDualLines (K := ZMod 2) (E := E)),
    card_lines_binary, Subspace.dual_finrank_eq]

/-- A dimension identity for the quotient correspondence, retaining addition. -/
theorem finrank_map_mkQ_add [FiniteDimensional K E]
    (H W : Submodule K E) (hHW : H ≤ W) :
    finrank K (W.map H.mkQ) + finrank K H = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.mkQ.comp W.subtype)
  have hr : LinearMap.range (H.mkQ.comp W.subtype) = W.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (H.mkQ.comp W.subtype) = H.comap W.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq] at h
  exact h

/-- One-dimensional extensions of a subspace. -/
abbrev Extensions (H : Submodule K E) :=
  {W : Submodule K E // H ≤ W ∧ finrank K W = finrank K H + 1}

/-- The quotient correspondence identifies extensions with quotient lines. -/
noncomputable def extensionsEquivLines [FiniteDimensional K E]
    (H : Submodule K E) : Extensions H ≃ Lines K (E ⧸ H) where
  toFun W := ⟨W.val.map H.mkQ, by
    have h := finrank_map_mkQ_add H W.val W.property.1
    rw [W.property.2] at h
    omega⟩
  invFun L := ⟨L.val.comap H.mkQ, Submodule.le_comap_mkQ H L.val, by
    have h := finrank_map_mkQ_add H (L.val.comap H.mkQ)
      (Submodule.le_comap_mkQ H L.val)
    have heq : (L.val.comap H.mkQ).map H.mkQ = L.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [heq, L.property] at h
    omega⟩
  left_inv W := by
    apply Subtype.ext
    simp [Submodule.comap_map_mkQ, sup_eq_right.mpr W.property.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

theorem card_extensions_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (H : Submodule (ZMod 2) E) :
    Nat.card (Extensions H) = 2 ^ finrank (ZMod 2) (E ⧸ H) - 1 := by
  rw [Nat.card_congr (extensionsEquivLines H), card_lines_binary]

end MaxCutGames.Inverse.MatrixChart

end OAI
