import Mathlib
import OAI.Computability.DirectedFeedback.Analysis.MatrixEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace DFVSGames.Decoder.PositiveMultiplier

section FiniteSpectra

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

theorem retained_mass_of_acceptance
    (w : J → ℝ) (a lam : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (23 : ℝ) / 25 ≤ cutoffEnergy w keep a := by
  classical
  have hp (j : J) (i : I j) :
      lam j i * a j i ^ 2 ≤ (7 / 8 : ℝ) * a j i ^ 2 +
        (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0) := by
    by_cases hk : keep j i
    · have h := mul_le_mul_of_nonneg_right (hone j i) (sq_nonneg (a j i))
      simp only [ite_eq_left hk] at *
      nlinarith
    · have h := mul_le_mul_of_nonneg_right (hhigh j i hk) (sq_nonneg (a j i))
      simpa only [ite_eq_right hk, mul_zero, add_zero] using h
  have hb : spectralEnergy w lam a ≤
      (7 / 8 : ℝ) * energy w a + (1 / 8 : ℝ) * cutoffEnergy w keep a := by
    calc
      _ ≤ ∑ j, w j * ∑ i, ((7 / 8 : ℝ) * a j i ^ 2 +
          (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0)) := by
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hp j i)) (hw j))
      _ = _ := by
        simp only [energy, cutoffEnergy, Finset.sum_add_distrib,
          Finset.mul_sum, mul_add]
        congr 1 <;>
          (apply Finset.sum_congr rfl
           intro j _
           apply Finset.sum_congr rfl
           intro i _
           ring)
  rw [htotal] at hb
  linarith

theorem positive_multiplier_comparison
    (w : J → ℝ) (a lam τ : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop) (t : ℝ)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1) (ht : 0 ≤ t)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (hτ : ∀ j i, 0 ≤ τ j i)
    (hlow : ∀ j i, keep j i → t ≤ τ j i)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (9 : ℝ) / 10 * t ≤ spectralEnergy w τ a := by
  classical
  have hmass := retained_mass_of_acceptance w a lam keep hw htotal hone hhigh haccept
  have hp (j : J) (i : I j) :
      t * (if keep j i then a j i ^ 2 else 0) ≤ τ j i * a j i ^ 2 := by
    by_cases hk : keep j i
    · simpa only [ite_eq_left hk] using
        mul_le_mul_of_nonneg_right (hlow j i hk) (sq_nonneg (a j i))
    · simpa only [ite_eq_right hk, mul_zero] using mul_nonneg (hτ j i) (sq_nonneg (a j i))
  have hb : t * cutoffEnergy w keep a ≤ spectralEnergy w τ a := by
    unfold cutoffEnergy spectralEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      t * (w j * ∑ i, if keep j i then a j i ^ 2 else 0) =
          w j * (∑ i, t * (if keep j i then a j i ^ 2 else 0)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hp j i)) (hw j)
  have hm := mul_le_mul_of_nonneg_left hmass ht
  nlinarith

theorem good_fiber_mass
    {Q : Type*} [Fintype Q] (μ p : Q → ℝ) (η : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hη : 0 ≤ η) (hp : ∀ q, p q ≤ 1)
    (hmean : (72 : ℝ) / 5 * η ≤ ∑ q, μ q * p q) :
    10 * η ≤ ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
  classical
  have hbound : (∑ q, μ q * p q) ≤
      4 * η + ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
    calc
      _ ≤ ∑ q, μ q * (4 * η + if 4 * η ≤ p q then 1 else 0) := by
        apply Finset.sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_left _ (hμ q)
        split_ifs with hq
        · linarith [hp q]
        · linarith
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
  linarith

end FiniteSpectra

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

def equalityAcceptance (ν : V → ℝ) (label : (E →ₗ[F2] V) → C) : ℝ := by
  classical
  exact 𝔼 X, ∑ v, ν v * (𝔼 l : E →ₗ[F2] F2,
    if label X = label (X + l.smulRight v) then (1 : ℝ) else 0)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 V] [Fintype V] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)] in
theorem color_pair_sum (label : (E →ₗ[F2] V) → C)
    (X Y : E →ₗ[F2] V) :
    (∑ c, colorIndicator label c X * colorIndicator label c Y) =
      if label X = label Y then (1 : ℝ) else 0 := by
  classical
  simp [colorIndicator, eq_comm]

theorem equalityAcceptance_fourier (ν : V → ℝ)
    (label : (E →ₗ[F2] V) → C) :
    equalityAcceptance ν label =
      ∑ c, ∑ S : V →ₗ[F2] E,
        linearNoiseEigenvalue ν S * linearCoeff (colorIndicator label c) S ^ 2 := by
  classical
  simp_rw [← linearRealNoiseOperator_energy]
  rw [← Finset.expect_sum_comm]
  unfold equalityAcceptance linearRealNoiseOperator
  apply Finset.expect_congr rfl
  intro X _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  calc
    ν v * (𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight v) then (1 : ℝ) else 0) =
      ν v * (𝔼 l : E →ₗ[F2] F2,
        ∑ c, colorIndicator label c X * colorIndicator label c (X + l.smulRight v)) := by
          simp only [color_pair_sum]
    _ = _ := by
      rw [Finset.expect_sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_expect]
      ring

theorem matrix_test_comparison
    (μ : Q → ℝ) (ν ρ : V → ℝ)
    (label : Q → (E →ₗ[F2] V) → C)
    (keep : (V →ₗ[F2] E) → Prop) (t : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hρ : ∀ v, 0 ≤ ρ v) (ht : 0 ≤ t)
    (hhigh : ∀ S : V →ₗ[F2] E, ¬ keep S → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (hlow : ∀ S : V →ₗ[F2] E, keep S → t ≤ linearNoiseEigenvalue ρ S)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * t ≤ ∑ q, μ q * equalityAcceptance ρ (label q) := by
  have hs (law : V → ℝ) :
      spectralEnergy (fun qc : Q × C => μ qc.1)
        (fun _ S => linearNoiseEigenvalue law S) (labelingCoeff label) =
          ∑ q, μ q * equalityAcceptance law (label q) := by
    simp only [spectralEnergy, labelingCoeff, Fintype.sum_prod_type,
      equalityAcceptance_fourier, Finset.mul_sum]
  rw [← hs] at haccept ⊢
  apply positive_multiplier_comparison
    (fun qc : Q × C => μ qc.1) (labelingCoeff label)
    (fun _ S => linearNoiseEigenvalue ν S)
    (fun _ S => linearNoiseEigenvalue ρ S) (fun _ S => keep S) t
  · exact fun qc => hμ qc.1
  · exact labelingCoeff_energy_one μ label hμsum
  · exact ht
  · exact fun _ S => linearNoiseEigenvalue_le_one ν S hν hνsum
  · exact fun _ S hS => hhigh S hS
  · exact fun _ S => linearNoiseEigenvalue_nonneg ρ S hρ
  · exact fun _ S hS => hlow S hS
  · exact haccept

end ActualMatrixTest

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

def subspaceLaw (ι : K →ₗ[F2] V) (v : V) : ℝ := by
  classical
  exact ∑ k, if ι k = v then (Fintype.card K : ℝ)⁻¹ else 0

omit [FiniteDimensional F2 K] [Fintype V] in
theorem subspaceLaw_nonneg (ι : K →ₗ[F2] V) (v : V) :
    0 ≤ subspaceLaw ι v := by
  classical
  unfold subspaceLaw
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_sum (ι : K →ₗ[F2] V) (f : V → ℝ) :
    (∑ v, subspaceLaw ι v * f v) = (Fintype.card K : ℝ)⁻¹ * ∑ k, f (ι k) := by
  classical
  unfold subspaceLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Finset.mul_sum _ _ _).symm

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_normalized (ι : K →ₗ[F2] V) :
    ∑ v, subspaceLaw ι v = 1 := by
  have h := subspaceLaw_sum ι (fun _ => 1)
  simpa [Fintype.card_ne_zero] using h

theorem subspaceLaw_eigenvalue (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E) :
    linearNoiseEigenvalue (subspaceLaw ι) S =
      ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun x : K => S (ι x) = 0).card
  have hs : (∑ x : K, if S (ι x) = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
      (Fintype.card K : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (DFVSGames.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, LinearMap.comp_apply] using h
  have hn : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold linearNoiseEigenvalue
  rw [subspaceLaw_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card K : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
        (Fintype.card K : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range) :=
      mul_assoc _ _ _
    _ = (Fintype.card K : ℝ)⁻¹ * (Fintype.card K : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range := (inv_mul_cancel₀ hp).symm

theorem subspaceLaw_eigenvalue_lower (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E)
    (r : ℕ) (hr : Module.finrank F2 (S.comp ι).range < r) :
    ((2 : ℝ) ^ r)⁻¹ ≤ linearNoiseEigenvalue (subspaceLaw ι) S := by
  rw [subspaceLaw_eigenvalue, ← one_div, ← one_div]
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hr)

end UniformSubspace

variable {Q C K E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

theorem matrix_spectral_comparison
    (μ : Q → ℝ) (ν : V → ℝ) (ι : K →ₗ[F2] V)
    (label : Q → (E →ₗ[F2] V) → C) (r : ℕ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hdetect : ∀ S : V →ₗ[F2] E,
      r ≤ Module.finrank F2 (S.comp ι).range → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ q, μ q * equalityAcceptance (subspaceLaw ι) (label q) := by
  apply matrix_test_comparison μ ν (subspaceLaw ι) label
    (fun S => Module.finrank F2 (S.comp ι).range < r) ((2 : ℝ) ^ r)⁻¹
    hμ hμsum hν hνsum (subspaceLaw_nonneg ι)
  · positivity
  · intro S hS
    exact hdetect S (Nat.le_of_not_gt hS)
  · intro S hS
    exact subspaceLaw_eigenvalue_lower ι S r hS
  · exact haccept

end DFVSGames.Decoder.PositiveMultiplier
end

noncomputable section

open scoped BigOperators

namespace DFVSGames.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

def codomainSplit : (E →ₗ[K] C × D) ≃ₗ[K] (E →ₗ[K] C) × (E →ₗ[K] D) :=
  (LinearMap.prodEquiv K).symm

def domainSplit : (C × D →ₗ[K] E) ≃ₗ[K] (C →ₗ[K] E) × (D →ₗ[K] E) :=
  (LinearMap.coprodEquiv K).symm

@[simp] theorem codomainSplit_symm_apply (X : E →ₗ[K] C) (Z : E →ₗ[K] D) :
    codomainSplit.symm (X, Z) = X.prod Z := rfl

@[simp] theorem domainSplit_symm_apply (S : C →ₗ[K] E) (T : D →ₗ[K] E) :
    domainSplit.symm (S, T) = S.coprod T := rfl

theorem expect_codomain_product
    [Fintype (E →ₗ[K] C × D)] [Fintype (E →ₗ[K] C)] [Fintype (E →ₗ[K] D)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (E →ₗ[K] C × D) → A) :
    (𝔼 X, f X) = 𝔼 (X : E →ₗ[K] C), 𝔼 (Z : E →ₗ[K] D), f (X.prod Z) := by
  classical
  rw [Fintype.expect_equiv codomainSplit.toEquiv f
    (fun p => f (p.1.prod p.2)) (by intro X; rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_domain_product
    [Fintype (C × D →ₗ[K] E)] [Fintype (C →ₗ[K] E)] [Fintype (D →ₗ[K] E)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (C × D →ₗ[K] E) → A) :
    (𝔼 S, f S) = 𝔼 (S : C →ₗ[K] E), 𝔼 (T : D →ₗ[K] E), f (S.coprod T) := by
  classical
  rw [Fintype.expect_equiv domainSplit.toEquiv f
    (fun p => f (p.1.coprod p.2)) (by
      intro S
      simp [domainSplit])]
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem sum_domain_product
    [Fintype (C × D →ₗ[K] E)] [Fintype (C →ₗ[K] E)] [Fintype (D →ₗ[K] E)]
    {A : Type*} [AddCommMonoid A]
    (f : (C × D →ₗ[K] E) → A) :
    (∑ S, f S) = ∑ (S : C →ₗ[K] E), ∑ (T : D →ₗ[K] E), f (S.coprod T) := by
  classical
  rw [← domainSplit.symm.toEquiv.sum_comp f]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rfl

end DFVSGames.Fourier.SplitMaps
end

namespace DFVSGames.Decoder.SurrogateFibers

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

omit [Fintype K] [Fintype W] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)] [Fintype (E →ₗ[F2] K × W)] in
theorem product_perturbation (M : E →ₗ[F2] K) (T : E →ₗ[F2] W)
    (l : E →ₗ[F2] F2) (a : K) :
    M.prod T + l.smulRight ((LinearMap.inl F2 K W) a) =
      (M + l.smulRight a).prod T := by
  ext x <;> simp

theorem surrogate_acceptance_eq_fiber_average
    (label : (E →ₗ[F2] K × W) → C) :
    equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 T : E →ₗ[F2] W,
        shortcodeAcceptance (fun M : E →ₗ[F2] K => label (M.prod T)) := by
  classical
  have hsampling : equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 X : E →ₗ[F2] K × W, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight ((LinearMap.inl F2 K W) a)) then
          (1 : ℝ) else 0 := by
    unfold equalityAcceptance
    apply Finset.expect_congr rfl
    intro X _
    rw [subspaceLaw_sum, Fintype.expect_eq_sum_div_card]
    ring
  rw [hsampling, SplitMaps.expect_codomain_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro T _
  unfold shortcodeAcceptance
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  rw [product_perturbation]

end
end DFVSGames.Decoder.SurrogateFibers

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Reduction.ActualSource
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

theorem expect_eq_uniform_sum {I : Type*} [Fintype I] (f : I → ℝ) :
    (𝔼 i, f i) = ∑ i, (Fintype.card I : ℝ)⁻¹ * f i := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
  ring

theorem eigenvalue_eq_kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] (S : Ambient s d →ₗ[F2] P) :
    linearNoiseEigenvalue (samplerLaw g.noise) S =
      (Integration.SplitGadget.kernelProbability g S : ℝ) := by
  rw [← sample_kernel_eq_eigenvalue]
  unfold Integration.SplitGadget.kernelProbability
  rw [rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

theorem acceptance_nested (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k, 𝔼 X : Map k s d, 𝔼 i : g.NoiseIndex, 𝔼 l : Dual k,
        if unfolded S k s d label (U, X) =
          unfolded S k s d label (U, X + l.smulRight (g.noise i))
        then (1 : ℝ) else 0 := by
  rw [acceptanceProbability_eq_test, rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]
  simp only [expect_prod, leftQuery, rightQuery, ActualGame.leftQuery, ActualGame.rightQuery]
  apply Finset.expect_congr rfl
  intro U _
  apply Finset.expect_congr rfl
  intro X _
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  by_cases h : unfolded S k s d label (U, X) =
      unfolded S k s d label (U, X + l.smulRight (g.noise i)) <;> simp [h]

theorem acceptance_eq_equality_mean (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k,
        equalityAcceptance (samplerLaw g.noise) (fun X : Map k s d =>
          unfolded S k s d label (U, X)) := by
  rw [acceptance_nested]
  apply Finset.expect_congr rfl
  intro U _
  unfold equalityAcceptance
  apply Finset.expect_congr rfl
  intro X _
  rw [← sample_expect_eq]
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  split_ifs <;> rfl

def fiberAcceptance (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) : ℝ :=
  shortcodeAcceptance (fun M : ActualHomogeneous.E k →ₗ[F2] Alphabet s =>
    unfolded S k s d label (U, M.prod T))

theorem fiberAcceptance_le_one (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) :
    fiberAcceptance S k s d label U T ≤ 1 := by
  unfold fiberAcceptance shortcodeAcceptance
  apply Finset.expect_le Finset.univ_nonempty
  intro M _
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le Finset.univ_nonempty
  intro l _
  split_ifs <;> norm_num

theorem weighted_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (μ : Question S k → ℝ) (r : Nat)
    (hμ : ∀ U, 0 ≤ μ U) (hμsum : ∑ U, μ U = 1)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ U, μ U *
      equalityAcceptance (samplerLaw g.noise)
        (fun X : Map k s d => unfolded S k s d label (U, X))) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ U, μ U * (𝔼 T, fiberAcceptance S k s d label U T) := by
  have h := matrix_spectral_comparison μ (samplerLaw g.noise) (alphabetEmbedding s d)
    (fun U (X : Map k s d) => unfolded S k s d label (U, X)) r
    hμ hμsum (samplerLaw_nonneg g.noise) (samplerLaw_normalized g.noise)
    (fun L hL => by
      rw [eigenvalue_eq_kernelProbability]
      have hc := (Rat.cast_le (K := ℝ)).mpr (hkernel L hL)
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hc) haccept
  simpa only [alphabetEmbedding, surrogate_acceptance_eq_fiber_average,
    fiberAcceptance] using h

theorem actual_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      𝔼 U : Question S k, 𝔼 T, fiberAcceptance S k s d label U T := by
  rw [expect_eq_uniform_sum]
  apply weighted_fiber_mean_lower S k g label
    (fun _ => (Fintype.card (Question S k) : ℝ)⁻¹) r
  · intro U
    positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply mul_inv_cancel₀
    exact_mod_cast Fintype.card_ne_zero (α := Question S k)
  · exact hkernel
  · have hc := (Rat.cast_le (K := ℝ)).mpr haccept
    rw [acceptance_eq_equality_mean, expect_eq_uniform_sum] at hc
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

def eta (r : Nat) : ℝ := ((2 : ℝ) ^ r)⁻¹ / 16

theorem eta_pos (r : Nat) : 0 < eta r := by unfold eta; positivity

theorem actual_good_fiber_mass (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    10 * eta r ≤ 𝔼 U : Question S k,
      𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
        if 4 * eta r ≤ fiberAcceptance S k s d label U T then (1 : ℝ) else 0 := by
  let I := Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)
  let μ : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹
  let p : I → ℝ := fun a => fiberAcceptance S k s d label a.1 a.2
  have hmean := actual_fiber_mean_lower S k g label r hkernel haccept
  have hmean' : (72 : ℝ) / 5 * eta r ≤ ∑ a, μ a * p a := by
    rw [← expect_eq_uniform_sum, expect_prod]

    unfold eta
    nlinarith
  have h := good_fiber_mass μ p (eta r) (fun _ => by positivity)
    (by simp [μ, Fintype.card_ne_zero]) (eta_pos r).le
    (fun a => fiberAcceptance_le_one S k s d label a.1 a.2) hmean'
  change 10 * eta r ≤
    ∑ a : Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d),
      (Fintype.card (Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)) : ℝ)⁻¹ *
        (if 4 * eta r ≤ fiberAcceptance S k s d label a.1 a.2 then 1 else 0) at h
  rw [← expect_eq_uniform_sum, expect_prod] at h
  exact h

end DFVSGames.Decoder.ActualSpectral
end

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators

noncomputable section

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

@[simp] theorem indicator_true : indicator True = 1 := by simp [indicator]
@[simp] theorem indicator_false : indicator False = 0 := by simp [indicator]

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  unfold indicator
  split <;> norm_num

theorem indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  classical
  unfold indicator
  split <;> norm_num

def uniformMass {X : Type*} [Fintype X] (p : X → Prop) : ℝ :=
  Finset.univ.expect fun x => indicator (p x)

theorem uniformMass_nonneg {X : Type*} [Fintype X] (p : X → Prop) :
    0 ≤ uniformMass p :=
  Finset.expect_nonneg fun x _ => indicator_nonneg (p x)

theorem uniformMass_le_one {X : Type*} [Fintype X] [Nonempty X]
    (p : X → Prop) : uniformMass p ≤ 1 :=
  Finset.expect_le Finset.univ_nonempty fun x _ => indicator_le_one (p x)

def replaceOn {X Y : Type*} (B : X → Prop) (f replacement : X → Y) : X → Y := by
  classical
  exact fun x => if B x then replacement x else f x

theorem replaceOn_of_not_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : ¬ B x) :
    replaceOn B f replacement x = f x := by
  simp [replaceOn, hx]

theorem replaceOn_of_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : B x) :
    replaceOn B f replacement x = replacement x := by
  simp [replaceOn, hx]

def equalityAcceptance {X Y E : Type*} [Fintype E]
    (left right : E → X) (f : X → Y) : ℝ :=
  uniformMass fun e => f (left e) = f (right e)

theorem acceptance_le_modified_add_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f g : X → Y)
    (unchanged : ∀ x, ¬ B x → f x = g x)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f ≤
      equalityAcceptance left right g + 2 * uniformMass B := by
  classical
  have pointwise : ∀ e : E,
      indicator (f (left e) = f (right e)) ≤
        indicator (g (left e) = g (right e)) +
          indicator (B (left e)) + indicator (B (right e)) := by
    intro e
    by_cases hl : B (left e)
    · have h₁ := indicator_le_one (f (left e) = f (right e))
      have h₂ := indicator_nonneg (g (left e) = g (right e))
      have h₃ := indicator_nonneg (B (right e))
      simp only [indicator, ite_eq_left hl] at *
      linarith
    · by_cases hr : B (right e)
      · have h₁ := indicator_le_one (f (left e) = f (right e))
        have h₂ := indicator_nonneg (g (left e) = g (right e))
        simp only [indicator, ite_eq_right hl, ite_eq_left hr] at *
        linarith
      · rw [unchanged _ hl, unchanged _ hr]
        simp [indicator, hl, hr]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun e _ => pointwise e)
  simp only [Finset.expect_add_distrib] at h
  change equalityAcceptance left right f ≤
    equalityAcceptance left right g + uniformMass (fun e => B (left e)) +
      uniformMass (fun e => B (right e)) at h
  rw [left_uniform, right_uniform] at h
  linarith

theorem acceptance_ge_original_sub_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f replacement : X → Y)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f - 2 * uniformMass B ≤
      equalityAcceptance left right (replaceOn B f replacement) := by
  have h := acceptance_le_modified_add_two_mass left right B f
    (replaceOn B f replacement)
    (fun x hx => (replaceOn_of_not_mem B f replacement hx).symm)
    left_uniform right_uniform
  linarith

def goodUnion {A X : Type*} (good : A → X → Prop) (x : X) : Prop :=
  ∃ a, good a x

def adviceMass {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : ℝ :=
  Finset.univ.expect fun x => uniformMass fun a => good a x

theorem adviceMass_nonneg {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : 0 ≤ adviceMass good :=
  Finset.expect_nonneg fun x _ => uniformMass_nonneg (fun a => good a x)

theorem union_mass_le_card_mul_adviceMass
    {A X : Type*} [Fintype A] [Fintype X] (good : A → X → Prop) :
    uniformMass (goodUnion good) ≤ (Fintype.card A : ℝ) * adviceMass good := by
  classical
  have pointwise : ∀ x : X, indicator (goodUnion good x) ≤
      (Fintype.card A : ℝ) * uniformMass (fun a => good a x) := by
    intro x
    rw [uniformMass, Fintype.card_mul_expect]
    by_cases hx : goodUnion good x
    · obtain ⟨a, ha⟩ := hx
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset A)) (f := fun a => indicator (good a x))
        (fun a _ => indicator_nonneg (good a x)) (Finset.mem_univ a)
      simpa [indicator, ha, goodUnion, show ∃ a, good a x from ⟨a, ha⟩] using h
    · simp only [indicator, ite_eq_right hx]
      exact Finset.sum_nonneg fun a _ => indicator_nonneg (good a x)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun x _ => pointwise x)
  simpa only [uniformMass, adviceMass, ← Finset.mul_expect] using h

theorem adviceMass_ge_union_div_card
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) :
    uniformMass (goodUnion good) / (Fintype.card A : ℝ) ≤ adviceMass good := by
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  simpa [mul_comm] using union_mass_le_card_mul_adviceMass good

theorem adviceMass_ge_of_union_mass
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) (η : ℝ) (hη : η ≤ uniformMass (goodUnion good)) :
    η / (Fintype.card A : ℝ) ≤ adviceMass good := by
  exact (div_le_div_of_nonneg_right hη (Nat.cast_nonneg _)).trans
    (adviceMass_ge_union_div_card good)

end
end DFVSGames.Inverse.RowErasure

end OAI
