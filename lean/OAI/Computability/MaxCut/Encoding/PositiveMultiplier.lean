import Mathlib
import OAI.Computability.MaxCut.Games.PartnerProjection
import OAI.Computability.MaxCut.Games.MatrixNoise
import OAI.Computability.MaxCut.Games.RankAdditivity

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace MaxCutGames.Decoder.PositiveMultiplier

section FiniteSpectra

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

/-- A `7/8` bound outside the retained set forces at least `0.92` retained
mass when acceptance is at least `0.99`.  The statement keeps the exact
rational constants, rather than assuming a low-rank mass premise. -/
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

/-- A finite probability law with mean at least `14.4 η` assigns mass at
least `10 η` to acceptances at least `4 η`. -/
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

/-- The actual equality test, including zero perturbation factors. -/
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

/-- Equality acceptance has the actual positive Fourier multiplier.  Color
indicators give the same equality expansion as output characters, with no
extra factor depending on the output alphabet. -/
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

/-- Spectral comparison applied to a genuine family of matrix labelings.
The two explicit probability laws may be the latent gadget law and uniform
sampling in the distinguished subspace, respectively. -/
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

/-- Pushforward of uniform sampling in `K`.  For a subspace inclusion this
is uniform sampling in that subspace; the definition also permits a linear
map with nontrivial fibers without accidentally conditioning on nonzero vectors. -/
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
      (MaxCutGames.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
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

end MaxCutGames.Decoder.PositiveMultiplier
end

end OAI
