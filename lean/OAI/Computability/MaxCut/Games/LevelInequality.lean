import Mathlib
import OAI.Computability.MaxCut.Games.A4IndexCount

namespace OAI

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

namespace MaxCutGames.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsBoolean (f : α → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

omit [Fintype α] in
theorem boolean_nonneg {f : α → ℝ} (hf : IsBoolean f) (x : α) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype α] in
theorem boolean_sq {f : α → ℝ} (hf : IsBoolean f) (x : α) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

theorem boolean_four_thirds_moment {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, |f x| ^ ((4 : ℝ) / 3)) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> norm_num [h]

theorem boolean_holder_fourth {f : α → ℝ} (hf : IsBoolean f) (h : α → ℝ) :
    (𝔼 x, h x * f x) ^ 4 ≤ (𝔼 x, h x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have hfirst := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x * f x) f
  have eleft : (𝔼 x, (h x * f x) * f x) = 𝔼 x, h x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = h x * (f x ^ 2) := by ring
      _ = _ := by rw [boolean_sq hf]
  have eright : (𝔼 x, (h x * f x) ^ 2) = 𝔼 x, h x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [eleft, eright, boolean_squared_norm_eq_density hf] at hfirst
  have hsecond := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x ^ 2) f
  have epow : (𝔼 x, (h x ^ 2) ^ 2) = 𝔼 x, h x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [epow, boolean_squared_norm_eq_density hf] at hsecond
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hweighted : 0 ≤ 𝔼 x, h x ^ 2 * f x :=
    Finset.expect_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x))
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, h x * f x)) hfirst
  have hscaled := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The fourth-root conversion used in the final displayed inequality.
This is an elementary real estimate, independent of Fourier analysis. -/
theorem fourth_power_le_implies_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hpow : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hba hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) hpow

/-- Once the genuine fourth-moment estimate has been established, this
proves the final Boolean Hölder implication. The fourth-moment estimate is
an explicit hypothesis here; this lemma itself is not Theorem 2.3. -/
theorem boolean_level_bound_of_fourth_moment {f h : α → ℝ}
    (hf : IsBoolean f) (d : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hprojection : (𝔼 x, h x ^ 2) = 𝔼 x, h x * f x)
    (hfourth : (𝔼 x, h x ^ 4) ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x)) :
    (𝔼 x, h x ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 x, f x ^ 2) := by
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hh : 0 ≤ 𝔼 x, h x ^ 2 := Finset.expect_nonneg (fun x _ => sq_nonneg _)
  have hηroot : 0 ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hη _
  have hroot : (η ^ ((1 : ℝ) / 4)) ^ 4 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
    norm_num
  have hslack : 113 * d * d ≤ (30 * d * d) * 4 := by
    calc
      113 * d * d = 113 * (d * d) := by ring
      _ ≤ 120 * (d * d) := Nat.mul_le_mul_right _ (by decide)
      _ = (30 * d * d) * 4 := by ring
  have htwo : (2 : ℝ) ^ (113 * d * d) ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hslack
  have hholder := boolean_holder_fourth hf h
  rw [← hprojection] at hholder
  have hscale := mul_le_mul_of_nonneg_right hfourth (pow_nonneg hμ 3)
  have hlarge := mul_le_mul_of_nonneg_right htwo (mul_nonneg hη (pow_nonneg hμ 4))
  rw [boolean_squared_norm_eq_density hf]
  apply fourth_power_le_implies_le hh
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hηroot) hμ)
  calc
    _ ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hholder, hscale]
    _ ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hlarge]
    _ = _ := by rw [mul_pow, mul_pow, hroot]

end MaxCutGames.Appendix.LevelInequality

noncomputable section

namespace MaxCutGames.Appendix.LevelInequality

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual rank of a Fourier index `S : F → E`. -/
def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

def rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S with frequencyRank S = d,
    linearCoeff f S • (fun X => (linearTraceCharacter S X).re)

theorem linearCoeff_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (rankLevel d f) S = if frequencyRank S = d then linearCoeff f S else 0 := by
  classical
  unfold rankLevel
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- The selected rank mass equals the normalized squared norm of the actual
rank projection. -/
theorem rankLevel_energy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) =
      ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  classical
  rw [← linear_parseval]
  simp only [linearCoeff_rankLevel]
  simp [Finset.sum_filter]

/-- Orthogonal-projection identity used in the final Hölder step. -/
theorem rankLevel_inner_self (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) = 𝔼 X, rankLevel d f X * f X := by
  classical
  rw [← linear_parseval, ← linear_parseval_inner]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankLevel]
  split_ifs <;> ring

/-- Rank projection contracts the normalized L2 norm. -/
theorem rankLevel_energy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankLevel_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => sq_nonneg _)

theorem rankLevel_degree_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : d < frequencyRank S) :
    linearCoeff (rankLevel d f) S = 0 := by
  rw [linearCoeff_rankLevel, ite_eq_right (Nat.ne_of_gt hS)]

theorem rankLevel_bound_of_fourth_moment (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (η : ℝ) (hη : 0 ≤ η)
    (hfourth : (𝔼 X, rankLevel d f X ^ 4) ≤
      (2 : ℝ) ^ (113 * d * d) * η * (𝔼 X, f X)) :
    (𝔼 X, rankLevel d f X ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2) :=
  boolean_level_bound_of_fourth_moment hf d η hη (rankLevel_inner_self d f) hfourth

variable [Finite E] [Finite F]

def IsRestrictionGlobal (f : (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
    MaxCutGames.Fourier.MatrixRestrictions.order A B ≤ d →
      (𝔼 N, MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T N ^ 2) ≤ η

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (MaxCutGames.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- On Boolean functions the restriction-global norm bound is exactly the
restriction-density hypothesis in Theorem 2.3. -/
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        MaxCutGames.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

def Theorem23 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
    ∀ (f : (E →ₗ[F2] F) → ℝ), IsBoolean f →
      (∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        MaxCutGames.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T N) ≤ ρ) →
      (𝔼 X, rankLevel d f X ^ 2) ≤
        (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2)

end MaxCutGames.Appendix.LevelInequality

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

namespace MaxCutGames.Appendix.DerivativeDegree

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier support is restricted to maps of rank at most `d`. -/
def DegreeAtMost (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ Y, d < frequencyRank Y → linearCoeff f Y = 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem DegreeAtMost.mono {d e : ℕ} {f : (E →ₗ[F2] F) → ℝ}
    (hf : DegreeAtMost d f) (hde : d ≤ e) : DegreeAtMost e f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hde hY)

theorem degree_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DegreeAtMost d (LevelInequality.rankLevel d f) :=
  LevelInequality.rankLevel_degree_le d f

theorem degree_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    {d : ℕ} {f : (E →ₗ[F2] F) → ℝ} (hf : DegreeAtMost d f) :
    DegreeAtMost d (spectralProjector P f) := by
  intro Y hY
  rw [linearCoeff_spectralProjector, hf Y hY]
  split_ifs <;> rfl

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem degree_mapDerivative (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - frequencyRank X) (mapDerivative X f) := by
  intro Z hZ
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

theorem degree_map_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - (order A B + frequencyRank X))
      (mapDerivative X (hybridDerivative A B T f)) := by
  simpa only [Nat.sub_sub] using
    degree_mapDerivative X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)

/-- The support cutoff keeps the total order intact even when `order A B > d`. -/
theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end MaxCutGames.Appendix.DerivativeDegree

/-! The degree-zero base case in the actual finite binary Fourier model. -/
namespace MaxCutGames.Appendix.DegreeZero
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem rank_pos_of_ne_zero (Y : F →ₗ[F2] E) (hY : Y ≠ 0) :
    0 < Module.finrank F2 Y.range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hb : Y.range = ⊥ := Submodule.finrank_eq_zero.mp hr
  apply hY
  ext x
  have hx : Y x ∈ Y.range := ⟨x, rfl⟩
  rw [hb] at hx
  exact hx

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_constant_of_degree_zero (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0)
    (M : E →ₗ[F2] F) : f M = linearCoeff f 0 := by
  classical
  rw [← linear_fourier_inversion f M, Finset.sum_eq_single (0 : F →ₗ[F2] E)]
  · simp
  · intro Y _ hY
    rw [hdegree Y (rank_pos_of_ne_zero Y hY), zero_mul]
  · simp

theorem fourth_moment_eq_energy_sq (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) = (𝔼 M, f M^2)^2 := by
  simp only [eq_constant_of_degree_zero f hdegree, Fintype.expect_const]
  rw [← pow_mul]

end MaxCutGames.Appendix.DegreeZero

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

namespace MaxCutGames.Appendix.A5IndexCount

open MaxCutGames.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

def insideEquiv (A I : Submodule F2 V) (hIA : I ≤ A) :
    (I.comap A.subtype) ≃ₗ[F2] I where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hIA i.property⟩, i.property⟩
  left_inv _i := Subtype.ext (Subtype.ext rfl)
  right_inv _i := Subtype.ext rfl
  map_add' _i _j := Subtype.ext rfl
  map_smul' _c _i := Subtype.ext rfl

theorem internal_isCompl (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) :
    IsCompl (I.comap A.subtype) (A0.comap A.subtype) := by
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro a hi h0
    exact Subtype.ext (Submodule.disjoint_def.mp hd a.val h0 hi)
  · apply eq_top_iff.mpr
    intro a _
    have ha : a.val ∈ A0 ⊔ I := by rw [hj]; exact a.property
    rcases Submodule.mem_sup.mp ha with ⟨v, hv, i, hi, hvi⟩
    refine Submodule.mem_sup.mpr ⟨⟨i, hIA hi⟩, hi, ⟨v, hA0 hv⟩, hv, ?_⟩
    apply Subtype.ext
    change i + v = a.val
    rw [add_comm]
    exact hvi

def projectionA0 (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) : A →ₗ[F2] I :=
  (insideEquiv A I hIA).toLinearMap.comp
    (((I.comap A.subtype).isComplEquivProj
      ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩).val)

theorem projectionA0_injective (A I A0 A0' : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A)
    (hd' : Disjoint A0' I) (hj' : A0' ⊔ I = A)
    (h : projectionA0 A I A0 hIA hd hj = projectionA0 A I A0' hIA hd' hj') :
    A0 = A0' := by
  let P := I.comap A.subtype
  let Q : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩
  let Q' : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0'.comap A.subtype, internal_isCompl A I A0' hIA hd' hj'⟩
  have hp : (P.isComplEquivProj Q).val = (P.isComplEquivProj Q').val := by
    apply LinearMap.ext
    intro a
    apply (insideEquiv A I hIA).injective
    exact LinearMap.congr_fun h a
  have hQ := P.isComplEquivProj.injective (Subtype.ext hp)
  have hq : A0.comap A.subtype = A0'.comap A.subtype := congrArg Subtype.val hQ
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  have hA0' : A0' ≤ A := le_sup_left.trans hj'.le
  ext x
  constructor
  · intro hx
    have hm : (⟨x, hA0 hx⟩ : A) ∈ A0.comap A.subtype := hx
    rw [hq] at hm
    exact hm
  · intro hx
    have hm : (⟨x, hA0' hx⟩ : A) ∈ A0'.comap A.subtype := hx
    rw [← hq] at hm
    exact hm

def fullRange {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    L →ₗ[F2] S.range :=
  (LinearMap.id : L →ₗ[F2] L).codRestrict S.range (fun x => by rw [hS]; trivial)

theorem fullRange_surjective {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    Function.Surjective (fullRange S hS) := fun c => ⟨c.val, Subtype.ext rfl⟩

theorem quotientRestriction_surjective (J B0 : Submodule F2 W) (hc : B0 ⊔ J = ⊤) :
    Function.Surjective (A4IndexCount.quotientRestriction J B0) := by
  intro z
  obtain ⟨w, rfl⟩ := J.mkQ_surjective z
  have hw : w ∈ B0 ⊔ J := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, j, hj, hbj⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change J.mkQ b = J.mkQ w
  have hz : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hj
  rw [← hbj, map_add, hz, add_zero]

theorem quotientRestriction_same_kernel (B J B0 : Submodule F2 W)
    (hm : B0 ⊓ J = B) :
    (A4IndexCount.quotientRestriction J B0).ker =
      (A4IndexCount.quotientRestriction B B0).ker := by
  rw [A4IndexCount.ker_quotientRestriction, A4IndexCount.ker_quotientRestriction]
  ext b
  change (b : W) ∈ J ↔ (b : W) ∈ B
  constructor
  · intro hj
    have hb : (b : W) ∈ B0 ⊓ J := ⟨b.property, hj⟩
    rwa [hm] at hb
  · intro hb
    exact (hm.symm.le.trans inf_le_right) hb

def sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) : (W ⧸ J) →ₗ[F2] (W ⧸ B) :=
  (A4IndexCount.factorViaRange (A4IndexCount.quotientRestriction J B0)
    (A4IndexCount.quotientRestriction B B0)
    (quotientRestriction_same_kernel B J B0 hm).le).comp
      (fullRange (A4IndexCount.quotientRestriction J B0)
        (LinearMap.range_eq_top.mpr (quotientRestriction_surjective J B0 hc)))

theorem range_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range = (A4IndexCount.quotientRestriction B B0).range := by
  rw [sectionB0, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (fullRange_surjective _ _))]
  exact A4IndexCount.factorViaRange_range _ _ _

theorem recover_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range.comap B.mkQ = B0 := by
  rw [range_sectionB0]
  have hB : B ≤ B0 := hm.symm.le.trans inf_le_left
  ext w
  change B.mkQ w ∈ (A4IndexCount.quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hz : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hz) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem sectionB0_injective (B J B0 B0' : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B)
    (hc' : B0' ⊔ J = ⊤) (hm' : B0' ⊓ J = B)
    (h : sectionB0 B J B0 hc hm = sectionB0 B J B0' hc' hm') : B0 = B0' := by
  calc
    B0 = (sectionB0 B J B0 hc hm).range.comap B.mkQ :=
      (recover_sectionB0 B J B0 hc hm).symm
    _ = (sectionB0 B J B0' hc' hm').range.comap B.mkQ :=
      congrArg (fun T : (W ⧸ J) →ₗ[F2] (W ⧸ B) => T.range.comap B.mkQ) h
    _ = B0' := recover_sectionB0 B J B0' hc' hm'

def encode (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) (p : OperatorPartitions.A5GeometricIndex X A B) :
    (A →ₗ[F2] X.range) × ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) :=
  (projectionA0 A X.range p.val.1 hIA p.property.1 p.property.2.1,
    sectionB0 B X.ker p.val.2 p.property.2.2.1 p.property.2.2.2)

theorem encode_injective (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) : Function.Injective (encode X A B hIA) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact projectionA0_injective A X.range p.val.1 q.val.1 hIA
      p.property.1 p.property.2.1 q.property.1 q.property.2.1 (congrArg Prod.fst h)
  · exact sectionB0_injective B X.ker p.val.2 q.val.2
      p.property.2.2.1 p.property.2.2.2 q.property.2.2.1 q.property.2.2.2
      (congrArg Prod.snd h)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_geometricIndex_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B))) := by
  have hfirst := CompressionCount.natCard_linearMap (U := A) (C := X.range)
  have hsecond := CompressionCount.natCard_linearMap (U := W ⧸ X.ker) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] X.range) := Nat.finite_of_card_ne_zero
    (by rw [hfirst]; exact pow_ne_zero _ (by decide))
  let : Finite ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero
    (by rw [hsecond]; exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode X A B hIA) (encode_injective X A B hIA)
  rw [Nat.card_prod, hfirst, hsecond, X.quotKerEquivRange.finrank_eq, ← pow_add] at h
  have he : Module.finrank F2 A * Module.finrank F2 X.range +
      Module.finrank F2 X.range * Module.finrank F2 (W ⧸ B) =
      Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) := by ring
  rwa [he] at h

theorem card_geometricIndex_degree_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (2 * d * Module.finrank F2 X.range) := by
  have hs : Module.finrank F2 A + Module.finrank F2 (W ⧸ B) ≤ 2 * d := by omega
  have he : Module.finrank F2 X.range *
      (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) ≤
      2 * d * Module.finrank F2 X.range := by
    calc
      _ ≤ Module.finrank F2 X.range * (2 * d) := Nat.mul_le_mul_left _ hs
      _ = _ := by ac_rfl
  exact (card_geometricIndex_le X A B hIA).trans
    (Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) he)

theorem card_geometricIndex_cube_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ^ 3 ≤
      2 ^ (6 * d * Module.finrank F2 X.range) := by
  have h := Nat.pow_le_pow_left (card_geometricIndex_degree_le X A B hIA d hA hB) 3
  rw [← pow_mul] at h
  convert h using 1
  congr 1
  ring

end MaxCutGames.Appendix.A5IndexCount
end

namespace MaxCutGames.Appendix.Induction

/-- The corrected outer-order cutoff (A.14), with natural subtraction explicit. -/
theorem outer_order_cutoff (d i j k a b : Nat)
    (ha : i + k ≤ a) (hb : j + k ≤ b) (ht : i + j + k ≤ d)
    (ho : (a - i - k) + (b - j - k) ≤ d - (i + j + k)) :
    a + b ≤ d + k := by
  omega

/-- Each complementary-space dimension is at most the original degree. -/
theorem complement_dimension_bounds (d i j k a b : Nat)
    (ha : i + k ≤ a) (hb : j + k ≤ b) (h : a + b ≤ d + k) :
    a - i ≤ d ∧ b - j ≤ d := by
  omega

/-- Recombination preserves the required derivative degree cutoff. -/
theorem recombined_order_cutoff (d k a b : Nat)
    (ha : k ≤ a) (hb : k ≤ b) (h : a + b ≤ d + k) :
    (a - k) + (b - k) + k ≤ d := by
  omega

theorem square_remainder_budget (d t : Nat) (ht : t ≤ d) :
    (d - t) * (d - t) + d * t ≤ d * d := by
  have hm := Nat.mul_le_mul_left (d - t) (Nat.sub_le d t)
  have hs : d - t + t = d := by omega
  have he : (d - t) * d + t * d = d * d := by
    rw [← Nat.add_mul, hs]
  rw [Nat.mul_comm d t]
  omega

/-- The exponent inequality preceding (A.16), with negative exponents moved
to the left side so natural subtraction cannot hide an invalid inequality. -/
theorem induction_exponent_budget (d t k : Nat) (ht : t ≤ d) (hk : k ≤ t) :
    100 * ((d - t) * (d - t)) + 27 * (d * t) + 6 * (d * k) +
      63 * (d * t) + 4 * (d * k) ≤ 100 * (d * d) := by
  have hs := Nat.mul_le_mul_left 100 (square_remainder_budget d t ht)
  have hm := Nat.mul_le_mul_left d hk
  omega

theorem antecedent_exponent_budget (d i j k t : Nat)
    (ht : t = i + j + k) (hd : t ≤ d) :
    d * (i + j) + 2 * (d * k) + k * k ≤ 3 * (d * t) := by
  have hk : k ≤ d := by omega
  have hm := Nat.mul_le_mul_right k hk
  have he : d * t = d * (i + j) + d * k := by
    rw [ht, Nat.mul_add]
  omega

/-- The factor from the fourth-power triangle inequality fits inside the
12d(i+j) budget used before (A.13). -/
theorem first_triangle_exponent_budget (d i j : Nat) (hi : i ≤ d) :
    7 * (d * (i + j)) + 3 * (i * j) ≤ 12 * (d * (i + j)) := by
  have hm := Nat.mul_le_mul_right j hi
  have he : d * (i + j) = d * i + d * j := Nat.mul_add d i j
  omega

/-- The derivative order t is at least half the original pair order. -/
theorem initial_order_bound (i j k : Nat) (hi : k ≤ i) (hj : k ≤ j) :
    i + j ≤ 2 * (i + j - k) := by
  omega

/-- For positive k the geometric-series exponent has at least d of slack. -/
theorem positive_rank_geometric_slack (d k : Nat) (hk : 1 ≤ k) :
    31 * (d * (k + 1)) + d ≤ 63 * (d * k) := by
  have hm := Nat.mul_le_mul_left d hk
  have he : d * (k + 1) = d * k + d := by simp [Nat.mul_add]
  omega

/-- The rank-dependent decay in (A.16) contains the corrected 8dk weight. -/
theorem corrected_weight_exponent (d k : Nat) :
    31 * (d * (k + 1)) + 4 * (d * k) =
      31 * d + 27 * (d * k) + 8 * (d * k) := by
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- When B′ plus the prescribed kernel spans the domain, the map on B′
determines its extension. Thus fixing image and kernel in the antecedent
count leaves no additional induced-isomorphism choice. The hypotheses expose
the only algebra used; the ambient finite vector spaces are not yet built. -/
theorem extension_unique {B V : Type} [Add B] [Add V]
    (zero : V) (X₁ X₂ : B → V) (B' K : B → Prop)
    (right_zero : ∀ v : V, v + zero = v)
    (add₁ : ∀ x y, X₁ (x + y) = X₁ x + X₁ y)
    (add₂ : ∀ x y, X₂ (x + y) = X₂ x + X₂ y)
    (span : ∀ x, ∃ b z, B' b ∧ K z ∧ x = b + z)
    (agree : ∀ b, B' b → X₁ b = X₂ b)
    (kill₁ : ∀ z, K z → X₁ z = zero)
    (kill₂ : ∀ z, K z → X₂ z = zero) : X₁ = X₂ := by
  funext x
  obtain ⟨b, z, hb, hz, hx⟩ := span x
  rw [hx, add₁, add₂, kill₁ z hz, kill₂ z hz, right_zero, right_zero]
  exact agree b hb

end MaxCutGames.Appendix.Induction

end OAI
