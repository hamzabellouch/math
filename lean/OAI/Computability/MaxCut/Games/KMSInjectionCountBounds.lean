import Mathlib
import OAI.Computability.MaxCut.Games.KMSFourthMomentZoomInvariant

namespace OAI

/-! Elementary dimension bounds for the actual injection count. The lower
bound is intentionally loose; its exponent suffices for the KMS norm ratio. -/

namespace MaxCutGames.Inverse.KMSInjectionCount

open scoped BigOperators

theorem binary_factor_lower {d n j : ℕ} (hj : j < d) (hdn : d ≤ n) :
    2 ^ (n - d) ≤ 2 ^ n - 2 ^ j := by
  have hn : 0 < n := by omega
  have hjn : j ≤ n - 1 := by omega
  have hdn' : n - d ≤ n - 1 := by omega
  calc
    2 ^ (n - d) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) hdn'
    _ = 2 ^ n - 2 ^ (n - 1) := (Nat.two_pow_sub_two_pow_pred hn).symm
    _ ≤ 2 ^ n - 2 ^ j :=
      Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) hjn) _

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

theorem beta_le_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E ≤ 2 ^ (Module.finrank F2 E * Module.finrank F2 I) := by
  rw [beta_eq_product I E hdim]
  calc
    _ ≤ ∏ _j : Fin (Module.finrank F2 I), 2 ^ Module.finrank F2 E := by
      apply Finset.prod_le_prod
      intro j _
      exact Nat.sub_le _ _
    _ = _ := by simp [← pow_mul]

theorem beta_ge_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) ≤
      beta I E := by
  rw [beta_eq_product I E hdim]
  calc
    _ = ∏ _j : Fin (Module.finrank F2 I),
        2 ^ (Module.finrank F2 E - Module.finrank F2 I) := by
      simp [← pow_mul, Nat.mul_comm]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro j _
      exact binary_factor_lower j.isLt hdim

theorem beta_positive (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    0 < beta I E :=
  lt_of_lt_of_le (Nat.pow_pos (by decide)) (beta_ge_pow I E hdim)

theorem beta_self_le [Finite I] :
    beta I I ≤ 2 ^ (Module.finrank F2 I * Module.finrank F2 I) :=
  beta_le_pow I I le_rfl

end
end MaxCutGames.Inverse.KMSInjectionCount

/-!
# Exact small-component energy ratio

The small full-rank component and the large rank component have the same
Fourier value on each kernel class. Their actual multiplicities are the
numbers of injective maps into the two domain spaces. This is the counting
identity underlying the zero-fixed-character case of KMS Lemma 3.19.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant
open MaxCutGames.Inverse.KMSKernelOrbitsFourier
open MaxCutGames.Inverse.KMSKernelFiberCard (KernelClass FullFrequency RankFrequency
  fullKernel rankKernel fullKernel_surjective rankKernel_surjective
  fullKernel_fiber_card rankKernel_fiber_card)
open MaxCutGames.Inverse.KMSInjectionCount (beta)

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KernelClass F I)]

omit [Finite E] [Finite F] [Finite I] in
/-- The exact ratio is cross-multiplied, so the identity also covers zero
components without any nonzero-energy premise. -/
theorem smallComponent_energy_cross_mul (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (beta I E : ℝ) * (𝔼 X, smallComponent ι f X ^ 2) =
      (beta I I : ℝ) * (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have h := fiber_constant_energy_cross_mul
    (fullKernel (F := F) (I := I)) (rankKernel (F := F) (E := E) (I := I))
    fullKernel_surjective (rankKernel_surjective hdim)
    (fun T : FullFrequency F I => linearCoeff f (ι.comp T.val))
    (fun S : RankFrequency F E I => linearCoeff f S.val)
    (fun T S hTS => coefficient_eq_of_ker_eq f hf _ _
      ((ker_comp_of_injective ι hι T.val).trans
        (congrArg Subtype.val hTS)))
    (beta I I) (beta I E)
    (fun K => by
      have hc := fullKernel_fiber_card (F := F) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
    (fun K => by
      have hc := rankKernel_fiber_card (F := F) (E := E) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
  rw [smallComponent_energy, rankComponent_energy]
  rw [Finset.sum_subtype (p := fun T : F →ₗ[F2] I => Function.Surjective T) _ (by simp) (fun T : F →ₗ[F2] I => linearCoeff f (ι.comp T) ^ 2),
    Finset.sum_subtype (p := fun S : F →ₗ[F2] E => Module.finrank F2 S.range = Module.finrank F2 I) _ (by simp) (fun S : F →ₗ[F2] E => linearCoeff f S ^ 2)]
  exact h

omit [Finite F]

omit [Finite I] in
/-- Dividing by the positive, explicitly counted injection multiplicity gives
the normalized small-space energy exactly. -/
theorem smallComponent_energy_ratio (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      (beta I I : ℝ) / (beta I E : ℝ) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hb : (beta I E : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (KMSInjectionCount.beta_positive I E hdim))
  apply (mul_left_cancel₀ hb)
  calc
    _ = (beta I I : ℝ) * (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) :=
      smallComponent_energy_cross_mul ι hι f hf
    _ = _ := by field_simp

/-- An explicit dimension-only norm comparison obtained from the actual
injection counts. The loose constant is sufficient for the analytic argument. -/
theorem smallComponent_energy_pow_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (2 : ℝ) ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlo : (2 : ℝ) ^
      (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) ≤
      (beta I E : ℝ) := by
    exact_mod_cast KMSInjectionCount.beta_ge_pow I E hdim
  have hhi : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast KMSInjectionCount.beta_self_le I
  calc
    _ ≤ (beta I E : ℝ) * (𝔼 X, smallComponent ι f X ^ 2) :=
      mul_le_mul_of_nonneg_right hlo (Finset.expect_nonneg (fun _ _ => sq_nonneg _))
    _ = (beta I I : ℝ) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) :=
      smallComponent_energy_cross_mul ι hι f hf
    _ ≤ _ := mul_le_mul_of_nonneg_right hhi
      (Finset.expect_nonneg (fun _ _ => sq_nonneg _))

/-- The zero-fixed-character case uses only the original function's squared
norm bound. In particular it applies to a pseudorandom indicator of density
at most `ε`, without assuming any restricted Fourier inequality. -/
theorem smallComponent_energy_le_of_energy_le (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ) (hε : (𝔼 X, f X ^ 2) ≤ ε) :
    (2 : ℝ) ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * ε := by
  exact (smallComponent_energy_pow_bound ι hι f hf).trans
    (mul_le_mul_of_nonneg_left
      ((component_energy_le (fun T : F →ₗ[F2] E =>
        Module.finrank F2 T.range = Module.finrank F2 I) f).trans hε)
      (pow_nonneg (by norm_num) _))

end
end MaxCutGames.Inverse.KMSAnalytic

/-! Dimension-only real bounds for actual binary injection counts. Multiplying
by the square-dimension factor removes truncated natural subtraction from the
ambient-dimension exponent. -/

namespace MaxCutGames.Inverse.KMSInjectionCount

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

/-- A subtraction-free form of the lower injection count. -/
theorem pow_dim_mul_le_pow_sq_mul_beta
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ) := by
  have hexp : Module.finrank F2 I * Module.finrank F2 I +
      Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I) =
      Module.finrank F2 I * Module.finrank F2 E := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hdim]
  have hnat : 2 ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      2 ^ (Module.finrank F2 I * Module.finrank F2 I) * beta I E := by
    calc
      _ = 2 ^ (Module.finrank F2 I * Module.finrank F2 I) *
          2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) := by
        rw [← pow_add, hexp]
      _ ≤ _ := Nat.mul_le_mul_left _ (beta_ge_pow I E hdim)
  exact_mod_cast hnat

/-- The small-to-ambient injection ratio, with the full ambient exponent. -/
theorem beta_ratio_le_pow [Finite I]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    (beta I I : ℝ) / (beta I E : ℝ) ≤
      (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) /
        (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) := by
  have hb : 0 < (beta I E : ℝ) := by exact_mod_cast beta_positive I E hdim
  have hp : 0 < (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) :=
    pow_pos (by norm_num) _
  have hq : 0 ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) :=
    pow_nonneg (by norm_num) _
  have hself : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast beta_self_le I
  apply (div_le_div_iff₀ hb hp).mpr
  calc
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) :=
      mul_le_mul_of_nonneg_right hself hp.le
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ)) :=
      mul_le_mul_of_nonneg_left (pow_dim_mul_le_pow_sq_mul_beta I E hdim) hq
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- Convert a count-weighted energy identity into a clean dimension bound. -/
theorem pow_mul_le_of_beta_cross_mul [Finite I]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcross : (beta I E : ℝ) * x = (beta I I : ℝ) * y) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) * x ≤
      (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * y := by
  have hq : 0 ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) :=
    pow_nonneg (by norm_num) _
  have hself : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast beta_self_le I
  calc
    _ ≤ ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ)) * x :=
      mul_le_mul_of_nonneg_right (pow_dim_mul_le_pow_sq_mul_beta I E hdim) hx
    _ = (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * ((beta I I : ℝ) * y) := by
      rw [mul_assoc, hcross]
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hself hy) hq
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

end
end MaxCutGames.Inverse.KMSInjectionCount

/-! The zero-fixed-character base of KMS's restricted Fourier induction,
with the actual injection-count ratio and homogeneous squared-density bound.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

universe u v w x
variable {E : Type u} {F : Type v} {I : Type w} {J : Type x}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KMSKernelFiberCard.KernelClass F I)]

omit [Finite F]

theorem smallComponent_energy_base_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have henergy : (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) ≤ ε :=
    (component_energy_le (fun T : F →ₗ[F2] E =>
      Module.finrank F2 T.range = Module.finrank F2 I) f).trans (hg.energy_le _ _ _)
  have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans henergy
  have hbase := KMSInjectionCount.pow_mul_le_of_beta_cross_mul I E hdim
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (smallComponent ι f _)))
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (rankComponent (Module.finrank F2 I) f _)))
    (smallComponent_energy_cross_mul ι hι f hf)
  calc
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := hbase
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * ε :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)) hε

/-- In a zero-dimensional partial codomain every prescribed frequency is the
unique one, so the base sum is exactly the small-component squared norm. -/
theorem fixedFrequencyEnergy_zero_dim_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) (hJ : Module.finrank F2 J = 0) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  let : Subsingleton J := Module.finrank_zero_iff.mp hJ
  have hπ : π = 0 := Subsingleton.elim _ _
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hπ, hA, fixedFrequencyEnergy_zero, hJ, Nat.add_zero]
  exact smallComponent_energy_base_bound ι hι f hf ε hg

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The exact Fourier coefficient merging law for a codomain restriction. This
is the Fourier step of KMS's zoom-out recursion: the subsequent orbit argument
groups the genuine extension fiber using basis invariance. Neither an inverse
nor a rank-level estimate is a premise.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 B]

/-- Restricting the codomain of a primal map restricts the domain of its dual
frequency. This identity is independent of the choice of bases. -/
theorem character_codomain_composition (J : B →ₗ[F2] F)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] B) :
    linearTraceCharacter S (J.comp X) = linearTraceCharacter (S.comp J) X := by
  simp only [linearTraceCharacter_apply]
  congr 1
  rw [linearTracePair_swap (J.comp X) S, linearTracePair_swap X (S.comp J)]
  simp only [linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)]
/-- Coefficients of the actual restricted function are the unnormalized sum
over exactly those original frequencies whose restriction is the new one.
The statement allows arbitrary linear `J`; injections are the KMS use case. -/
theorem coefficient_codomain_pullback (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : F →ₗ[F2] E, if S.comp J = T then linearCoeff f S else 0 := by
  have hexpand : (fun X => f (J.comp X)) =
      ∑ S : F →ₗ[F2] E, linearCoeff f S •
        (fun X => (linearTraceCharacter (S.comp J) X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa only [character_codomain_composition] using
      (linear_fourier_inversion f (J.comp X)).symm
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.comp J = T
  · simp [hS]
  · simp [hS, Ne.symm hS]

/-- The same merging identity on the actual fiber type. This form is ready
for the hyperplane extension bijection, without changing normalization. -/
theorem coefficient_codomain_pullback_fiber (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : {S : F →ₗ[F2] E // S.comp J = T}, linearCoeff f S.val := by
  rw [coefficient_codomain_pullback]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun S _ => S.val) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property⟩
  · intro S _ R _ h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S, (Finset.mem_filter.mp hS).2⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rfl

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Extension fibers for a dual hyperplane

Extending a linear frequency from `B` to `B × F2` amounts to choosing one
vector. Outside the old range every extension has the same kernel. Actual
basis invariance therefore makes all these Fourier coefficients equal.
The resulting exact counting identity is the algebraic part of the
hyperplane recursion; no analytic estimate is assumed here.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

/-- Extend a frequency by specifying its value on the new coordinate. -/
def hyperplaneExtend (z : B →ₗ[F2] E) (v : E) : (B × F2) →ₗ[F2] E :=
  z.coprod (LinearMap.toSpanSingleton F2 E v)

@[simp] theorem hyperplaneExtend_apply (z : B →ₗ[F2] E) (v : E) (b : B) (c : F2) :
    hyperplaneExtend z v (b, c) = z b + c • v := rfl

@[simp] theorem hyperplaneExtend_comp_inl (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).comp (LinearMap.inl F2 B F2) = z :=
  LinearMap.coprod_inl _ _

@[simp] theorem hyperplaneExtend_new_coordinate (z : B →ₗ[F2] E) (v : E) :
    hyperplaneExtend z v (0, 1) = v := by simp

/-- Recover a linear map from its old coordinates and its new-coordinate value. -/
theorem hyperplaneExtend_recover (S : (B × F2) →ₗ[F2] E) :
    hyperplaneExtend (S.comp (LinearMap.inl F2 B F2)) (S (0, 1)) = S := by
  have h : LinearMap.toSpanSingleton F2 E (S (0, 1)) =
      S.comp (LinearMap.inr F2 B F2) := by
    ext
    simp
  rw [hyperplaneExtend, h, LinearMap.coprod_comp_inl_inr]

/-- Exact parametrization of a restriction fiber, including dependent extensions. -/
def hyperplaneExtensionEquiv (z : B →ₗ[F2] E) :
    E ≃ {S : (B × F2) →ₗ[F2] E // S.comp (LinearMap.inl F2 B F2) = z} where
  toFun v := ⟨hyperplaneExtend z v, hyperplaneExtend_comp_inl z v⟩
  invFun S := S.1 (0, 1)
  left_inv v := hyperplaneExtend_new_coordinate z v
  right_inv S := by
    apply Subtype.ext
    change hyperplaneExtend z (S.1 (0, 1)) = S.1
    simpa only [S.2] using hyperplaneExtend_recover S.1

theorem hyperplaneExtend_injective (z : B →ₗ[F2] E) :
    Function.Injective (hyperplaneExtend z) := by
  intro u v h
  simpa using congrArg (fun S : (B × F2) →ₗ[F2] E => S (0, 1)) h

/-- The range is the old range plus the span of the new vector. -/
theorem range_hyperplaneExtend (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).range = z.range ⊔ Submodule.span F2 {v} := by
  rw [hyperplaneExtend, LinearMap.range_coprod, LinearMap.range_toSpanSingleton]

theorem range_hyperplaneExtend_of_mem (z : B →ₗ[F2] E) {v : E} (hv : v ∈ z.range) :
    (hyperplaneExtend z v).range = z.range := by
  rw [range_hyperplaneExtend, sup_eq_left]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv

/-- All outside-range extensions have the same actual kernel. -/
theorem ker_hyperplaneExtend_of_notMem (z : B →ₗ[F2] E) {v : E}
    (hv : v ∉ z.range) :
    (hyperplaneExtend z v).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  have hv0 : v ≠ 0 := fun h => hv (h.symm ▸ z.range.zero_mem)
  have hd : Disjoint z.range (LinearMap.toSpanSingleton F2 E v).range := by
    rw [LinearMap.range_toSpanSingleton]
    exact Submodule.disjoint_span_singleton_of_notMem hv
  rw [hyperplaneExtend, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
    LinearMap.ker_toSpanSingleton F2 hv0]

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

theorem coefficient_hyperplaneExtend_eq (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {u v : E} (hu : u ∉ z.range) (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z u) = linearCoeff f (hyperplaneExtend z v) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [ker_hyperplaneExtend_of_notMem z hu, ker_hyperplaneExtend_of_notMem z hv]

variable [Fintype E]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] B × F2)] in
/-- The number of outside choices is exactly the ambient cardinality minus
the old range cardinality. -/
theorem card_hyperplaneExtension_outside (z : B →ₗ[F2] E) :
    (Finset.univ.filter (fun v : E => v ∉ z.range)).card =
      Fintype.card E - Fintype.card z.range := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_subtype_compl (fun v : E => v ∈ z.range)

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] B × F2)] in
theorem card_hyperplaneExtension_outside_pow (z : B →ₗ[F2] E) :
    (Finset.univ.filter (fun v : E => v ∉ z.range)).card =
      2 ^ Module.finrank F2 E - 2 ^ Module.finrank F2 z.range := by
  rw [card_hyperplaneExtension_outside, Module.card_eq_pow_finrank (K := F2) (V := E),
    Module.card_eq_pow_finrank (K := F2) (V := z.range)]
  simp only [F2, ZMod.card]

/-- Exact sum of the common coefficient over all outside-range extensions. -/
theorem sum_hyperplaneExtend_outside (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u with u ∉ z.range, linearCoeff f (hyperplaneExtend z u)) =
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  calc
    _ = ∑ _u ∈ Finset.univ.filter (fun u : E => u ∉ z.range),
        linearCoeff f (hyperplaneExtend z v) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact coefficient_hyperplaneExtend_eq f hf z (Finset.mem_filter.mp hu).2 hv
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_hyperplaneExtension_outside]

/-- Split the full extension fiber into dependent and independent choices. -/
theorem sum_hyperplaneExtend (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u : E, linearCoeff f (hyperplaneExtend z u)) =
      (∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) +
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  rw [← sum_hyperplaneExtend_outside f hf z hv]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u => u ∈ z.range) (fun u => linearCoeff f (hyperplaneExtend z u))).symm

/-- Solve the extension sum for the coefficient of an independent extension. -/
theorem coefficient_hyperplaneExtend_recursion (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z v) =
      ((∑ u : E, linearCoeff f (hyperplaneExtend z u)) -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) /
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) := by
  have hlt : Fintype.card z.range < Fintype.card E :=
    Fintype.card_subtype_lt hv
  have hne : ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
  apply (eq_div_iff hne).mpr
  rw [sum_hyperplaneExtend f hf z hv]
  ring

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The exact basis-invariant KMS zoom-out recursion. The restricted coefficient
is an actual Fourier coefficient of the homogeneous codomain restriction.
The full extension fiber is split into dependent vectors and one common
coefficient on all independent vectors; neither term is replaced by an
assumed estimate.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)]

/-- Exact codomain-restriction coefficient, reindexed by the extension vector.
The sum has no cardinality normalization. -/
theorem coefficient_hyperplane_restriction
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (z : B →ₗ[F2] E) :
    linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z =
      ∑ u : E, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_codomain_pullback_fiber]
  exact ((hyperplaneExtensionEquiv z).sum_comp
    (fun S => linearCoeff f S.val)).symm

/-- KMS's genuine zoom-out recurrence, in product coordinates. The denominator
is the exact number of independent extension vectors. Basis invariance is
used to prove their Fourier coefficients coincide. -/
theorem coefficient_zoomOut_recursion
    (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z v) =
      (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) /
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) := by
  rw [coefficient_hyperplane_restriction]
  exact coefficient_hyperplaneExtend_recursion f hf z hv

/-- A denominator-free form convenient for squared-norm estimates. -/
theorem coefficient_zoomOut_mul
    (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) =
      linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_hyperplane_restriction, sum_hyperplaneExtend f hf z hv]
  ring

end
end MaxCutGames.Inverse.KMSFourthMoment

/-! The actual squared-coefficient inequality from the KMS zoom-out recursion.
Only a finite Cauchy--Schwarz inequality is applied to the exact restriction
identity. No restricted Fourier bound is taken as a premise. -/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant
open MaxCutGames.Inverse.KMSFourthMoment

/-- Cauchy--Schwarz with the distinguished scalar included as one extra
summand. This form also handles an empty dependent branch. -/
theorem sub_sum_sq_le_card_mul {C : Type*} [Fintype C]
    (x : ℝ) (a : C → ℝ) :
    (x - ∑ c, a c) ^ 2 ≤
      ((Fintype.card C : ℝ) + 1) * (x ^ 2 + ∑ c, a c ^ 2) := by
  let b : Option C → ℝ := fun c => c.elim x (fun c => -a c)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option C))
    (fun _ => (1 : ℝ)) b
  simpa [b, Fintype.sum_option, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
/-- An actual independent extension coefficient is controlled by its
homogeneous restriction coefficient and every dependent extension. -/
theorem coefficient_zoomOut_sq_bound
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] E) {v : E} (hv : v ∉ z.range) :
    (((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend z v) ^ 2 ≤
      ((Fintype.card z.range : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z ^ 2 +
          ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val) ^ 2) := by
  have hrec := coefficient_zoomOut_mul f hf z hv
  rw [Finset.sum_subtype (p := fun u : E => u ∈ z.range) _ (by simp)
    (fun u : E => linearCoeff f (hyperplaneExtend z u))] at hrec
  calc
    _ = ((((Fintype.card E - Fintype.card z.range : ℕ) : ℝ)) *
        linearCoeff f (hyperplaneExtend z v)) ^ 2 := (mul_pow _ _ _).symm
    _ = (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val)) ^ 2 := by rw [hrec]
    _ ≤ _ := sub_sum_sq_le_card_mul _ _

end

/-! Exact images and dependent-extension sums after embedding a smaller
frequency space. These identities align the genuine zoom-out recurrence with
the small-component Fourier coefficients. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

def leftEmbedding (ι : (J × F2) →ₗ[F2] E) : J →ₗ[F2] E :=
  ι.comp (LinearMap.inl F2 J F2)

theorem leftEmbedding_injective (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : Function.Injective (leftEmbedding ι) := by
  intro x y h
  have hxy : (x, (0 : F2)) = (y, 0) := hι h
  exact congrArg Prod.fst hxy

theorem lastVector_not_mem_left_range (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : ι (0, 1) ∉ (leftEmbedding ι).range := by
  rintro ⟨j, hj⟩
  have h : (j, (0 : F2)) = (0, 1) := hι hj
  exact zero_ne_one (congrArg Prod.snd h)

theorem range_left_comp_of_surjective (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    ((leftEmbedding ι).comp z).range = (leftEmbedding ι).range := by
  ext v
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨z b, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨b, rfl⟩ := hz j
    exact ⟨b, rfl⟩

/-- The dependent extensions are enumerated exactly once by the small space. -/
def liftedRangeEquiv (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    J ≃ ((leftEmbedding ι).comp z).range :=
  Equiv.ofBijective
    (fun j => ⟨leftEmbedding ι j, by
      rw [range_left_comp_of_surjective ι z hz]
      exact ⟨j, rfl⟩⟩)
    ⟨by
      intro x y h
      exact leftEmbedding_injective ι hι (congrArg Subtype.val h),
      by
      rintro ⟨v, b, rfl⟩
      exact ⟨z b, rfl⟩⟩

@[simp] theorem liftedRangeEquiv_val (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (z : B →ₗ[F2] J) (hz : Function.Surjective z) (j : J) :
    (liftedRangeEquiv ι hι z hz j).val = leftEmbedding ι j := rfl

theorem card_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    Fintype.card ((leftEmbedding ι).comp z).range = Fintype.card J :=
  (Fintype.card_congr (liftedRangeEquiv ι hι z hz)).symm

theorem sum_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) (a : E → ℝ) :
    (∑ u : ((leftEmbedding ι).comp z).range, a u.val) =
      ∑ j : J, a (leftEmbedding ι j) :=
  ((liftedRangeEquiv ι hι z hz).sum_comp (fun u => a u.val)).symm

theorem hyperplaneExtend_left_comp (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (w : J) :
    hyperplaneExtend ((leftEmbedding ι).comp z) (leftEmbedding ι w) =
      (leftEmbedding ι).comp (hyperplaneExtend z w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [hyperplaneExtend, map_add, map_smul]

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
