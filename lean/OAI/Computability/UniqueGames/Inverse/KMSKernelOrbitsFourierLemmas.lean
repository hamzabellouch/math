import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Analysis.SubspaceCountingLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedScalarLemmas

namespace OAI

section

/-! Basis-invariant matrix functions have constant actual Fourier coefficients
on kernel fibers. This uses ambient automorphism transitivity proved from the
first isomorphism theorem, followed by the exact change-of-basis identity for
the normalized trace-character transform. -/

namespace UniqueGamesTheorem.Inverse.KMSKernelOrbitsFourier

open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant
open UniqueGamesTheorem.Inverse.KMSKernelOrbits

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]

/-- Actual coefficients depend on the kernel, not on the chosen embedding of
the quotient into the basis-index space. No coefficient-invariance premise is
assumed beyond the original function's basis invariance. -/
theorem coefficient_eq_of_ker_eq (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (S T : F →ₗ[F2] E) (hker : S.ker = T.ker) :
    linearCoeff f S = linearCoeff f T := by
  obtain ⟨g, hg⟩ := exists_postcomp_equiv_of_ker_eq S T hker
  have h := coefficient_change f hf g S
  rw [hg] at h
  exact h.symm

end
end UniqueGamesTheorem.Inverse.KMSKernelOrbitsFourier

end

section

/-!
# Extension fibers for a dual hyperplane

Extending a linear frequency from `B` to `B × F2` amounts to choosing one
vector. Outside the old range every extension has the same kernel. Actual
basis invariance therefore makes all these Fourier coefficients equal.
The resulting exact counting identity is the algebraic part of the
hyperplane recursion; no analytic estimate is assumed here.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

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

section Fourier
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

end Fourier
end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact images and dependent-extension sums after embedding a smaller
frequency space. These identities align the genuine zoom-out recurrence with
the small-component Fourier coefficients. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

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
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Exact small-component energy ratio

The small full-rank component and the large rank component have the same
Fourier value on each kernel class. Their actual multiplicities are the
numbers of injective maps into the two domain spaces. This is the counting
identity underlying the zero-fixed-character case of KMS Lemma 3.19.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant
open UniqueGamesTheorem.Inverse.KMSKernelOrbitsFourier
open UniqueGamesTheorem.Inverse.KMSKernelFiberCard (KernelClass FullFrequency RankFrequency
  fullKernel rankKernel fullKernel_surjective rankKernel_surjective
  fullKernel_fiber_card rankKernel_fiber_card)
open UniqueGamesTheorem.Inverse.KMSInjectionCount (beta)

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
      convert hc using 1
      congr 1
      ext T
      simp)
    (fun K => by
      have hc := rankKernel_fiber_card (F := F) (E := E) (I := I) K
      convert hc using 1
      congr 1
      ext T
      simp)
  rw [smallComponent_energy, rankComponent_energy]
  rw [Finset.sum_subtype (p := fun T : F →ₗ[F2] I => Function.Surjective T) _ (by simp) (fun T : F →ₗ[F2] I => linearCoeff f (ι.comp T) ^ 2),
    Finset.sum_subtype (p := fun S : F →ₗ[F2] E => Module.finrank F2 S.range = Module.finrank F2 I) _ (by simp) (fun S : F →ₗ[F2] E => linearCoeff f S ^ 2)]
  exact h

omit [Finite F] [Finite I] in
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

omit [Finite F] in
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

omit [Finite F] in
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
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallCoeff ι f = smallCoeff κ f :=
  smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- Independence is equality of the actual small-space functions. -/
theorem smallComponent_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallComponent ι f = smallComponent κ f :=
  smallComponent_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem surjective_postcomp_equiv (g : I ≃ₗ[F2] I) (T : F →ₗ[F2] I) :
    Function.Surjective (g.toLinearMap.comp T) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (g y)
    exact ⟨x, g.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (g.symm y)
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- The retained coefficient array is invariant under a small-space basis
change, with surjectivity and the lifted frequency kernel both preserved. -/
theorem smallCoeff_postcomp_equiv (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (g : I ≃ₗ[F2] I) (T : F →ₗ[F2] I) :
    smallCoeff ι f (g.toLinearMap.comp T) = smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_postcomp_equiv]
  split_ifs
  · apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
    rw [ker_comp_of_injective ι hι, ker_comp_of_injective g.toLinearMap g.injective,
      ker_comp_of_injective ι hι]
  · rfl

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The small component is genuinely invariant as a function on matrices. -/
theorem smallComponent_invariant (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (smallComponent ι f) := by
  intro g X
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Fintype.sum_equiv (KMSBasisInvariant.frequencyChange g)
  intro T
  change smallCoeff ι f T * (linearTraceCharacter T (X.comp g.toLinearMap)).re =
    smallCoeff ι f (g.toLinearMap.comp T) *
      (linearTraceCharacter (g.toLinearMap.comp T) X).re
  rw [smallCoeff_postcomp_equiv ι hι f hf, KMSBasisInvariant.character_change]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalyticHybridCoordinates KMSAnalytic

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The unnormalized fiber of extensions of one compressed frequency. -/
abbrev Extension (z : B →ₗ[R] W) :=
  {ψ : (B × C) →ₗ[R] W // ψ.comp (LinearMap.inl R B C) = z}

/-- The coordinate record has precisely three independent entries. -/
def coordinatesDataEquiv (z : B →ₗ[R] W) :
    Coordinates (A := A) (D := D) (C := C) z ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) where
  toFun p := (p.alpha, ⟨p.psi, p.psi_left⟩, p.v)
  invFun p := ⟨p.1, p.2.1.val, p.2.1.property, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨a, ⟨ψ, hψ⟩, v⟩; rfl

def compressedFiberDataEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) :=
  (compressedFiberEquiv z).trans (coordinatesDataEquiv z)

/-- Specifying the value on the complementary block gives every extension
exactly once. This will give the cardinality factor `|Hom(C,W)|`. -/
def extensionEquiv (z : B →ₗ[R] W) : Extension (C := C) z ≃ (C →ₗ[R] W) where
  toFun ψ := ψ.val.comp (LinearMap.inr R B C)
  invFun u := ⟨z.coprod u, by ext b; simp⟩
  left_inv ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : ψ.val (b, 0) = z b :=
      congrArg (fun t : B →ₗ[R] W => t b) ψ.property
    change z b + ψ.val (0, c) = ψ.val (b, c)
    rw [← hb, ← map_add]
    simp
  right_inv u := by ext c; simp

section Binary
variable [Module F2 A] [Module F2 W] [Module F2 D] [Module F2 B] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]

omit [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))] in
/-- The actual hybrid and rank selectors reduce to the small component's
ordinary surjectivity selector. The only remaining geometric selector is
injectivity of the complementary block. -/
theorem hybrid_rank_coeff_assemble
    {z : B →ₗ[F2] W} (hz : Function.Surjective z)
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D)))
    (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) :
    (if LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) (assemble p)
     else 0) =
      if Function.Injective p.v then smallCoeff κ f (fullCoordinates p) else 0 := by
  have hh := hybrid_assemble_iff p hz
  change LinearIdentities.Hybrid (assemble p) _ _ ↔
    Function.Injective p.v ∧ Function.Surjective (fullCoordinates p) at hh
  rw [hh]
  by_cases hv : Function.Injective p.v
  · simp only [hv, true_and, ite_true]
    by_cases hp : Function.Surjective (fullCoordinates p)
    · rw [ite_eq_left hp]
      have hr := finrank_assemble p hv hp
      simp only [rankComponent, coeff_component, hr, ite_true]
      have he := congrFun (smallCoeff_eq_of_basisInvariant (embedLast p.v) κ
        (embedLast_injective p.v hv) hκ f hf) (fullCoordinates p)
      rw [smallCoeff, ite_eq_left hp, ← assemble_eq_embedLast_comp] at he
      exact he
    · simp [hp, smallCoeff]
  · simp [hv]

end Binary
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Cardinality budgets for hybrid coefficient fibers

Extensions are counted by an exact equivalence with linear maps on the
complement. Injective complementary maps are bounded by all linear maps.
Images of fixed dimension are counted using the proved basis encoding of
subspaces. Their combined exponent fits the mixed Fourier denominator.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix

/-- The restriction fiber has exactly as many elements as the maps on its
complement, before any finite-field cardinality formula is applied. -/
theorem card_restriction_fiber_eq {R B C W : Type*} [Ring R]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup W] [Module R W]
    [Fintype ((B × C) →ₗ[R] W)] [Fintype (C →ₗ[R] W)]
    (z : B →ₗ[R] W) :
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)).card = Fintype.card (C →ₗ[R] W) := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (extensionEquiv (C := C) z)

section Extensions

variable {B C W : Type*}
  [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
  [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]

/-- The exact number of extensions is independent of the prescribed map. -/
theorem natCard_extension (z : B →ₗ[F2] W) :
    Nat.card (Extension (C := C) z) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 W) := by
  rw [Nat.card_congr (extensionEquiv (C := C) z)]
  exact CompressionCount.natCard_linearMap

/-- The same exact count in the filtered form used by the fiber Cauchy bound. -/
theorem card_restriction_fiber [Fintype ((B × C) →ₗ[F2] W)]
    (z : B →ₗ[F2] W) :
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[F2] W =>
      ψ.comp (LinearMap.inl F2 B C) = z)).card =
        2 ^ (Module.finrank F2 C * Module.finrank F2 W) := by
  rw [← Fintype.card_subtype]
  simpa only [Extension, Nat.card_eq_fintype_card] using natCard_extension (C := C) z

end Extensions

section Injections

variable {C D : Type*}
  [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
  [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]

/-- Exact binary cardinality of the unrestricted complementary map space. -/
theorem card_linearMap_eq [Fintype (C →ₗ[F2] D)] :
    Fintype.card (C →ₗ[F2] D) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using
    (CompressionCount.natCard_linearMap (U := C) (C := D))

/-- Ordered independent complementary choices are no more numerous than
all maps on the complementary domain; there is no basis-orbit quotient. -/
theorem natCard_injective_le :
    Nat.card {v : C →ₗ[F2] D // Function.Injective v} ≤
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  let : Finite C := Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (C →ₗ[F2] D) := Finite.of_injective
    (fun v : C →ₗ[F2] D => (v : C → D)) DFunLike.coe_injective
  calc
    _ ≤ Nat.card (C →ₗ[F2] D) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := CompressionCount.natCard_linearMap

theorem card_injective_le [Fintype (C →ₗ[F2] D)] :
    Fintype.card {v : C →ₗ[F2] D // Function.Injective v} ≤
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using natCard_injective_le (C := C) (D := D)

end Injections

section Images

variable {U : Type*} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]

/-- Choose one ordered basis for each image. The resulting encoding gives
the dimension-sensitive image count, rather than the count of all subspaces. -/
theorem natCard_rank_subspaces_le (q : ℕ) :
    Nat.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.mul_comm] using
    (SubspaceCounting.card_binary_subspaces_rank_le (V := U)
      (Module.finrank F2 U) q le_rfl)

theorem card_rank_subspaces_le [Fintype (Submodule F2 U)] (q : ℕ) :
    Fintype.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.card_eq_fintype_card] using natCard_rank_subspaces_le (U := U) q

end Images

/-- The three counting costs leave nonnegative slack in the ambient
dimension exponent. The complementary image space has dimension `q + d`. -/
theorem count_exponent_le (a b q d : ℕ) :
    q * (q + d) + (b * d) * 2 + b * q ≤ (2 * b + q) * (a + q + d) := by
  calc
    _ ≤ q * (q + d) + (b * d) * 2 + b * q + ((2 * b + q) * a + b * q) :=
      Nat.le_add_right _ _
    _ = _ := by ring

/-- The actual nonnegative counts fit the mixed Fourier denominator.
The bound also permits real-valued upper estimates for those counts. -/
theorem count_budget_le (a b q d : ℕ) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (q + d)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤
      (2 : ℝ) ^ ((2 * b + q) * (a + q + d)) := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hvSq : countV ^ 2 ≤ ((2 : ℝ) ^ (b * d)) ^ 2 :=
    (sq_le_sq₀ hv0 (pow_nonneg htwo _)).mpr hv
  have hfirst : countW * countV ^ 2 ≤
      (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 :=
    mul_le_mul hw hvSq (sq_nonneg countV) (pow_nonneg htwo _)
  calc
    _ ≤ (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 *
        (2 : ℝ) ^ (b * q) :=
      mul_le_mul hfirst he he0 (mul_nonneg (pow_nonneg htwo _) (sq_nonneg _))
    _ = (2 : ℝ) ^ (q * (q + d) + (b * d) * 2 + b * q) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (count_exponent_le a b q d)

/-- Ambient-dimension form of the same budget, with the split dimension
identity supplied by the adapted coordinates. -/
theorem count_budget_le_of_dimension (a b q d ell : ℕ)
    (hell : ell = a + q + d) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (ell - a)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤ (2 : ℝ) ^ ((2 * b + q) * ell) := by
  have hsub : ell - a = q + d := by omega
  rw [hsub] at hw
  rw [hell]
  exact count_budget_le a b q d countW countV extensionFactor hv0 he0 hw hv he

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- Squared small Fourier coefficients whose image under a prescribed linear
projection is the fixed partial frequency. -/
def fixedFrequencyEnergy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) : ℝ :=
  ∑ T with π.comp T = A, smallCoeff ι f T ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_nonneg (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    0 ≤ fixedFrequencyEnergy ι f π A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The definition retains precisely the surjective compatible frequencies. -/
theorem fixedFrequencyEnergy_eq (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => π.comp T = A ∧ Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> by_cases hA : π.comp T = A <;>
    simp [smallCoeff, hT, hA]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- An impossible partial frequency contributes no energy. -/
theorem fixedFrequencyEnergy_eq_zero_of_not_surjective
    (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (A : F →ₗ[F2] J) (hA : ¬ Function.Surjective A) :
    fixedFrequencyEnergy ι f π A = 0 := by
  rw [fixedFrequencyEnergy_eq]
  apply Finset.sum_eq_zero
  intro T hT
  have ht := (Finset.mem_filter.mp hT).2
  exact (hA (ht.1 ▸ hπ.comp ht.2)).elim

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Forgetting the prescribed partial frequency gives the exact full small
energy, so every individual restricted sum is bounded by it. -/
theorem fixedFrequencyEnergy_le (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A ≤ 𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- With no fixed characters the restricted sum is exactly the small squared
norm; there is no ambient-cardinality normalization in the frequency sum. -/
theorem fixedFrequencyEnergy_zero (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    fixedFrequencyEnergy ι f (0 : I →ₗ[F2] J) 0 =
      𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  simp [fixedFrequencyEnergy]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The fixed-character energy is independent of the chosen small-space
embedding for the actual basis-invariant function. -/
theorem fixedFrequencyEnergy_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A = fixedFrequencyEnergy κ f π A := by
  unfold fixedFrequencyEnergy
  rw [smallCoeff_eq_of_basisInvariant ι κ hι hκ f hf]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
