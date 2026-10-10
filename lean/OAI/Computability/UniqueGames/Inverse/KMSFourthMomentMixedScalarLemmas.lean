import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas

namespace OAI

section

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

/-- A deliberately generous rank-dependent cost for one fixed point. -/
def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

theorem one_le_mixedStepFactor (R : ℕ) : 1 ≤ mixedStepFactor R := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

/-- Character dimension is at most the number of free coordinates, so the
ambient-weight ratio has exponent at most twice the rank cap. -/
theorem mixed_step_factor_bound (R t n : ℕ) (ht : t ≤ 2 * R) (hn : n ≤ R) :
    2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) ≤ mixedStepFactor R := by
  have ht' : (2 : ℝ) ^ t ≤ 2 ^ (2 * R) :=
    pow_le_pow_right₀ (by norm_num) ht
  have hn' : ((2 : ℝ) ^ n) ^ 2 ≤ 2 ^ (2 * R) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have he : mixedStepFactor R = 4 * (2 : ℝ) ^ (2 * R) := by
    unfold mixedStepFactor
    rw [pow_add]
    ring
  rw [he]
  linarith

/-- The two lower estimates live in adjacent ambient dimensions. Multiplying
by the new weight costs q on the point-restricted branch, and nothing on the
unrestricted lower-component branch. -/
theorem mixed_weighted_step {M A B q w n C : ℝ}
    (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hrec : M ≤ 2 * (A + n ^ 2 * B))
    (hA : w * A ≤ C) (hB : (q * w) * B ≤ C) :
    (q * w) * M ≤ 2 * (q + n ^ 2) * C := by
  calc
    (q * w) * M ≤ (q * w) * (2 * (A + n ^ 2 * B)) :=
      mul_le_mul_of_nonneg_left hrec (mul_nonneg hq hw)
    _ = 2 * (q * (w * A) + n ^ 2 * ((q * w) * B)) := by ring
    _ ≤ 2 * (q * C + n ^ 2 * C) := by
      gcongr
    _ = 2 * (q + n ^ 2) * C := by ring

/-- The complete scalar induction step with a rank-independent ambient
weight and a rank-dependent but dimension-independent loss. -/
theorem mixed_weighted_step_pow (R s ell t n : ℕ) (H ε M A B : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (ht : t ≤ 2 * R) (hn : n ≤ R)
    (hrec : M ≤ 2 * (A + ((2 : ℝ) ^ n) ^ 2 * B))
    (hA : (2 : ℝ) ^ (t * ell) * A ≤ H * mixedStepFactor R ^ s * ε)
    (hB : (2 : ℝ) ^ (t * (ell + 1)) * B ≤ H * mixedStepFactor R ^ s * ε) :
    (2 : ℝ) ^ (t * (ell + 1)) * M ≤ H * mixedStepFactor R ^ (s + 1) * ε := by
  have he : (2 : ℝ) ^ (t * (ell + 1)) = 2 ^ t * 2 ^ (t * ell) := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    ring
  have hc : 0 ≤ H * mixedStepFactor R ^ s * ε :=
    mul_nonneg (mul_nonneg hH (pow_nonneg (mixedStepFactor_nonneg R) _)) hε
  have h := mixed_weighted_step (q := (2 : ℝ) ^ t)
    (w := (2 : ℝ) ^ (t * ell)) (n := (2 : ℝ) ^ n)
    (by positivity) (by positivity) hrec hA (by simpa only [he] using hB)
  rw [← he] at h
  calc
    _ ≤ 2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) *
        (H * mixedStepFactor R ^ s * ε) := h
    _ ≤ mixedStepFactor R * (H * mixedStepFactor R ^ s * ε) :=
      mul_le_mul_of_nonneg_right (mixed_step_factor_bound R t n ht hn) hc
    _ = _ := by rw [pow_succ]; ring

end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

namespace UniqueGamesTheorem.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

abbrev F2 := ZMod 2

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

/-- The actual number of injective linear maps, with no asymptotic convention. -/
def beta : ℕ := Nat.card {J : I →ₗ[F2] E // Function.Injective J}

/-- A domain basis turns injective maps into independent image families. -/
def injectiveEquivIndependent {ι : Type*} (b : Module.Basis ι F2 I) :
    {J : I →ₗ[F2] E // Function.Injective J} ≃
      {s : ι → E // LinearIndependent F2 s} where
  toFun J := ⟨J.val ∘ b, b.linearIndependent.map' J.val (LinearMap.ker_eq_bot.mpr J.property)⟩
  invFun s := ⟨b.constr F2 s.val, b.injective_constr_of_linearIndependent s.property⟩
  left_inv J := by
    apply Subtype.ext
    exact b.constr_self F2 J.val
  right_inv s := by
    apply Subtype.ext
    funext i
    exact b.constr_basis F2 s.val i

/-- Exact binary injection count, including the zero-dimensional domain. -/
theorem beta_eq_product [FiniteDimensional F2 I] [Finite E]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E = ∏ j : Fin (Module.finrank F2 I),
      (2 ^ Module.finrank F2 E - 2 ^ j.val) := by
  unfold beta
  rw [Nat.card_congr (injectiveEquivIndependent I E (Module.finBasis F2 I))]
  simpa only [F2, ZMod.card] using
    (card_linearIndependent (K := F2) (V := E) hdim)

end
end UniqueGamesTheorem.Inverse.KMSInjectionCount

end

section

/-! Elementary dimension bounds for the actual injection count. The lower
bound is intentionally loose; its exponent suffices for the KMS norm ratio. -/

namespace UniqueGamesTheorem.Inverse.KMSInjectionCount

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
end UniqueGamesTheorem.Inverse.KMSInjectionCount

end

section

/-! Dimension-only real bounds for actual binary injection counts. Multiplying
by the square-dimension factor removes truncated natural subtraction from the
ambient-dimension exponent. -/

namespace UniqueGamesTheorem.Inverse.KMSInjectionCount

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
end UniqueGamesTheorem.Inverse.KMSInjectionCount

end

section

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

noncomputable section

abbrev F2 := ZMod 2

variable (F E I : Type*)
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

abbrev KernelClass :=
  {K : Submodule F2 F // Module.finrank F2 (F ⧸ K) = Module.finrank F2 I}

abbrev RankFrequency :=
  {S : F →ₗ[F2] E // Module.finrank F2 S.range = Module.finrank F2 I}

abbrev FullFrequency := {T : F →ₗ[F2] I // Function.Surjective T}

variable {F E I}

def rankKernel (S : RankFrequency F E I) : KernelClass F I :=
  ⟨S.val.ker, S.val.quotKerEquivRange.finrank_eq.trans S.property⟩

def fullKernel (T : FullFrequency F I) : KernelClass F I :=
  ⟨T.val.ker, (T.val.quotKerEquivOfSurjective T.property).finrank_eq⟩

@[simp] theorem rankKernel_val (S : RankFrequency F E I) :
    (rankKernel S).val = S.val.ker := rfl

@[simp] theorem fullKernel_val (T : FullFrequency F I) :
    (fullKernel T).val = T.val.ker := rfl

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

/-- Equal quotient dimension gives an actual linear equivalence. -/
def quotientEquiv (K : KernelClass F I) : (F ⧸ K.val) ≃ₗ[F2] I :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq K.property)

/-- Every kernel of the prescribed codimension occurs among rank-`dim I`
maps into any ambient space whose dimension is at least `dim I`. -/
theorem rankKernel_surjective
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    Function.Surjective (rankKernel (F := F) (E := E) (I := I)) := by
  classical
  obtain ⟨j, hj⟩ :=
    (finrank_le_iff_exists_linearMap (R := F2) (M := I) (M' := E)).mp hdim
  intro K
  let J : (F ⧸ K.val) →ₗ[F2] E := j.comp (quotientEquiv K).toLinearMap
  have hJ : Function.Injective J := hj.comp (quotientEquiv K).injective
  refine ⟨⟨J.comp K.val.mkQ, ?_⟩, ?_⟩
  · exact (quotientInjection_comp_finrank K.val J hJ).trans K.property
  · apply Subtype.ext
    exact ker_comp_mkQ K.val J hJ

/-- Every kernel of the prescribed codimension occurs among surjections onto
the comparison space, including the zero-dimensional case. -/
theorem fullKernel_surjective :
    Function.Surjective (fullKernel (F := F) (I := I)) := by
  classical
  intro K
  let T : F →ₗ[F2] I := (quotientEquiv K).toLinearMap.comp K.val.mkQ
  have hT : Function.Surjective T :=
    (quotientEquiv K).surjective.comp K.val.mkQ_surjective
  refine ⟨⟨T, hT⟩, ?_⟩
  apply Subtype.ext
  exact ker_comp_mkQ K.val (quotientEquiv K).toLinearMap (quotientEquiv K).injective

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

/-- Changing the domain by a linear equivalence preserves the set of actual
injective linear maps. -/
def injectionEquivOfDomainEquiv (e : J ≃ₗ[F2] I) :
    {u : J →ₗ[F2] E // Function.Injective u} ≃
      {u : I →ₗ[F2] E // Function.Injective u} where
  toFun u := ⟨u.val.comp e.symm.toLinearMap, u.property.comp e.symm.injective⟩
  invFun u := ⟨u.val.comp e.toLinearMap, u.property.comp e.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e.symm (e x)) = u.val x
    rw [e.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e (e.symm x)) = u.val x
    rw [e.apply_symm_apply]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

/-- A fixed-kernel fiber is in explicit bijection with injections from the
comparison space. This includes the zero-dimensional comparison space. -/
def fixedKernelEquivInjection (K : KernelClass F I) :
    {S : F →ₗ[F2] E // S.ker = K.val} ≃
      {J : I →ₗ[F2] E // Function.Injective J} :=
  (fixedKernelEquivQuotientInjection K.val).trans
    (injectionEquivOfDomainEquiv (quotientEquiv K))

/-- Exact fixed-kernel count, without a chosen finite enumeration. -/
theorem natCard_fixedKernel_eq_beta (K : KernelClass F I) :
    Nat.card {S : F →ₗ[F2] E // S.ker = K.val} = beta I E :=
  Nat.card_congr (fixedKernelEquivInjection K)

/-- The kernel condition already forces the rank condition. -/
def rankFiberEquivFixedKernel (K : KernelClass F I) :
    {S : RankFrequency F E I // rankKernel S = K} ≃
      {S : F →ₗ[F2] E // S.ker = K.val} where
  toFun S := ⟨S.val.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨⟨S.val,
    (fixedKernel_finrank_eq_quotient K.val S).trans K.property⟩,
    Subtype.ext S.property⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

omit [FiniteDimensional F2 F] in
/-- A map into the comparison space with this kernel has full range. -/
theorem surjective_of_kernel_class (K : KernelClass F I)
    (T : F →ₗ[F2] I) (hT : T.ker = K.val) : Function.Surjective T := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (fixedKernel_finrank_eq_quotient K.val ⟨T, hT⟩).trans K.property

/-- The kernel condition already forces surjectivity onto the comparison
space. -/
def fullFiberEquivFixedKernel (K : KernelClass F I) :
    {T : FullFrequency F I // fullKernel T = K} ≃
      {T : F →ₗ[F2] I // T.ker = K.val} where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, surjective_of_kernel_class K T.val T.property⟩,
    Subtype.ext T.property⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    rfl

/-- Every rank-frequency kernel fiber has the same actual cardinality. -/
theorem rankKernel_fiber_card [Fintype (F →ₗ[F2] E)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun S : RankFrequency F E I => rankKernel S = K)).card =
      beta I E := by
  calc
    _ = Fintype.card {S : RankFrequency F E I // rankKernel S = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {S : RankFrequency F E I // rankKernel S = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {S : F →ₗ[F2] E // S.ker = K.val} :=
      Nat.card_congr (rankFiberEquivFixedKernel K)
    _ = beta I E := natCard_fixedKernel_eq_beta K

/-- Every surjective-frequency kernel fiber has the square injection count. -/
theorem fullKernel_fiber_card [Fintype (F →ₗ[F2] I)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun T : FullFrequency F I => fullKernel T = K)).card =
      beta I I := by
  calc
    _ = Fintype.card {T : FullFrequency F I // fullKernel T = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {T : FullFrequency F I // fullKernel T = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {T : F →ₗ[F2] I // T.ker = K.val} :=
      Nat.card_congr (fullFiberEquivFixedKernel K)
    _ = beta I I := natCard_fixedKernel_eq_beta K

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The range identification induced by a common kernel. -/
def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

/-- This identification respects every original vector, including vectors in
the kernel and maps of rank zero. -/
theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

/-- Finite-dimensional image suffices: the ambient codomain and domain may
otherwise be infinite-dimensional. -/
theorem exists_postcomp_equiv_of_ker_eq (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] (hker : S.ker = T.ker) :
    ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (rangeEquivOfKerEq S T hker)
  refine ⟨g, ?_⟩
  ext x
  change g (S x) = T x
  exact (hg ⟨S x, ⟨x, rfl⟩⟩).symm.trans (rangeEquivOfKerEq_apply S T hker x)

/-- Invertible postcomposition never changes the kernel. Thus the kernel is
an exact orbit invariant, rather than only a necessary condition. -/
theorem ker_eq_iff_exists_postcomp_equiv (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] :
    S.ker = T.ker ↔ ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  constructor
  · exact exists_postcomp_equiv_of_ker_eq S T
  · rintro ⟨g, rfl⟩
    ext x
    simp

end
end UniqueGamesTheorem.Inverse.KMSKernelOrbits

end

section

namespace UniqueGamesTheorem.Inverse.KMSMomentScalar

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
end UniqueGamesTheorem.Inverse.KMSMomentScalar

end

section

/-! Dimension-independent choices for the KMS low-level/spectral contradiction.
These are scalar choices only; they do not supply the upper moment theorem. -/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open KMSMomentScalar

/-- The level cutoff and pseudorandomness tolerance are selected before either
matrix dimension. The inequality leaves half the retention budget for model
comparison errors. -/
theorem exists_cutoff_parameters {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (r + 1 : ℕ) * ((2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹ ≤ ζ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ζ / 4 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  let r := max 1 N
  let C : ℝ := (2 : ℝ) ^ (7 * r ^ 3 + 3)
  let t : ℝ := min 1 (ζ / (4 * (r + 1 : ℕ) * C))
  let ε : ℝ := t ^ 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 1 ≤ r := le_max_left _ _
  have hden : 0 < 4 * (r + 1 : ℕ) * C := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hζ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hε : 0 < ε := pow_pos ht _
  have hε1 : ε ≤ 1 := pow_le_one₀ ht.le ht1
  have hroot : ε ^ ((1 : ℝ) / 4) = t := by
    have hpow : (ε ^ ((1 : ℝ) / 4)) ^ 4 = t ^ 4 := fourth_root_power hε.le
    have hroot_nonneg : 0 ≤ ε ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hε.le _
    exact le_antisymm (le_of_fourth_power_le hroot_nonneg ht.le hpow.le)
      (le_of_fourth_power_le ht.le hroot_nonneg hpow.symm.le)
  have hlow : (r + 1 : ℕ) * (C * ε ^ ((1 : ℝ) / 4)) ≤ ζ / 4 := by
    rw [hroot]
    have ht' : t ≤ ζ / (4 * (r + 1 : ℕ) * C) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp ht'
    nlinarith only [hm]
  have htail : ((2 : ℝ) ^ (r + 1))⁻¹ < ζ / 4 := by
    have hmon : (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right 1 N) (Nat.le_succ r))
    simpa only [one_div, inv_pow] using hmon.trans_lt hN
  refine ⟨r, hr, ε, hε, hε1, ?_⟩
  change (r + 1 : ℕ) * (C * ε ^ ((1 : ℝ) / 4)) + _ ≤ ζ / 2
  linarith

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

end OAI
