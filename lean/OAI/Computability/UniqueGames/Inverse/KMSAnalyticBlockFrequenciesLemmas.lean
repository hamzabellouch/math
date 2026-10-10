import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedScalarLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentZoomInAlgebraLemmas
import OAI.Computability.UniqueGames.Inverse.KMSKernelOrbitsFourierLemmas

namespace OAI

section

/-!
# Compatible block frequencies

A compatible surjection on `B × F2` has a unique old surjection and a new
vector in the kernel of the partial projection. The new vector does not
change its kernel. Consequently actual basis-invariant Fourier coefficients
are constant along this fiber, yielding its exact energy multiplicity.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

/-- Adjoin a new identity coordinate and an arbitrary off-diagonal vector. -/
def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

theorem blockFrequency_surjective_iff (z : B →ₗ[F2] J) (w : J) :
    Function.Surjective (blockFrequency z w) ↔ Function.Surjective z := by
  constructor
  · intro h y
    obtain ⟨⟨b, c⟩, hx⟩ := h (y, 0)
    have hc : c = 0 := congrArg Prod.snd hx
    refine ⟨b, ?_⟩
    simpa only [blockFrequency_apply, hc, zero_smul, add_zero] using congrArg Prod.fst hx
  · intro h x
    obtain ⟨b, hb⟩ := h (x.1 - x.2 • w)
    refine ⟨(b, x.2), ?_⟩
    simp only [blockFrequency_apply, hb, sub_add_cancel, Prod.eta]

/-- The kernel is independent of the off-diagonal vector, without any
surjectivity assumption. -/
theorem ker_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    (blockFrequency z w).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  ext ⟨b, c⟩
  change ((z b + c • w, c) = (0, 0)) ↔ (z b = 0 ∧ c = 0)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by simpa using h, rfl⟩
  · rintro ⟨h, rfl⟩
    simpa using h

theorem blockFrequency_compatible_iff (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (z : B →ₗ[F2] J) (w : J) :
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp (blockFrequency z w) =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) ↔ π.comp z = A ∧ π w = 0 := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro b
      simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (b, 0)).1) h
    · simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (0, 1)).1) h
  · rintro ⟨hz, hw⟩
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : π (z b) = A b := congrArg (fun T : B →ₗ[F2] K => T b) hz
    simp [hb, hw]

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

theorem blockFrequency_recover (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (T : (B × F2) →ₗ[F2] (J × F2))
    (hT : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) :
    blockFrequency (blockOld T) (blockNew T) = T := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun R : (B × F2) →ₗ[F2] J => R x)
      (hyperplaneExtend_recover ((LinearMap.fst F2 J F2).comp T))
  · have h := congrArg (fun R : (B × F2) →ₗ[F2] (K × F2) => (R x).2) hT
    exact h.symm

abbrev CompatibleBlockFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {T : (B × F2) →ₗ[F2] (J × F2) // Function.Surjective T ∧
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)}

abbrev CompatibleOldFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {z : B →ₗ[F2] J // Function.Surjective z ∧ π.comp z = A}

/-- The actual compatible frequency fiber, with its exact kernel-vector parameter. -/
def compatibleBlockFrequencyEquiv (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    CompatibleBlockFrequency π A ≃ CompatibleOldFrequency π A × π.ker where
  toFun T := by
    have hr := blockFrequency_recover π A T.val T.property.2
    have hc : π.comp (blockOld T.val) = A ∧ π (blockNew T.val) = 0 :=
      (blockFrequency_compatible_iff π A _ _).mp (by rw [hr]; exact T.property.2)
    refine (⟨blockOld T.val, ?_, hc.1⟩, ⟨blockNew T.val, hc.2⟩)
    apply (blockFrequency_surjective_iff (blockOld T.val) (blockNew T.val)).mp
    rw [hr]
    exact T.property.1
  invFun p := ⟨blockFrequency p.1.val p.2.val,
    (blockFrequency_surjective_iff _ _).mpr p.1.property.1,
    (blockFrequency_compatible_iff π A _ _).mpr ⟨p.1.property.2, p.2.property⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact blockFrequency_recover π A T.val T.property.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact blockOld_blockFrequency _ _
    · apply Subtype.ext
      exact blockNew_blockFrequency _ _

section Fourier
variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

/-- Actual lifted coefficients are independent of the block vector. -/
theorem coefficient_blockFrequency_eq (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] J) (u v : J) :
    linearCoeff f (ι.comp (blockFrequency z u)) =
      linearCoeff f (ι.comp (blockFrequency z v)) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    ker_blockFrequency, ker_blockFrequency]

variable [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype ((J × F2) →ₗ[F2] (B × F2))] in
/-- Exact collapse of the new-coordinate fiber in the prescribed-frequency
energy. The multiplier is the actual number of vectors in `ker π`. -/
theorem fixedFrequencyEnergy_block (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
      (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
      (Fintype.card π.ker : ℝ) * ∑ z : CompatibleOldFrequency π A,
        linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2 := by
  let e := compatibleBlockFrequencyEquiv π A
  calc
    _ = ∑ T : CompatibleBlockFrequency π A, linearCoeff f (ι.comp T.val) ^ 2 := by
      unfold fixedFrequencyEnergy
      rw [← Finset.sum_subtype (Finset.univ.filter (fun T : (B × F2) →ₗ[F2] (J × F2) =>
          Function.Surjective T ∧
            (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
              A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))) (by simp)
          (fun T => linearCoeff f (ι.comp T) ^ 2),
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hs : Function.Surjective T <;>
        by_cases hp : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
            A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) <;> simp [smallCoeff, hs, hp]
    _ = ∑ p : CompatibleOldFrequency π A × π.ker,
        linearCoeff f (ι.comp (blockFrequency p.1.val p.2.val)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro T
      exact congrArg (fun R : (B × F2) →ₗ[F2] (J × F2) =>
        linearCoeff f (ι.comp R) ^ 2) (congrArg Subtype.val (e.symm_apply_apply T)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [coefficient_blockFrequency_eq ι hι f hf _ _ 0]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

end Fourier
end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! The zero-fixed-character base of KMS's restricted Fourier induction,
with the actual injection-count ratio and homogeneous squared-density bound.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

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

omit [Finite F] in
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

omit [Finite F] in
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
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Transport of the primal codomain

An equivalence of primal codomains gives a unique frequency in the Fourier
pullback fiber. The resulting exact coefficient identity transports both
the small component and its prescribed-frequency energy. No invariance or
analytic estimate is needed for these identities.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainTransport (e : F ≃ₗ[F2] F') (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F') → ℝ := fun X => f (e.symm.toLinearMap.comp X)

/-- Actual dual frequencies are reindexed by precomposition with the inverse. -/
def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

theorem surjective_comp_codomainEquiv_iff (e : F ≃ₗ[F2] F') (T : F' →ₗ[F2] I) :
    Function.Surjective (T.comp e.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨e x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨e.symm x, ?_⟩
    simpa using hx

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)]

omit [Fintype (F' →ₗ[F2] E)] in
/-- The Fourier pullback fiber of a codomain equivalence has a single term. -/
theorem linearCoeff_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (S' : F' →ₗ[F2] E) :
    linearCoeff (codomainTransport e f) S' = linearCoeff f (S'.comp e.toLinearMap) := by
  unfold codomainTransport
  rw [KMSFourthMoment.coefficient_codomain_pullback]
  have hc : (S'.comp e.toLinearMap).comp e.symm.toLinearMap = S' := by ext x; simp
  rw [Finset.sum_eq_single (S'.comp e.toLinearMap)]
  · rw [ite_eq_left hc]
  · intro S _ hS
    apply ite_eq_right
    intro h
    apply hS
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun R : F' →ₗ[F2] E => R (e x)) h
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)] in
/-- Codomain transport preserves the original basis invariance. -/
theorem basisInvariant_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (codomainTransport e f) := by
  intro g X
  change f (e.symm.toLinearMap.comp (X.comp g.toLinearMap)) =
    f (e.symm.toLinearMap.comp X)
  rw [← LinearMap.comp_assoc]
  exact hf g (e.symm.toLinearMap.comp X)

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [Fintype (F' →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)] in
theorem smallCoeff_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F' →ₗ[F2] I) :
    smallCoeff ι (codomainTransport e f) T =
      smallCoeff ι f (T.comp e.toLinearMap) := by
  unfold smallCoeff
  rw [surjective_comp_codomainEquiv_iff]
  split_ifs
  · rw [linearCoeff_codomainTransport, LinearMap.comp_assoc]
  · rfl

omit [Fintype (F' →ₗ[F2] E)] in
/-- The synthesized small component itself commutes with codomain transport. -/
theorem smallComponent_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent ι (codomainTransport e f) =
      codomainTransport e (smallComponent ι f) := by
  apply eq_of_coeff_eq
  intro T
  rw [coeff_smallComponent, linearCoeff_codomainTransport, coeff_smallComponent,
    smallCoeff_codomainTransport]

omit [FiniteDimensional F2 I] [Fintype (F' →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (I →ₗ[F2] F')] in
/-- Transport the prescribed partial frequency together with the primal
codomain; the normalized energy remains exactly unchanged. -/
theorem fixedFrequencyEnergy_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι (codomainTransport e f) π (A.comp e.symm.toLinearMap) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (codomainFrequencyEquiv (I := I) e)
  intro T
  have hp : π.comp (T.comp e.symm.toLinearMap) = A.comp e.symm.toLinearMap ↔
      π.comp T = A := by
    rw [← LinearMap.comp_assoc]
    exact (codomainFrequencyEquiv (I := J) e).injective.eq_iff
  simp only [codomainFrequencyEquiv_apply, smallCoeff_codomainTransport,
    codomainFrequency_cancel, hp]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
The dependent branches in the KMS fixed-character recursion inject into the
lower-rank restricted Fourier sum. The new coordinate value is kept fixed,
so no multiplicity or ambient-dimension loss is introduced here.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

/-- Fixing the new coordinate still allows recovery of the entire old map. -/
theorem hyperplaneExtend_old_injective (w : J) :
    Function.Injective (fun z : B →ₗ[F2] J => hyperplaneExtend z w) := by
  intro z z' h
  have hc := congrArg
    (fun T : (B × F2) →ₗ[F2] J => T.comp (LinearMap.inl F2 B F2)) h
  simpa only [hyperplaneExtend_comp_inl] using hc

/-- A surjective old frequency stays surjective after any new coordinate. -/
theorem hyperplaneExtend_surjective {z : B →ₗ[F2] J}
    (hz : Function.Surjective z) (w : J) :
    Function.Surjective (hyperplaneExtend z w) := by
  intro y
  obtain ⟨b, hb⟩ := hz y
  refine ⟨(b, 0), ?_⟩
  simpa using hb

/-- The fixed partial frequency extends by its actual projected new value. -/
theorem comp_hyperplaneExtend (π : J →ₗ[F2] K) (z : B →ₗ[F2] J) (w : J) :
    π.comp (hyperplaneExtend z w) = hyperplaneExtend (π.comp z) (π w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [LinearMap.comp_apply]

section Energy
variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
/-- Each fixed dependent extension branch is bounded by the genuine restricted
small-component energy. There is no hidden cardinality factor. -/
theorem dependent_extension_energy_le
    (ι : J →ₗ[F2] E) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (π : J →ₗ[F2] K) (A0 : B →ₗ[F2] K) (w : J) :
    (∑ z : B →ₗ[F2] J with π.comp z = A0 ∧ Function.Surjective z,
      linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
        fixedFrequencyEnergy ι f π (hyperplaneExtend A0 (π w)) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A0 ∧ Function.Surjective z
  let Q : Finset ((B × F2) →ₗ[F2] J) :=
    Finset.univ.filter fun T =>
      π.comp T = hyperplaneExtend A0 (π w) ∧ Function.Surjective T
  have hsub : P.image (fun z => hyperplaneExtend z w) ⊆ Q := by
    intro T hT
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hT
    have hp := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hyperplaneExtend_surjective hp.2 w⟩
    rw [comp_hyperplaneExtend, hp.1]
  rw [fixedFrequencyEnergy_eq]
  change (∑ z ∈ P, linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
    ∑ T ∈ Q, linearCoeff f (ι.comp T) ^ 2
  calc
    _ = ∑ T ∈ P.image (fun z => hyperplaneExtend z w),
        linearCoeff f (ι.comp T) ^ 2 := by
      rw [Finset.sum_image]
      exact fun z _ z' _ h => hyperplaneExtend_old_injective w h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun T _ _ => sq_nonneg _)

end Energy
end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Coordinate and budget transport for the genuine homogeneous character
induction. These statements only change presentations of the actual local
squared-density hypothesis and prescribed Fourier sums. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w x y
variable {E : Type u} {F F' : Type v} {I : Type w} {J : Type x} {J' : Type y}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup J'] [Module F2 J']

theorem HomogeneousRestrictionBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : HomogeneousRestrictionBound s ε f) :
    HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ L hL hd
  exact hf C L hL (by omega)

theorem HomogeneousRestrictionBound.codomain_equiv
    [FiniteDimensional F2 F] [FiniteDimensional F2 F']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) (e : F ≃ₗ[F2] F') :
    HomogeneousRestrictionBound r ε (codomainTransport e f) := by
  intro C _ _ _ _ L hL hd
  have hd' : Module.finrank F2 F ≤ Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hd
  simpa only [codomainTransport, LinearMap.comp_assoc] using
    hf C (e.symm.toLinearMap.comp L) (e.symm.injective.comp hL) hd'

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_postcomp_injective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J)
    (e : J →ₗ[F2] J') (he : Function.Injective e) :
    fixedFrequencyEnergy ι f (e.comp π) (e.comp A) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    exact he (congrArg (fun L : F →ₗ[F2] J' => L x) h)
  · intro h
    rw [LinearMap.comp_assoc, h]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Transport of the small component between equivalent coordinate spaces

The embedding and partial projection are transported together. Thus the
lifted frequency and its prescribed partial value remain literally the same.
Finite reindexing proves exact coefficient, function, and restricted-energy
identities without requiring basis invariance of the original function.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

/-- Reindex the actual dual frequency maps by an equivalence of their targets. -/
def smallFrequencyEquiv (e : I ≃ₗ[F2] I') : (F →ₗ[F2] I) ≃ (F →ₗ[F2] I') where
  toFun T := e.toLinearMap.comp T
  invFun T := e.symm.toLinearMap.comp T
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem smallFrequencyEquiv_apply (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    smallFrequencyEquiv e T = e.toLinearMap.comp T := rfl

theorem surjective_smallFrequencyEquiv_iff (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    Function.Surjective (e.toLinearMap.comp T) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    exact ⟨x, e.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨x, ?_⟩
    change e (T x) = y
    rw [hx, e.apply_symm_apply]

/-- Transporting the outer map in the opposite direction cancels the
frequency-coordinate change. -/
theorem smallFrequency_transport_comp (e : I ≃ₗ[F2] I') (π : I →ₗ[F2] J)
    (T : F →ₗ[F2] I) :
    (π.comp e.symm.toLinearMap).comp (e.toLinearMap.comp T) = π.comp T := by
  ext x
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')] in
/-- Exact coefficient transport; the embedding need not be injective and
the original function need not be basis invariant. -/
theorem smallCoeff_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (ι.comp e.symm.toLinearMap) f (e.toLinearMap.comp T) =
      smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_smallFrequencyEquiv_iff, smallFrequency_transport_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in
/-- Prescribed partial-frequency energy is unchanged when its projection
and embedding are both transported to the new small space. -/
theorem fixedFrequencyEnergy_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy (ι.comp e.symm.toLinearMap) f
      (π.comp e.symm.toLinearMap) A = fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallFrequency_transport_comp,
    smallCoeff_transport]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in
/-- The actual small-space functions agree under the corresponding primal
coordinate pullback. -/
theorem smallComponent_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I' →ₗ[F2] F) :
    smallComponent (ι.comp e.symm.toLinearMap) f X =
      smallComponent ι f (X.comp e.toLinearMap) := by
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallCoeff_transport,
    linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in
/-- The same function identity with the new embedding written as `ι ∘ g`. -/
theorem smallComponent_precomp_equiv (g : I ≃ₗ[F2] I') (ι : I' →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I →ₗ[F2] F) :
    smallComponent (ι.comp g.toLinearMap) f X =
      smallComponent ι f (X.comp g.symm.toLinearMap) := by
  simpa only [LinearEquiv.symm_symm] using smallComponent_transport g.symm ι f X

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
KMS Lemma 3.8 in coordinates with the newly fixed column last. The correction
sum runs over the dual of the smaller coordinate space. This is exactly one
representative of each graph subspace, so there is no basis-counting factor.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

theorem sum_dependentRows [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, if ¬ Function.Surjective (T.prod ell) then g ell else 0) =
      ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  calc
    _ = ∑ ell ∈ Finset.univ.filter (fun ell => ¬ Function.Surjective (T.prod ell)),
        g ell := (Finset.sum_filter _ _).symm
    _ = ∑ ell : {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)},
        g ell.val := Finset.sum_subtype _ (by simp) _
    _ = _ := ((dependentRowEquiv T hT).sum_comp (fun ell => g ell.val)).symm

theorem sum_rows_split [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, g ell) =
      (∑ ell, if Function.Surjective (T.prod ell) then g ell else 0) +
        ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  rw [← sum_dependentRows T hT g, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases h : Function.Surjective (T.prod ell) <;> simp [h]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 J]
  [Fintype ((E × F2) →ₗ[F2] F)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 J] in
/-- A dependent row changes the embedding, but not its frequency kernel. -/
theorem coeff_dependent_extension (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (φ : J →ₗ[F2] F2) :
    linearCoeff f ((ι.comp T).prod (φ.comp T)) =
      linearCoeff f ((pointPad ι).comp T) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  ext x
  change (ι (T x), φ (T x)) = (0, 0) ↔ (ι (T x), (0 : F2)) = (0, 0)
  constructor
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    exact Prod.ext hfst rfl
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    have hTx : T x = 0 := hι (by simpa using hfst)
    simp [hTx]

variable [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]

omit [FiniteDimensional F2 J] in
/-- The precise rowwise identity before Fourier synthesis. -/
theorem point_row_recursion (ι : J →ₗ[F2] E) (hι : Function.Injective ι)
    (f : ((E × F2) →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (X : J →ₗ[F2] F) (a : F) :
    (∑ ell : F →ₗ[F2] F2,
      linearCoeff f ((ι.comp T).prod ell) * (binarySign (ell a)).re) *
        (linearTraceCharacter T X).re =
      (∑ ell : F →ₗ[F2] F2,
        (if Function.Surjective (T.prod ell)
          then linearCoeff f ((ι.comp T).prod ell) else 0) *
            (linearTraceCharacter (T.prod ell) (pointAppend X a)).re) +
      ∑ φ : J →ₗ[F2] F2, linearCoeff f ((pointPad ι).comp T) *
        (linearTraceCharacter T (X + φ.smulRight a)).re := by
  calc
    _ = ∑ ell : F →ₗ[F2] F2, linearCoeff f ((ι.comp T).prod ell) *
        (linearTraceCharacter (T.prod ell) (pointAppend X a)).re := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ell _
      rw [character_pointAppend]
      ring
    _ = _ := by
      rw [sum_rows_split T hT]
      congr 1
      · apply Finset.sum_congr rfl
        intro ell _
        split_ifs <;> simp
      · apply Finset.sum_congr rfl
        intro φ _
        rw [coeff_dependent_extension ι hι f hf, character_pointAppend,
          character_pointShift]
        rfl

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (J →ₗ[F2] F)] [Fintype (F →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 J]
  [Fintype (J →ₗ[F2] F)] [Fintype ((J × F2) →ₗ[F2] F)] in
/-- One-column point restriction, with the dependent-row correction added
back. This identity applies in every dimension, including zero. -/
theorem point_restriction_recursion_add (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent ι (pointRestrict f a) X =
      smallComponent (pointLift ι) f (pointAppend X a) +
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  simp only [smallComponent, synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_frequency_prod (fun S : F →ₗ[F2] (J × F2) =>
    smallCoeff (pointLift ι) f S * (linearTraceCharacter S (pointAppend X a)).re)]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (J →ₗ[F2] F2)))
    (t := (Finset.univ : Finset (F →ₗ[F2] J))), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T
  · simp only [smallCoeff, hT, ite_true, coeff_pointRestrict, pointLift_comp_prod]
    exact point_row_recursion ι hι f hf T hT X a
  · have hprod : ∀ ell : F →ₗ[F2] F2, ¬ Function.Surjective (T.prod ell) :=
      fun ell h => hT (surjective_of_surjective_prod T ell h)
    simp [smallCoeff, hT, hprod]

omit [FiniteDimensional F2 J]
  [Fintype (J →ₗ[F2] F)] [Fintype ((J × F2) →ₗ[F2] F)] in
/-- KMS Lemma 3.8: the full-rank component after adjoining one coordinate
is the restricted component minus the sum of all dependent graph terms. -/
theorem point_restriction_recursion (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent (pointLift ι) f (pointAppend X a) =
      smallComponent ι (pointRestrict f a) X -
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  have h := point_restriction_recursion_add ι hι f hf X a
  linarith

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
