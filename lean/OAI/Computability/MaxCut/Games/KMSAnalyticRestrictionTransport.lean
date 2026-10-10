import Mathlib
import OAI.Computability.MaxCut.Games.KMSAnalyticFrequencyShift

namespace OAI

/-! Coordinate and budget transport for the genuine homogeneous character
induction. These statements only change presentations of the actual local
squared-density hypothesis and prescribed Fourier sums. -/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
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
end MaxCutGames.Inverse.KMSAnalytic

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

namespace MaxCutGames.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Split off the coordinate measured by `a`, using the prescribed vector `t`.
The kernel coordinate is exactly `x - a x • t`. -/
def splitEquiv (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    F ≃ₗ[K] (a.ker × K) where
  toFun x := (⟨x - a x • t, by simp [LinearMap.mem_ker, ht]⟩, a x)
  invFun p := (p.1 : F) + p.2 • t
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - a (x + y) • t = (x - a x • t) + (y - a y • t)
      rw [map_add, add_smul]
      abel
    · exact a.map_add x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - a (c • x) • t = c • (x - a x • t)
      simp [smul_sub, smul_smul]
    · exact a.map_smul c x
  left_inv x := by
    change x - a x • t + a x • t = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : a (p.1 : F) = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : F) + p.2 • t - a ((p.1 : F) + p.2 • t) • t = p.1
      simp [hp, ht]
    · change a ((p.1 : F) + p.2 • t) = p.2
      simp [hp, ht]

@[simp] theorem splitEquiv_apply_snd (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    (splitEquiv a t ht x).2 = a x := rfl

@[simp] theorem splitEquiv_apply_fst_coe (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    ((splitEquiv a t ht x).1 : F) = x - a x • t := rfl

@[simp] theorem splitEquiv_symm_apply (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (p : a.ker × K) :
    (splitEquiv a t ht).symm p = (p.1 : F) + p.2 • t := rfl

@[simp] theorem splitEquiv_symm_apply_zero (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : (splitEquiv a t ht).symm (b, 0) = (b : F) := by
  simp

@[simp] theorem splitEquiv_apply_ker (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : splitEquiv a t ht (b : F) = (b, 0) := by
  apply (splitEquiv a t ht).symm.injective
  simp

@[simp] theorem splitEquiv_apply_unit (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    splitEquiv a t ht t = (0, 1) := by
  apply (splitEquiv a t ht).symm.injective
  simp

/-- A functional with a unit preimage has a kernel of codimension one. -/
theorem finrank_eq_ker_add_one [FiniteDimensional K F]
    (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    Module.finrank K F = Module.finrank K a.ker + 1 := by
  have h := (splitEquiv a t ht).finrank_eq
  simpa [Module.finrank_prod] using h

end MaxCutGames.Inverse.KMSAnalyticFunctionalSplit

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

namespace MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

/-- Data of one common coordinate and compatible section vectors. All maps
and all smaller spaces below are constructed from these original data. -/
structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def targetEquiv (s : CompatibleSplitting π A) : K ≃ₗ[F2] (s.K0 × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv s.functional s.targetVector
    s.functional_targetVector

def leftEquiv (s : CompatibleSplitting π A) : I ≃ₗ[F2] (s.J × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

def rightEquiv (s : CompatibleSplitting π A) : F ≃ₗ[F2] (s.B × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

/-- The remaining part of the left surjection is its literal restriction. -/
def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

/-- The remaining part of the right surjection is its literal restriction. -/
def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

@[simp] theorem leftMap_apply_val (s : CompatibleSplitting π A) (x : s.J) :
    (s.leftMap x : K) = π x := rfl

@[simp] theorem rightMap_apply_val (s : CompatibleSplitting π A) (x : s.B) :
    (s.rightMap x : K) = A x := rfl

theorem leftMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.leftMap := by
  intro y
  obtain ⟨x, hx⟩ := s.left_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (π x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

theorem rightMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.rightMap := by
  intro y
  obtain ⟨x, hx⟩ := s.right_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (A x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

@[simp] theorem leftEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    s.leftEquiv.symm x = (x.1 : I) + x.2 • s.leftVector := rfl

@[simp] theorem rightEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    s.rightEquiv.symm x = (x.1 : F) + x.2 • s.rightVector := rfl

@[simp] theorem targetEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.K0 × F2) :
    s.targetEquiv.symm x = (x.1 : K) + x.2 • s.targetVector := rfl

theorem left_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    π (s.leftEquiv.symm x) = s.targetEquiv.symm (s.leftMap x.1, x.2) := by
  change π ((x.1 : I) + x.2 • s.leftVector) = π x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.leftVector_image]

theorem right_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    A (s.rightEquiv.symm x) = s.targetEquiv.symm (s.rightMap x.1, x.2) := by
  change A ((x.1 : F) + x.2 • s.rightVector) = A x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.rightVector_image]

/-- Both changes of coordinates use the same final binary coordinate. -/
theorem left_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (π.comp s.leftEquiv.symm.toLinearMap) =
      s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (π (s.leftEquiv.symm x)) = (s.leftMap x.1, x.2)
  rw [s.left_symm_apply, s.targetEquiv.apply_symm_apply]

theorem right_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (A.comp s.rightEquiv.symm.toLinearMap) =
      s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (A (s.rightEquiv.symm x)) = (s.rightMap x.1, x.2)
  rw [s.right_symm_apply, s.targetEquiv.apply_symm_apply]

theorem target_finrank [FiniteDimensional F2 K] (s : CompatibleSplitting π A) :
    Module.finrank F2 K = Module.finrank F2 s.K0 + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one s.functional s.targetVector
    s.functional_targetVector

theorem left_finrank [FiniteDimensional F2 I] (s : CompatibleSplitting π A) :
    Module.finrank F2 I = Module.finrank F2 s.J + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

theorem right_finrank [FiniteDimensional F2 F] (s : CompatibleSplitting π A) :
    Module.finrank F2 F = Module.finrank F2 s.B + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

end CompatibleSplitting

/-- Positive target dimension supplies a basis coordinate; surjectivity
supplies its two lifts. No additional splitting hypothesis is required. -/
theorem exists_compatibleSplitting [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : Nonempty (CompatibleSplitting π A) := by
  classical
  let b := Module.finBasis F2 K
  let j : Fin (Module.finrank F2 K) := ⟨0, hdim⟩
  obtain ⟨i, hi⟩ := hπ (b j)
  obtain ⟨f, hf⟩ := hA (b j)
  refine ⟨⟨b.coord j, b j, ?_, i, hi, f, hf, hπ, hA⟩⟩
  simp

def chooseSplit [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : CompatibleSplitting π A :=
  Classical.choice (exists_compatibleSplitting π A hπ hA hdim)

end
end MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

universe u v w x

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {E : Type u} [AddCommGroup E] [Module F2 E]
  [FiniteDimensional F2 E] [Fintype E]

private theorem fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction :
    ∀ (n : ℕ) (F : Type v) [AddCommGroup F] [Module F2 F]
      [FiniteDimensional F2 F] [Fintype F]
      (I : Type w) [AddCommGroup I] [Module F2 I]
      [FiniteDimensional F2 I] [Fintype I]
      (J : Type x) [AddCommGroup J] [Module F2 J]
      [FiniteDimensional F2 J] [Fintype J],
      Module.finrank F2 J = n →
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), IsBasisInvariant f →
      ∀ (ε : ℝ), HomogeneousRestrictionBound (Module.finrank F2 I) ε f →
      ∀ (π : I →ₗ[F2] J), Function.Surjective π → ∀ A : F →ₗ[F2] J,
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
          fixedFrequencyEnergy ι f π A ≤
        (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F _ _ _ _ I _ _ _ _ J _ _ _ _ hJn ι hι f hf ε hg π hπ A
    let : Finite (KMSKernelFiberCard.KernelClass F I) :=
      Finite.of_surjective (KMSKernelFiberCard.fullKernel (F := F) (I := I))
        (KMSKernelFiberCard.fullKernel_surjective (F := F) (I := I))
    let : Fintype (KMSKernelFiberCard.KernelClass F I) := Fintype.ofFinite _
    have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans
      (HomogeneousRestrictionBound.energy_le _ ε f hg)
    by_cases hn : n = 0
    · exact fixedFrequencyEnergy_zero_dim_bound ι hι f hf ε hg π A (hJn.trans hn)
    by_cases hA : Function.Surjective A
    · have hp : 0 < Module.finrank F2 J := by omega
      let s := KMSAnalyticCompatibleSplitting.chooseSplit π A hπ hA hp
      let ι' : (s.J × F2) →ₗ[F2] E := ι.comp s.leftEquiv.symm.toLinearMap
      let f' : (E →ₗ[F2] (s.B × F2)) → ℝ := codomainTransport s.rightEquiv f
      have hι' : Function.Injective ι' := hι.comp s.leftEquiv.symm.injective
      have hf' : IsBasisInvariant f' := basisInvariant_codomainTransport s.rightEquiv f hf
      have hg' : HomogeneousRestrictionBound (Module.finrank F2 s.J + 1) ε f' := by
        have h := HomogeneousRestrictionBound.codomain_equiv _ ε f hg s.rightEquiv
        simpa only [s.left_finrank] using h
      have hs : Module.finrank F2 s.K0 < n := by
        have hdim : Module.finrank F2 J = Module.finrank F2 s.K0 + 1 := s.target_finrank
        omega
      have hgfirst : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε
          (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X)) :=
        HomogeneousRestrictionBound.codomain_pullback _ 1 ε f' hg'
          (LinearMap.inl F2 s.B F2) (by intro x y h; exact congrArg Prod.fst h)
          (by simp only [Module.finrank_prod, Module.finrank_self]; omega)
      have hglower : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε f' :=
        HomogeneousRestrictionBound.mono (Nat.le_succ _) ε f' hg'
      have hfirst := ih (Module.finrank F2 s.K0) hs s.B s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι')
        (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X))
        (basisInvariant_codomain_pullback f' hf' (LinearMap.inl F2 s.B F2))
        ε hgfirst s.leftMap s.leftMap_surjective s.rightMap
      have hlower (w : s.J) := ih (Module.finrank F2 s.K0) hs (s.B × F2) s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι') f' hf'
        ε hglower s.leftMap s.leftMap_surjective (hyperplaneExtend s.rightMap (s.leftMap w))
      have hrec := fixedFrequencyEnergy_product_bound ι' hι' f' hf'
        s.leftMap s.rightMap ε hε hfirst hlower
      have htransport : fixedFrequencyEnergy ι' f'
          (s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
          fixedFrequencyEnergy ι f π A := by
        rw [← s.left_conjugation, ← s.right_conjugation,
          fixedFrequencyEnergy_postcomp_injective _ _ _ _ s.targetEquiv.toLinearMap
            s.targetEquiv.injective]
        change fixedFrequencyEnergy (ι.comp s.leftEquiv.symm.toLinearMap)
          (codomainTransport s.rightEquiv f) (π.comp s.leftEquiv.symm.toLinearMap)
          (A.comp s.rightEquiv.symm.toLinearMap) = _
        rw [fixedFrequencyEnergy_codomainTransport, fixedFrequencyEnergy_transport]
      rw [htransport, ← s.leftEquiv.finrank_eq, ← s.targetEquiv.finrank_eq] at hrec
      exact hrec
    · rw [fixedFrequencyEnergy_eq_zero_of_not_surjective ι f π hπ A hA, mul_zero]
      positivity

/-- KMS's fixed-character estimate, with actual homogeneous restriction
control. The injection is the only ambient-dimension assumption. -/
theorem fixedFrequencyEnergy_le_of_homogeneous
    {F : Type v} [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 F] [Fintype F]
    {I : Type w} [AddCommGroup I] [Module F2 I]
    [FiniteDimensional F2 I] [Fintype I]
    {J : Type x} [AddCommGroup J] [Module F2 J]
    [FiniteDimensional F2 J] [Fintype J]
    (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (ε : ℝ) (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π) (A : F →ₗ[F2] J) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε :=
  fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction (Module.finrank F2 J) F I J rfl ι hι f hf ε hg π hπ A

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

universe u v
attribute [local instance] mapFintype

variable {E A I J : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 A]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J] [FiniteDimensional F2 F]
  [Fintype E] [Fintype A] [Fintype I] [Fintype J] [Fintype F]

/-- KMS's mixed bound with an explicit safe rank-dependent constant. Fixed
points and fixed characters are arbitrary; their independence is not assumed. -/
theorem mixed_slice_bound (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ Module.finrank F2 A * ε := by
  have hi : Module.finrank F2 I ≤ R := by omega
  have hpow : (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) ≤
      2 ^ (4 * R * R) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hi
  apply mixed_bound_of_character_bound R ((2 : ℝ) ^ (4 * R * R)) ε
    (by positivity) hε π ν hπ ?_ (Module.finrank F2 A) E A rfl ι hι f hf hd a hr
  intro E' _ _ _ _ κ hκ g hg hgd
  exact (fixedFrequencyEnergy_le_of_homogeneous κ hκ g hg ε
    (AffineDensityBound.homogeneous _ ε g hgd) π hπ ν).trans
      (mul_le_mul_of_nonneg_right hpow hε)

/-- A single uniform constant for all fixed-point dimensions at rank at most R. -/
def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

theorem mixedRankConstant_nonneg (R : ℕ) : 0 ≤ mixedRankConstant R := by
  unfold mixedRankConstant
  exact mul_nonneg (by positivity) (pow_nonneg (mixedStepFactor_nonneg R) _)

theorem mixed_slice_bound_uniform (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        mixedRankConstant R * ε := by
  apply (mixed_slice_bound R ε hε ι hι f hf hd a π hπ ν hr).trans
  unfold mixedRankConstant
  have hp : mixedStepFactor R ^ Module.finrank F2 A ≤ mixedStepFactor R ^ R :=
    pow_le_pow_right₀ (one_le_mixedStepFactor R) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) hε

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

universe u v w

/-- A consistent finite enumeration of actual binary linear maps, built from
the finite vertex spaces. This is the enumeration used by the mixed theorem. -/
@[instance_reducible]
def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

/-- All mixed small-component slices of total degree at most `r`, with their
exact ambient normalization weight. No Hybrid derivative bound is included
in this property. Fixed primal points and prescribed frequencies are arbitrary. -/
def UniformMixedBound (r : ℕ) (L : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A I J : Type u)
    [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I] [Fintype I]
    [AddCommGroup J] [Module F2 J] [FiniteDimensional F2 J] [Fintype J],
    ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
    ∀ (a : A →ₗ[F2] F) (π : I →ₗ[F2] J), Function.Surjective π →
    ∀ (ν : F →ₗ[F2] J), Module.finrank F2 A + Module.finrank F2 I ≤ r →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent ι f) a) ≤ L

section Transport

variable {E' : Type u} {F' : Type w}
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype E'] [Fintype F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- Ambient and codomain coordinate pullback preserves every actual mixed
slice, while the exponent is unchanged by ambient dimension invariance. -/
theorem UniformMixedBound.pullback {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : UniformMixedBound r L f) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι u π hπ ν hr
  rw [sliceEnergy_partialRestrict_smallComponent_pullback a b ι f π ν u,
    a.finrank_eq]
  exact hf A I J (a.toLinearMap.comp ι) (a.injective.comp hι)
    (b.toLinearMap.comp u) π hπ (ν.comp b.symm.toLinearMap) hr

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- The uniform mixed property is independent of both ambient coordinate
choices. The reverse direction is pullback by the inverse equivalences. -/
theorem UniformMixedBound.pullback_iff {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) ↔
      UniformMixedBound r L f := by
  constructor
  · intro hf
    have h := UniformMixedBound.pullback a.symm b.symm
      (fun M => f (LinearEquiv.arrowCongr a b M)) hf
    have he : (fun M : E' →ₗ[F2] F' =>
        f (LinearEquiv.arrowCongr a b (LinearEquiv.arrowCongr a.symm b.symm M))) = f := by
      funext M
      apply congrArg f
      apply LinearMap.ext
      intro x
      change b (b.symm (M (a (a.symm x)))) = M x
      simp
    rw [he] at h
    exact h
  · exact UniformMixedBound.pullback a b f

end Transport

/-- The proved KMS mixed estimate discharges every instance of the uniform
mixed property. Only the actual affine density and basis-invariance
hypotheses remain; no Fourier or Hybrid estimate is supplied as a premise. -/
theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound r ε f) :
    UniformMixedBound r (mixedRankConstant r * ε) f := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι a π hπ ν hr
  exact mixed_slice_bound_uniform r ε hε ι hι f hf
    (AffineDensityBound.mono hr ε f hd) a π hπ ν hr

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

noncomputable section
namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open MaxCutGames.Fourier.MatrixRestrictions
open KMSAnalytic KMSFourthMoment

universe u

attribute [local instance] mapFintype

section Product
variable {A U B C : Type u}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- Each image-adapted slice in the product proof is one of the actual
uniform mixed slices. The dimension equality exactly matches its weight. -/
theorem productMixedSliceBound_of_uniform (i : ℕ) (L : ℝ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hMixed : UniformMixedBound i L f)
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (T : (A × U) →ₗ[F2] (B × C)) : ProductMixedSliceBound i f T L := by
  intro W D hW hD κ hκ
  have hm := UniformMixedBound.pullback (imageAmbientEquiv (A := A) W D hD)
    (LinearEquiv.refl F2 (B × C)) f hMixed
  have hm' : UniformMixedBound i L (imagePullback W D hD f) := by
    exact hm
  have hr : Module.finrank F2 A + Module.finrank F2 (W × C) ≤ i := by
    rw [Module.finrank_prod, hW]
    omega
  have hπ : Function.Surjective (LinearMap.snd F2 W C) := by
    intro c
    exact ⟨(0, c), rfl⟩
  have hh := hm' A (W × C) C κ hκ (primalA (imageTranslate W D hD T))
    (LinearMap.snd F2 W C) hπ (LinearMap.snd F2 B C) hr
  have hdim : Module.finrank F2 (A × (W × D)) = Module.finrank F2 (A × U) :=
    (imageAmbientEquiv (A := A) W D hD).finrank_eq
  have hexp : (Module.finrank F2 (W × C) + Module.finrank F2 C) *
      Module.finrank F2 (A × (W × D)) =
      (2 * Module.finrank F2 C + (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U) := by
    rw [Module.finrank_prod, hW, hdim]
    congr 1
    omega
  rw [hexp] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  convert hh using 1; try simp only [mul_comm]

end Product

variable {E F : Type u}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

omit [FiniteDimensional F2 E] [Fintype E] in
theorem map_leftRange_complement (A U : Submodule F2 E) (h : IsCompl A U) :
    (LinearMap.range (LinearMap.inl F2 A U)).map
      (Submodule.prodEquivOfIsCompl A U h).toLinearMap = A := by
  rw [← LinearMap.range_comp]
  have hc : (Submodule.prodEquivOfIsCompl A U h).toLinearMap.comp
      (LinearMap.inl F2 A U) = A.subtype := by
    apply LinearMap.ext
    intro a
    change (a : E) + (0 : E) = (a : E)
    simp
  rw [hc, Submodule.range_subtype]

/-- The actual hybrid derivative is uniformly bounded whenever all actual
mixed slices are bounded. Both selector subspaces and every affine translate
are arbitrary. -/
theorem hybridDerivative_energy_le_of_uniform
    (i : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hMixed : UniformMixedBound i L f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ L := by
  obtain ⟨U, hU⟩ := A.exists_isCompl
  obtain ⟨C, hC⟩ := B.exists_isCompl
  let a : (A × U) ≃ₗ[F2] E := Submodule.prodEquivOfIsCompl A U hU
  let b : (B × C) ≃ₗ[F2] F := Submodule.prodEquivOfIsCompl B C hC
  let f' : ((A × U) →ₗ[F2] (B × C)) → ℝ :=
    fun M => f (LinearEquiv.arrowCongr a b M)
  let T' : (A × U) →ₗ[F2] (B × C) := (LinearEquiv.arrowCongr a b).symm T
  have hf' : KMSBasisInvariant.IsBasisInvariant f' := basisInvariant_pullback a b f hf
  have hm' : UniformMixedBound i L f' := UniformMixedBound.pullback a b f hMixed
  have hi' : i ≤ Module.finrank F2 (A × U) := by rw [a.finrank_eq]; exact hi
  have hcoord : (𝔼 N, hybridDerivative
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T' (rankComponent i f') N ^ 2) ≤ L := by
    by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
    · exact product_hybrid_energy_le_of_mixed i f' hf' T' L hL hi'
        (productMixedSliceBound_of_uniform i L f' hm' ho T')
    · have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
        (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) T' f' i
        (by rw [product_restriction_order]
            change i < Module.finrank F2 A + Module.finrank F2 C
            omega)
      simpa [hzero] using hL
  have he := hybridDerivative_rankComponent_energy_pullback a b f i
    (LinearMap.range (LinearMap.inl F2 A U))
    (LinearMap.range (LinearMap.inl F2 B C)) T'
  have hA : (LinearMap.range (LinearMap.inl F2 A U)).map a.toLinearMap = A :=
    map_leftRange_complement A U hU
  have hB : (LinearMap.range (LinearMap.inl F2 B C)).map b.toLinearMap = B :=
    map_leftRange_complement B C hC
  have hT : LinearEquiv.arrowCongr a b T' = T :=
    (LinearEquiv.arrowCongr a b).apply_symm_apply T
  rw [hA, hB, hT] at he
  exact he ▸ hcoord

/-- Genuine KMS hybrid energy bound from basis invariance and actual local
squared density. This is the analytic input to the permitted generic fourth
moment inequality; no hybrid estimate is included among its hypotheses. -/
theorem hybridDerivative_energy_bound
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε :=
  hybridDerivative_energy_le_of_uniform i (mixedRankConstant i * ε)
    (mul_nonneg (mixedRankConstant_nonneg i) hε) f hf
    (uniformMixedBound_of_affineDensityBound i ε hε f hf hd) hi A B T

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
