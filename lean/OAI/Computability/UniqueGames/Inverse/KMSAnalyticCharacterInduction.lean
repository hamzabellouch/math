import Mathlib.FieldTheory.Finiteness
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionComplementLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticBlockFrequenciesLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedBaseLemmas

namespace OAI

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

universe u v w x

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {E : Type u} [AddCommGroup E] [Module F2 E]
  [FiniteDimensional F2 E] [Fintype E]
private theorem fixedFrequencyEnergy_bound_induction :
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
      let : Fintype (s.B →ₗ[F2] s.J) := mapFintype
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
  fixedFrequencyEnergy_bound_induction (Module.finrank F2 J) F I J rfl ι hι f hf ε hg π hπ A

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end OAI
