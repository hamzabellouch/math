import Mathlib
import OAI.Computability.MaxCut.Games.KMSFourthMomentPointShuffle

namespace OAI

/-!
Point restrictions inherit basis invariance in the remaining coordinates.
Translations split into a shift of the fixed point and a translation of the
remaining matrix; both identities are exact, with no probability loss.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem pointAppend_comp_basis (X : E →ₗ[F2] F) (a : F) (g : E ≃ₗ[F2] E) :
    pointAppend (X.comp g.toLinearMap) a =
      (pointAppend X a).comp (g.prodCongr (LinearEquiv.refl F2 F2)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rfl

/-- Fixing a column preserves invariance under changes of the other columns. -/
theorem pointRestrict_invariant (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : F) :
    KMSBasisInvariant.IsBasisInvariant (pointRestrict f a) := by
  intro g X
  change f (pointAppend (X.comp g.toLinearMap) a) = f (pointAppend X a)
  rw [pointAppend_comp_basis]
  exact hf (g.prodCongr (LinearEquiv.refl F2 F2)) (pointAppend X a)

theorem pointAppend_add (X : E →ₗ[F2] F) (a : F)
    (Z : (E × F2) →ₗ[F2] F) :
    pointAppend X a + Z =
      pointAppend (X + Z.comp (LinearMap.inl F2 E F2)) (a + Z (0, 1)) := by
  have hZ (x : E) (c : F2) : Z (x, c) = Z (x, 0) + c • Z (0, 1) := by
    calc
      Z (x, c) = Z ((x, 0) + c • (0, 1)) := by simp
      _ = Z (x, 0) + c • Z (0, 1) := by rw [map_add, map_smul]
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, c⟩
  simp only [LinearMap.add_apply, pointAppend_apply, LinearMap.comp_apply,
    LinearMap.inl_apply, smul_add]
  rw [hZ]
  abel

/-- A translation of the full matrix merely translates the remaining
coordinates and shifts the fixed primal value. -/
theorem pointRestrict_translate (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (Z : (E × F2) →ₗ[F2] F) (a : F) :
    pointRestrict (fun Y => f (Y + Z)) a =
      fun X => pointRestrict f (a + Z (0, 1))
        (X + Z.comp (LinearMap.inl F2 E F2)) := by
  funext X
  change f (pointAppend X a + Z) = _
  rw [pointAppend_add]
  rfl

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- All affine restrictions with at most r prescribed input/output dimensions
have normalized squared density at most ε. The dimension sum avoids any
truncated-subtraction ambiguity. -/
def AffineDensityBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]
    (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (D →ₗ[F2] C)],
    ∀ L : E →ₗ[F2] D, Function.Surjective L →
    ∀ J : C →ₗ[F2] F, Function.Injective J →
    ∀ T : E →ₗ[F2] F,
      Module.finrank F2 E + Module.finrank F2 F ≤
        Module.finrank F2 D + Module.finrank F2 C + r →
      (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) ≤ ε

/-- A stronger restriction budget supplies every smaller budget. -/
theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

/-- The homogeneous output restriction required for Lemma 3.19 is an actual
special case, using the identity domain quotient and zero affine center. -/
theorem AffineDensityBound.homogeneous [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) : HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ J hJ hdim
  have h := hf E C (LinearMap.id : E →ₗ[F2] E) Function.surjective_id
    J hJ 0 (by omega)
  simpa using h

/-- Fixing one additional primal column consumes exactly one dimension of
local-density budget. Its prescribed value is arbitrary, including zero. -/
theorem AffineDensityBound.pointRestrict [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound (r + 1) ε f) (a : F) :
    AffineDensityBound r ε (pointRestrict f a) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  let L' : (E × F2) →ₗ[F2] D := L.comp (LinearMap.fst F2 E F2)
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    exact ⟨(x, 0), hx⟩
  have hdim' : Module.finrank F2 (E × F2) + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + 1) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have he (X : D →ₗ[F2] C) :
      pointAppend (T + J.comp (X.comp L)) a =
        pointAppend T a + J.comp (X.comp L') := by
    apply LinearMap.ext
    intro p
    rcases p with ⟨x, c⟩
    simp only [pointAppend_apply, LinearMap.add_apply, LinearMap.comp_apply,
      L', LinearMap.fst_apply]
    abel
  have h := hf D C L' hL' J hJ (pointAppend T a) hdim'
  simpa only [KMSAnalytic.pointRestrict, he] using h

end

/-!
The local-density predicate is invariant under an ambient basis presentation
and consumes exactly the output codimension under a homogeneous restriction.
These are changes of the actual sampled affine maps, without an estimate loss.
-/

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)

universe u v
variable {E E' : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup B] [Module F2 B]

/-- Exact ambient coordinate transport of all sampled affine restrictions. -/
theorem AffineDensityBound.domain_equiv
    [FiniteDimensional F2 E] [FiniteDimensional F2 E']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) (e : E ≃ₗ[F2] E') :
    AffineDensityBound r ε (fun X : E' →ₗ[F2] F => f (X.comp e.toLinearMap)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hdim
  have h := hf D C (L.comp e.toLinearMap) (hL.comp e.surjective) J hJ
    (T.comp e.toLinearMap) hdim'
  simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using h

/-- Homogeneous codomain restriction uses its actual codimension budget. -/
theorem AffineDensityBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound (r + s) ε f)
    (K : B →ₗ[F2] F) (hK : Function.Injective K)
    (hdimK : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    AffineDensityBound r ε (fun X : E →ₗ[F2] B => f (K.comp X)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + s) := by omega
  have h := hf D C L hL (K.comp J) (hK.comp hJ) (K.comp T) hdim'
  simpa only [LinearMap.comp_add, LinearMap.comp_assoc] using h

end

/-!
The complete fixed-point induction from the fixed-character base estimate.
The base is kept as a named mathematical input here so its separate character
induction can be assembled independently. This intermediate theorem is not
the final KMS endpoint: its base must be discharged by the proved homogeneous
character estimate. All point-recursion, basis transport and local-density
steps are established within this theorem's proof.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {F : Type v} {I J : Type u}
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Fintype F] [Fintype I] [Fintype J]

omit [FiniteDimensional F2 J] [Fintype J] in
/-- The actual mixed norm for arbitrary prescribed fixed points. The rank cap
and scalar constants are chosen before either ambient dimension. -/
theorem mixed_bound_of_character_bound (R : ℕ) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J)
    (hπ : Function.Surjective π)
    (hbase : ∀ (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E],
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 I) ε f →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π ν ≤ H * ε) :
    ∀ (n : ℕ) (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E]
      (A : Type u) [AddCommGroup A] [Module F2 A]
      [FiniteDimensional F2 A] [Fintype A],
      Module.finrank F2 A = n →
      ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f →
      ∀ (a : A →ₗ[F2] F), Module.finrank F2 A + Module.finrank F2 I ≤ R →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
          H * mixedStepFactor R ^ n * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ A _ _ _ _ hAn ι hι f hf hd a hr
    by_cases hn : n = 0
    · have hz : Module.finrank F2 A = 0 := hAn.trans hn
      let : Subsingleton A := Module.finrank_zero_iff.mp hz
      have hi : Function.Injective (ι.comp (LinearMap.inr F2 A I)) := by
        intro x y hxy
        exact congrArg Prod.snd (hι hxy)
      have hd0 : AffineDensityBound (Module.finrank F2 I) ε f := by simpa [hz] using hd
      rw [mixedEnergy_zeroFixed]
      simpa only [hn, pow_zero, mul_one] using
        hbase E (ι.comp (LinearMap.inr F2 A I)) hi f hf hd0
    · have hp : 0 < Module.finrank F2 A := by omega
      obtain ⟨A0, eA, hAdrop⟩ := KMSPointComplement.exists_point_equiv hp
      change Module.finrank F2 A0 + 1 = Module.finrank F2 A at hAdrop
      obtain ⟨E0, eE, κ, hκ, halign⟩ := exists_mixed_aligned_point ι hι eA
      let f' : ((E0 × F2) →ₗ[F2] F) → ℝ :=
        fun X => f (X.comp eE.symm.toLinearMap)
      let a0 : A0 →ₗ[F2] F := (a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)
      let b : F := a (eA (0, 1))
      let r0 := Module.finrank F2 A0 + Module.finrank F2 I
      let t := Module.finrank F2 I + Module.finrank F2 J
      have hs : Module.finrank F2 A0 < n := by omega
      have hr0 : r0 ≤ R := by dsimp [r0]; omega
      have hf' : KMSBasisInvariant.IsBasisInvariant f' :=
        ambient_basisInvariant_transport eE.symm f hf
      have hd' : AffineDensityBound (r0 + 1) ε f' := by
        have h := AffineDensityBound.domain_equiv _ ε f hd eE.symm
        have he : Module.finrank F2 A + Module.finrank F2 I = r0 + 1 := by
          dsimp [r0]; omega
        simpa only [he] using h
      have hdp : AffineDensityBound r0 ε (pointRestrict f' b) :=
        AffineDensityBound.pointRestrict r0 ε f' hd' b
      have hdo : AffineDensityBound r0 ε f' :=
        AffineDensityBound.mono (Nat.le_succ r0) ε f' hd'
      have hdimE : Module.finrank F2 E = Module.finrank F2 E0 + 1 := by
        simpa only [Module.finrank_prod, Module.finrank_self] using eE.finrank_eq.symm
      have ht : t ≤ 2 * R := by
        have hji : Module.finrank F2 J ≤ Module.finrank F2 I :=
          LinearMap.finrank_le_finrank_of_surjective hπ
        dsimp [t]
        omega
      have hcard : (Fintype.card ((A0 × I) →ₗ[F2] F2) : ℝ) = (2 : ℝ) ^ r0 := by
        rw [Module.card_eq_pow_finrank (K := F2)]
        simp [Module.finrank_prod, r0, F2, ZMod.card]
      let C := H * mixedStepFactor R ^ Module.finrank F2 A0 * ε
      let W0 : ℝ := 2 ^ (t * Module.finrank F2 E0)
      let W1 : ℝ := 2 ^ (t * (Module.finrank F2 E0 + 1))
      have hW0 : 0 < W0 := by dsimp [W0]; positivity
      have hW1 : 0 < W1 := by dsimp [W1]; positivity
      have hfirst : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent κ (pointRestrict f' b)) a0) ≤ C / W0 := by
        apply (le_div_iff₀ hW0).mpr
        have h := ih (Module.finrank F2 A0) hs E0 A0 rfl κ hκ
          (pointRestrict f' b) (pointRestrict_invariant f' hf' b) hdp a0 hr0
        simpa only [C, W0, t, mul_comm] using h
      have hsecond (a' : A0 →ₗ[F2] F) : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent (pointPad κ) f') a') ≤ C / W1 := by
        apply (le_div_iff₀ hW1).mpr
        have h := ih (Module.finrank F2 A0) hs (E0 × F2) A0 rfl
          (pointPad κ) (pointPad_injective κ hκ) f' hf' hdo a' hr0
        simpa only [C, W1, t, Module.finrank_prod, Module.finrank_self, mul_comm] using h
      have hrec := mixed_point_sliceEnergy_le_of_bounds κ hκ f' hf' a0 b
        (fun T => π.comp T = ν) (C / W0) (C / W1) hfirst hsecond
      rw [hcard] at hrec
      have hweighted := mixed_weighted_step_pow R (Module.finrank F2 A0)
        (Module.finrank F2 E0) t r0 H ε _ (C / W0) (C / W1)
        hH hε ht hr0 hrec
        (by change W0 * (C / W0) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW0)])
        (by change W1 * (C / W1) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW1)])
      rw [partialRestrict_smallComponent_mixed_aligned ι eA eE κ halign f a]
      simpa only [hdimE, ← hAn, ← hAdrop, f', a0, b, t] using hweighted

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Exact orbit grouping for KMS Fourier norms

The frequency fibers are finite sets with their real cardinality as the
multiplicity. No probability normalization or orbit-size estimate is assumed
by the grouping identity. The later kernel-orbit count supplies these sizes
for the actual binary linear maps.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical

section FiniteFibers

variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]

/-- Exact sum of a function constant on the fibers of a finite map. -/
theorem sum_comp_eq_fiber_card (p : A → J) (b : J → ℝ) :
    (∑ x, b (p x)) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j := by
  calc
    (∑ x, b (p x)) = ∑ x, ∑ j, if p x = j then b j else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ∑ j, ∑ x, if p x = j then b j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

theorem sum_sq_eq_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) :
    (∑ x, a x ^ 2) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j ^ 2 := by
  simpa only [hab] using sum_comp_eq_fiber_card p (fun j => b j ^ 2)

/-- If every orbit has the same size, its multiplicity factors out exactly. -/
theorem sum_sq_eq_uniform_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) (n : ℕ)
    (hn : ∀ j, (Finset.univ.filter fun x => p x = j).card = n) :
    (∑ x, a x ^ 2) = (n : ℝ) * ∑ j, b j ^ 2 := by
  rw [sum_sq_eq_fiber_card p a b hab, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hn]

/-- Two coefficient arrays with the same orbit values have exactly the ratio
of their orbit multiplicities. Cross multiplication includes zero-energy
functions without dividing by their norm. -/
theorem fiber_constant_energy_cross_mul (p : A → J) (q : B → J)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (a : A → ℝ) (b : B → ℝ)
    (hab : ∀ x y, p x = q y → a x = b y)
    (nA nB : ℕ)
    (hA : ∀ j, (Finset.univ.filter fun x => p x = j).card = nA)
    (hB : ∀ j, (Finset.univ.filter fun y => q y = j).card = nB) :
    (nB : ℝ) * (∑ x, a x ^ 2) = (nA : ℝ) * ∑ y, b y ^ 2 := by
  let c : J → ℝ := fun j => b (Classical.choose (hq j))
  have ha : ∀ x, a x = c (p x) := by
    intro x
    exact hab x (Classical.choose (hq (p x)))
      (Classical.choose_spec (hq (p x))).symm
  have hb : ∀ y, b y = c (q y) := by
    intro y
    obtain ⟨x, hx⟩ := hp (q y)
    exact (hab x y hx).symm.trans (by simpa only [hx] using ha x)
  rw [sum_sq_eq_uniform_fiber_card p a c ha nA hA,
    sum_sq_eq_uniform_fiber_card q b c hb nB hB]
  ring

end FiniteFibers

open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype J]

/-- Parseval grouped by any genuine finite classification of frequencies. -/
theorem synthesis_energy_grouped (p : (F →ₗ[F2] E) → J)
    (a : (F →ₗ[F2] E) → ℝ) (b : J → ℝ) (hab : ∀ S, a S = b (p S)) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ j, ((Finset.univ.filter fun S => p S = j).card : ℝ) * b j ^ 2 := by
  rw [synthesis_energy]
  exact sum_sq_eq_fiber_card p a b hab

/-- In particular, basis-invariant coefficients may be grouped by their
actual kernels. The invariance premise is supplied separately by the proved
change-of-basis theorem, not by any inverse or hypercontractive hypothesis. -/
theorem synthesis_energy_by_kernel [Fintype (Submodule F2 F)]
    (a : (F →ₗ[F2] E) → ℝ) (b : Submodule F2 F → ℝ)
    (hab : ∀ S, a S = b S.ker) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ K : Submodule F2 F,
        ((Finset.univ.filter fun S : F →ₗ[F2] E => S.ker = K).card : ℝ) * b K ^ 2 :=
  synthesis_energy_grouped (fun S => S.ker) a b hab

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

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
end MaxCutGames.Inverse.KMSKernelFiberCard

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Composing an injective map with the quotient projection has exactly the
prescribed kernel. -/
theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

/-- Every map with kernel `K` factors uniquely through an injective quotient
map; the inverse sends that quotient map to its composition with `K.mkQ`. -/
def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

/-- Quotient factorization leaves the image subspace unchanged. -/
theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

/-- The quotient lift has the same rank as the original map. -/
theorem finrank_range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R (fixedKernelEquivQuotientInjection K S).val.range =
      Module.finrank R S.val.range := by
  rw [range_forward]

/-- A prescribed kernel fixes the rank to the dimension of its quotient. -/
theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

/-- Surjectivity of the quotient projection preserves the range of any map
defined on the quotient. -/
theorem range_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E) :
    (J.comp K.mkQ).range = J.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨K.mkQ x, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    exact ⟨x, rfl⟩

/-- The inverse factorization of an injection has quotient dimension as its
rank. In the finite-dimensional binary case this is the ordinary finite rank. -/
theorem quotientInjection_comp_finrank (K : Submodule R F)
    (J : (F ⧸ K) →ₗ[R] E) (hJ : Function.Injective J) :
    Module.finrank R (J.comp K.mkQ).range = Module.finrank R (F ⧸ K) := by
  rw [range_comp_mkQ]
  exact LinearMap.finrank_range_of_inj hJ

/-- Exact fixed-kernel count, stated without requiring a chosen enumeration. -/
theorem natCard_fixedKernel_eq_injectiveQuotient (K : Submodule R F) :
    Nat.card {S : F →ₗ[R] E // S.ker = K} =
      Nat.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Nat.card_congr (fixedKernelEquivQuotientInjection K)

/-- The same counting equality for any finite enumerations of the two sides. -/
theorem card_fixedKernel_eq_injectiveQuotient (K : Submodule R F)
    [Fintype {S : F →ₗ[R] E // S.ker = K}]
    [Fintype {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}] :
    Fintype.card {S : F →ₗ[R] E // S.ker = K} =
      Fintype.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Fintype.card_congr (fixedKernelEquivQuotientInjection K)

end
end MaxCutGames.Inverse.KMSAnalyticKernelCount

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

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
end MaxCutGames.Inverse.KMSKernelFiberCard

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

namespace MaxCutGames.Inverse.KMSInjectionCount

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
end MaxCutGames.Inverse.KMSInjectionCount

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

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
end MaxCutGames.Inverse.KMSKernelFiberCard

end OAI
