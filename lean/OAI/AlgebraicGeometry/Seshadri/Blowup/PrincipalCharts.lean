import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.ExceptionalIdeal

namespace OAI

section
namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalToLocalization : reesAlgebra I →+* Localization.Away r :=
  (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)).comp (reesAlgebra I).val.toRingHom

lemma principalToLocalization_base (s : R) :
    principalToLocalization I f r (algebraMap R (reesAlgebra I) s) =
      algebraMap S (Localization.Away r) (f s) := by
  simp [principalToLocalization]

lemma principalToLocalization_generator (a : I) :
    principalToLocalization I f r (generator I a) =
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by
  change (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)) (monomial 1 a.val) = _
  simp only [coe_eval₂RingHom, eval₂_monomial, RingHom.comp_apply, pow_one]
  rw [← BlowupLift.mul_coefficient I f r hI a, map_mul]
  calc _ = (algebraMap S (Localization.Away r) r * IsLocalization.Away.invSelf r) *
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by ring
       _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

include hI in
lemma principalToLocalization_range (p : reesAlgebra I) :
    ∃ s : S, algebraMap S (Localization.Away r) s = principalToLocalization I f r p := by
  have hp : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨BlowupLift.coefficient I f r hI a, (principalToLocalization_generator I f r hI a).symm⟩
  | algebraMap s => exact ⟨f s, (principalToLocalization_base I f r s).symm⟩
  | add p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s+t, by rw [map_add, hs, ht, map_add]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s*t, by rw [map_mul, hs, ht, map_mul]⟩

include hr in
lemma principalLocalization_injective : Function.Injective (algebraMap S (Localization.Away r)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))

def principalMap : reesAlgebra I →+* S where
  toFun p := Classical.choose (principalToLocalization_range I f r hI p)
  map_zero' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 0), map_zero, map_zero])
  map_one' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 1), map_one, map_one])
  map_add' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p+q)), map_add,
      map_add, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])
  map_mul' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p*q)), map_mul,
      map_mul, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])

lemma principalMap_spec (p : reesAlgebra I) :
    algebraMap S (Localization.Away r) (principalMap I f r hI hr p) =
      principalToLocalization I f r p :=
  Classical.choose_spec (principalToLocalization_range I f r hI p)

lemma principalMap_base (s : R) :
    principalMap I f r hI hr (algebraMap R (reesAlgebra I) s) = f s := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_base]

lemma principalMap_generator (a : I) :
    principalMap I f r hI hr (generator I a) = BlowupLift.coefficient I f r hI a := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_generator]

lemma principalMap_irrelevant :
    (HomogeneousIdeal.irrelevant (piece I)).toIdeal.map (principalMap I f r hI hr) = ⊤ := by
  rw [eq_top_iff, ← BlowupLift.coefficients_span I f r hI hr.left]
  apply Ideal.span_le.mpr
  rintro s ⟨a, rfl⟩
  rw [← principalMap_generator I f r hI hr]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem (piece I) (by decide : 0 < (1 : ℕ))
    (generator_mem I a)

end

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (X : Scheme.{u}) (f : R →+* Γ(X, ⊤)) (r : Γ(X, ⊤))
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalScheme : X ⟶ affineBlowup I :=
  Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
    (principalMap_irrelevant I f r hI hr)

@[reassoc]
lemma principalScheme_projection :
    principalScheme I X f r hI hr ≫ projection I =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  change Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
      (principalMap_irrelevant I f r hI hr) ≫
      (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext s
  exact principalMap_base I f r hI hr s

lemma principalScheme_preimage (a : I) :
    principalScheme I X f r hI hr ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) =
      X.basicOpen (BlowupLift.coefficient I f r hI a) := by
  exact (Proj.fromOfGlobalSections_preimage_basicOpen (piece I)
    (principalMap I f r hI hr) (principalMap_irrelevant I f r hI hr)
    Nat.zero_lt_one (generator_mem I a)).trans
    (congrArg X.basicOpen (principalMap_generator I f r hI hr a))

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.ProjBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma basicOpenToSpec_eq (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma basicOpenToSpec_mem (f : A) (x : Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      z.num.val ∈ x.val.asHomogeneousIdeal := by
  have he := congr($(basicOpenToSpec_eq 𝒜 f).base x)
  change (Proj.basicOpenToSpec 𝒜 f) x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x at he
  rw [he]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

lemma toSpecZero_mem (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∈ x.asHomogeneousIdeal := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply]
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) _).asIdeal ↔ _
  refine (basicOpenToSpec_mem 𝒜 (1 : A) _ ⟨0, a, 1, one_mem _⟩).trans ?_
  change a.val ∈ ((Proj.basicOpen 𝒜 (1 : A)).ι
    (((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ((Proj 𝒜).topIso.inv x))).asHomogeneousIdeal ↔ _
  rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι, ← Scheme.Hom.comp_apply]
  rw [Scheme.toIso_inv_ι]; rfl

lemma toSpecZero_preimage (a : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen a = Proj.basicOpen 𝒜 a.val := by
  ext x
  change a ∉ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∉ x.asHomogeneousIdeal
  exact not_congr (toSpecZero_mem 𝒜 x a)

end
end MaximalSeshadri.ProjBase

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance projection_separated : IsSeparated (projection I) := by
  have hP : IsSeparated (Proj.toSpecZero (piece I)) := inferInstance
  have hQ : IsSeparated (Spec.map (zeroIso I).hom) := inferInstance
  exact MorphismProperty.comp_mem (@IsSeparated) _ _ hP hQ

lemma projection_mem (x : affineBlowup I) (s : R) :
    s ∈ ((projection I) x).asIdeal ↔
      algebraMap R (reesAlgebra I) s ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I s ∈ ((Proj.toSpecZero (piece I)) x).asIdeal ↔ _
  exact ProjBase.toSpecZero_mem (piece I) x (zeroEquiv I s)

lemma projection_preimage (s : R) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      Proj.basicOpen (piece I) (algebraMap R (reesAlgebra I) s) := by
  ext x
  exact not_congr (projection_mem I x s)

lemma base_generator_comm (a b : I) :
    algebraMap R (reesAlgebra I) a.val * generator I b =
      algebraMap R (reesAlgebra I) b.val * generator I a := by
  apply Subtype.ext
  change C a.val * monomial 1 b.val = C b.val * monomial 1 a.val
  simp only [C_mul_monomial, mul_comm a.val b.val]

lemma projection_preimage_le_chart (a : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a.val ≤
      Proj.basicOpen (piece I) (generator I a) := by
  rw [projection_preimage]
  intro x hx
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))
  have h : x ∈ Proj.basicOpen (piece I)
      (algebraMap R (reesAlgebra I) a.val * generator I b) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hx, hb⟩
  rw [base_generator_comm, Proj.basicOpen_mul] at h
  exact h.2

lemma chartHom_ext {S : Type*} [CommRing S] (a : I)
    (g h : chart I a →+* S) (he : g.comp (chartBase I a) = h.comp (chartBase I a))
    (hr : IsRegular (g (chartBase I a a.val))) : g = h := by
  have hb (s : R) : g (chartBase I a s) = h (chartBase I a s) := RingHom.congr_fun he s
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hr.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg h (base_pow_mul_mk I a n p hp)
  simpa only [map_mul, map_pow, hb] using h₁.trans ((hb ((evaluation I) p)).trans h₂.symm)

end
end MaximalSeshadri.ReesGrading


end

end OAI
