import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional

namespace OAI

noncomputable section

namespace PiExponentSeshadri.BlowupLift
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsLeftRegular r)

def coefficient (a : I) : S :=
  Classical.choose ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))

lemma mul_coefficient (a : I) : r * coefficient I f r hI a = f a.val := by
  exact (Classical.choose_spec ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))).symm

include hr in

lemma coefficients_span : Ideal.span (Set.range (coefficient I f r hI)) = ⊤ := by
  let K : Ideal S := Ideal.span (Set.range (coefficient I f r hI))
  have hmap : I.map f ≤ Submodule.map (LinearMap.mulLeft S r) K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Submodule.map (LinearMap.mulLeft S r) K
    exact ⟨coefficient I f r hI ⟨a, ha⟩,
      Ideal.subset_span (Set.mem_range_self _), mul_coefficient I f r hI ⟨a, ha⟩⟩
  have hmem : r ∈ Submodule.map (LinearMap.mulLeft S r) K := by
    apply hmap
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨s, hs, hrs⟩ := hmem
  have hs1 : s = 1 := hr (by simpa using hrs)
  refine Ideal.eq_top_of_isUnit_mem (I := K) ?_ isUnit_one
  exact hs1 ▸ hs

end PiExponentSeshadri.BlowupLift

namespace PiExponentSeshadri.ReesGrading

section
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
  let g : CommRingCat.of (piece I 0) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom ((principalMap I f r hI hr).comp (algebraMap _ _))
  have hg : (zeroIso I).hom ≫ g = CommRingCat.ofHom f := by
    ext s
    exact principalMap_base I f r hI hr s
  have h : principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I) =
      X.toSpecΓ ≫ Spec.map g :=
    Proj.fromOfGlobalSections_toSpecZero (piece I) (principalMap I f r hI hr)
      (principalMap_irrelevant I f r hI hr)
  change principalScheme I X f r hI hr ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  calc
    _ = (principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I)) ≫
        Spec.map (zeroIso I).hom := (Category.assoc _ _ _).symm
    _ = (X.toSpecΓ ≫ Spec.map g) ≫ Spec.map (zeroIso I).hom :=
      congrArg (fun q : X ⟶ Spec (CommRingCat.of (piece I 0)) =>
        q ≫ Spec.map (zeroIso I).hom) h
    _ = X.toSpecΓ ≫ Spec.map ((zeroIso I).hom ≫ g) := by
      rw [Category.assoc, Spec.map_comp]
    _ = _ := congrArg (fun q : CommRingCat.of R ⟶ Γ(X, ⊤) =>
      X.toSpecΓ ≫ Spec.map q) hg

lemma principalScheme_preimage (a : I) :
    principalScheme I X f r hI hr ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) =
      X.basicOpen (BlowupLift.coefficient I f r hI a) := by
  erw [principalScheme, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _
    (show 0 < (1 : ℕ) from Nat.zero_lt_one) (generator_mem I a), principalMap_generator]

end PiExponentSeshadri.ReesGrading

end

end OAI
