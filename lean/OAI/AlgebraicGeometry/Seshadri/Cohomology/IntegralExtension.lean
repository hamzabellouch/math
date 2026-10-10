import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.IntegralSubschemes
import OAI.AlgebraicGeometry.Seshadri.Blowup.HartogsScheme

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits

theorem integral_of_affine_extension {X : Scheme} (U : X.Opens)
    [IsIntegral U.toScheme] (B : CommRingCat) (f : Spec B ⟶ X) [IsOpenImmersion f]
    (hcover : U ⊔ f.opensRange = ⊤)
    (hB : Nontrivial B → IsDomain B)
    (hne : Nontrivial B → Nonempty (f ⁻¹ᵁ U)) : IsIntegral X := by
  classical
  by_cases hb : Nontrivial B
  · let := hb
    let : IsDomain B := hB hb
    let : IsIntegral (Spec B) := (affine_isIntegral_iff B).mpr inferInstance
    let C : X.OpenCover := .mkOfCovers Bool
      (fun b => if b then Spec B else U.toScheme)
      (fun b => by cases b; exact U.ι; exact f)
      (by
        intro x
        have hx : x ∈ U ⊔ f.opensRange := hcover.ge (Set.mem_univ x)
        rcases hx with hx | hx
        · exact ⟨false, ⟨x, hx⟩, rfl⟩
        · obtain ⟨y, hy⟩ := hx
          exact ⟨true, y, hy⟩)
      (by intro b; cases b <;> dsimp <;> infer_instance)
    let : ∀ i, IsIntegral (C.X i) := fun i => by
      cases i with
      | false => change IsIntegral U.toScheme; infer_instance
      | true => change IsIntegral (Spec B); infer_instance
    apply BertiniIntegral.integral_of_integral_open_cover C false
    intro i
    cases i with
    | false =>
      obtain ⟨x⟩ := (inferInstance : Nonempty U.toScheme)
      exact ⟨U.ι x, ⟨x, rfl⟩, ⟨x, rfl⟩⟩
    | true =>
      obtain ⟨x⟩ := hne hb
      exact ⟨f x.1, ⟨⟨f x.1, x.2⟩, rfl⟩, ⟨x.1, rfl⟩⟩
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hb
    let : IsEmpty (Spec B) := by
      change IsEmpty (PrimeSpectrum B)
      infer_instance
    have hU : U = ⊤ := by
      rw [← hcover]
      symm
      apply sup_eq_left.mpr
      rintro x ⟨y, rfl⟩
      exact isEmptyElim y
    let e : U.toScheme ≅ X :=
      eqToIso (congrArg Scheme.Opens.toScheme hU) ≪≫ Scheme.topIso X
    exact IsIntegral.of_isIso e.hom

theorem integral_of_principal_extension {X : Scheme} (V : X.Opens)
    [IsIntegral V.toScheme] {A : Type} [CommRing A] [IsDomain A]
    (I : Ideal A) (r : A) (hI : I = Ideal.span {r})
    (x y : A) (hx : x ≠ 0) (hxy : ∀ a : A, x ∣ y * a → x ∣ a)
    (f : Spec (CommRingCat.of (A ⧸ I)) ⟶ X) [IsOpenImmersion f]
    (hcover : V ⊔ f.opensRange = ⊤)
    (hVx : PrimeSpectrum.basicOpen (Ideal.Quotient.mk I x) ≤ f ⁻¹ᵁ V)
    (hVy : PrimeSpectrum.basicOpen (Ideal.Quotient.mk I y) ≤ f ⁻¹ᵁ V) : IsIntegral X := by
  have hi : Function.Injective ((algebraMap (A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I x))).prod
        (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I y)))) := by
    subst I
    exact principal_quotient_localizations_jointly_injective x y r hx hxy
  let W := f ⁻¹ᵁ V
  let : IsReduced W.toScheme := isReduced_of_isOpenImmersion (f ∣_ V)
  let : PreirreducibleSpace W := (f ∣_ V).isOpenEmbedding.preirreducibleSpace
  apply integral_of_affine_extension V (CommRingCat.of (A ⧸ I)) f hcover
  · intro hB
    let := hB
    exact domain_of_detecting_preintegral_open _ _ hi W hVx hVy
  · intro hB
    let := hB
    exact nonempty_of_joint_localizations _ _ hi W hVx hVy

def restrictedIdealOpenIso {X : Scheme} (J : X.IdealSheafData) (V : X.Opens) :
    (J.comap V.ι).subscheme ≅ (J.subschemeι ⁻¹ᵁ V).toScheme := by
  let f := (J.comapIso V.ι).hom ≫ pullback.snd V.ι J.subschemeι
  have hf : f.opensRange = J.subschemeι ⁻¹ᵁ V := by
    dsimp [f]
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    rw [Scheme.Hom.opensRange_pullbackSnd]
    simp
  have hset : Set.range f = (J.subschemeι ⁻¹ᵁ V : Set J.subscheme) := congrArg SetLike.coe hf
  exact IsOpenImmersion.isoOfRangeEq f (J.subschemeι ⁻¹ᵁ V).ι
    (by simpa only [Scheme.Opens.range_ι] using hset)

end
end MaximalSeshadri.Hartogs
end


end
end

end OAI
