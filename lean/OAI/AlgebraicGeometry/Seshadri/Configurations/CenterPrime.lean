import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.CenteredJetChart

namespace OAI

section
noncomputable section
                                     
section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

lemma affineSectionRatios_basicOpen (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none)) (j : Option σ) :
    X.basicOpen (affineSectionRatios s U hU j) = U.1 ⊓ SectionOpens.isoOpen (s j) := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv]
  have hh : U.1.topIso.inv (affineSectionRatios s U hU j) =
      coefficient (sectionFrameOn (s none) U.1 hU) (restrictSection U.1.ι (s j)) := by
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id _
  rw [hh, ← preimage_isoOpen]
  ext x
  change (∃ q : U.1.toScheme, q.1 ∈ SectionOpens.isoOpen (s j) ∧ q.1 = x) ↔ _
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.property, hq⟩
  · rintro ⟨hx, hj⟩
    exact ⟨⟨x,hx⟩, hj, rfl⟩

theorem centered_evaluation_kernel (g : X ⟶ Spec (CommRingCat.of K))
    (s : Option σ → (O X ⟶ M)) (p : X)
    (hp : ∀ x : X, x ∉ centeredOpen s ↔ x = p)
    (U : X.affineOpens) (hpU : p ∈ U.1)
    (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (ρ : let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra;
      Γ(X, U.1) →ₐ[K] K)
    (hρ : ∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) :
    RingHom.ker ρ = (U.2.isoSpec.hom ⟨p,hpU⟩).asIdeal := by
  let q : PrimeSpectrum Γ(X, U.1) := ⟨RingHom.ker ρ, RingHom.ker_isPrime ρ⟩
  have hq : U.2.fromSpec q ∉ centeredOpen s := by
    intro h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp h
    have hmem : U.2.fromSpec q ∈ X.basicOpen (affineSectionRatios s U hU (some j)) := by
      rw [affineSectionRatios_basicOpen]
      exact ⟨by rw [← U.2.isoSpec_inv_ι]; exact (U.2.isoSpec.inv q).property, hj⟩
    have hn : q ∈ PrimeSpectrum.basicOpen (affineSectionRatios s U hU (some j)) := by
      rwa [← U.2.fromSpec_preimage_basicOpen]
    exact hn (hρ j)
  have hqp : U.2.fromSpec q = p := (hp _).mp hq
  have heq : q = U.2.isoSpec.hom ⟨p,hpU⟩ := by
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    apply (U.2.fromSpec.isOpenEmbedding.injective)
    rw [hqp]
    change p = (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p,hpU⟩
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  exact congrArg PrimeSpectrum.asIdeal heq

end
end MaximalSeshadri.Projective
end


end
end

end OAI
