import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CokernelResolution

namespace OAI

/-! # Finite projective resolutions through infinite cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

def projectiveResolutionAlongIso {A B : Rep ℤ G} (P : ProjectiveResolution A)
    (e : A ≅ B) : ProjectiveResolution B where
  complex := P.complex
  π := P.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map e.hom

theorem finiteProjectiveResolution_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (hN : HasFiniteProjectiveResolution N) : HasFiniteProjectiveResolution G := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨P, d, hP, hd⟩ := hN
  let IP := normalInducedResolution ℤ N P
  let R := projectiveResolutionAlongIso IP (inductionTrivialIso ℤ N)
  have hR (i : ℕ) : IntegralRepresentationFinite G (R.complex.X i) :=
    integralRepresentationFinite_induction N (P.complex.X i) (hP i)
  have hRd (i : ℕ) (hi : d < i) : IsZero (R.complex.X i) :=
    normalInducedResolution_bounded N P d hd i hi
  let S := cyclicQuotientSequence (G ⧸ N) (QuotientGroup.mk' N) z
  have hS : S.ShortExact :=
    cyclicQuotientSequence_shortExact (G ⧸ N) (QuotientGroup.mk' N) z hz
  refine ⟨cokernelProjectiveResolution S R R hS, d + 1, ?_, ?_⟩
  · exact repCofiber_finite R R (cokernelResolutionMap S R R) hR hR
  · exact repCofiber_bounded R R (cokernelResolutionMap S R R) d hRd hRd

theorem typeFPInfinity_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (hN : HasFiniteProjectiveResolution N) : TypeFPInfinity G :=
  (finiteProjectiveResolution_of_infiniteCyclicQuotient N hN).typeFPInfinity G

end PolycyclicRecognition

end

end OAI
