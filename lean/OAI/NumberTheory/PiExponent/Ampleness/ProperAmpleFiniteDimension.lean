import OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

namespace OAI

noncomputable section
namespace PiExponent.ProperAmpleFiniteDimension
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective

section Graded
variable {A S : Type*} [CommRing A] [SetLike S A] [AddSubmonoidClass S A]
    (G : ℕ → S) [GradedRing G]

def projectivePrime : ProjectiveSpectrum G → PrimeSpectrum A :=
  fun x => ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

theorem projectivePrime_isInducing : Topology.IsInducing (projectivePrime G) := by
  constructor
  apply TopologicalSpace.ext_isClosed
  intro Z
  rw [ProjectiveSpectrum.isClosed_iff_zeroLocus, isClosed_induced_iff]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩
  · rintro ⟨T,hT,hTZ⟩
    obtain ⟨s,rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus T).mp hT
    exact ⟨s,hTZ.symm⟩

theorem projectiveSpectrum_dimension_le :
    topologicalKrullDim (ProjectiveSpectrum G) ≤ ringKrullDim A := by
  simpa only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
    (projectivePrime_isInducing G).topologicalKrullDim_le
end Graded

theorem projectiveSpace_dimension_le_card (K σ : Type) [Field K] [Finite σ] :
    topologicalKrullDim (ProjectiveO1.projectiveSpace K σ) ≤ Nat.card σ := by
  let := MvPolynomial.gradedAlgebra (R := K) (σ := σ)
  change topologicalKrullDim (ProjectiveSpectrum (PolyGrade K σ)) ≤ _
  have h := projectiveSpectrum_dimension_le (PolyGrade K σ)
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add] using h

theorem closedImmersion_dimension_le {X Y : Scheme} (i : X ⟶ Y)
    [IsClosedImmersion i] : topologicalKrullDim X ≤ topologicalKrullDim Y :=
  i.isEmbedding.isInducing.topologicalKrullDim_le

theorem exists_dimension_bound_of_proper_ample {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨n, hn, σ, hσ, s, hs, hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let i : X ⟶ ProjectiveO1.projectiveSpace ℂ σ := sectionsMorphism k s hs
  have : IsClosedImmersion i := hclosed
  exact ⟨Nat.card σ, (closedImmersion_dimension_le i).trans
    (projectiveSpace_dimension_le_card ℂ σ)⟩

end PiExponent.ProperAmpleFiniteDimension

end

end OAI
