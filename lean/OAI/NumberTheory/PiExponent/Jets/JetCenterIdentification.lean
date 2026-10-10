import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PiExponent.JetCenterIdentification
open CurveValuationCenter PlaceValuationRing CompactLogJetIdeal CompactJetPolynomial

variable {E : Type} [Field E] [Algebra ℂ E]

theorem centered_of_closedPoint_eq {m : ℕ} (p : NormalizedPlace ℂ E)
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) = j (centerPoint c)) :
    CurveCenters.Centered z (Fin.cases 1 c) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (centerPoint c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : coordinateRing m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) = centerPoint c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) =
      centerPoint c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : coordinateRing m := MvPolynomial.X i - MvPolynomial.C (center c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (center c)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun f : CommRingCat.of (coordinateRing m) ⟶ CommRingCat.of E => f P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P, center] using hpos

end PiExponent.JetCenterIdentification

end

end OAI
