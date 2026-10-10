import OAI.GroupTheory.PolycyclicRecognition.Algebra.InductionAmbientQuotient
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCompleteCohomologyVanishing

namespace OAI

/-! # Complete vanishing for induction along a subgroup exhaustion

The finite stages may have arbitrarily large projective dimensions. The
ambient group's FP-infinity hypothesis supplies continuity of its completed
cohomology for the actual induced-coefficient colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A B : Rep.{0} ℤ G}

def transportIso (c : D.ColimitCocone A) (e : A ≅ B) : D.ColimitCocone B where
  ι n := c.ι n ≫ e.hom
  comm i j h := by rw [← Category.assoc, c.comm]
  surj b := by
    obtain ⟨n, x, hx⟩ := c.surj (e.inv.hom b)
    refine ⟨n, x, ?_⟩
    change e.hom.hom ((c.ι n).hom x) = b
    rw [hx]
    exact ConcreteCategory.congr_hom e.inv_hom_id b
  zero_exact i x hx := by
    apply c.zero_exact i x
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    change e.hom.hom ((c.ι i).hom x) = e.hom.hom 0
    change e.hom.hom ((c.ι i).hom x) = 0 at hx
    simpa only [map_zero] using hx

end SequentialRepresentationDiagram.ColimitCocone

variable (A : Rep.{0} ℤ G) (H : ℕ → Subgroup G) (K : Subgroup G)
variable (hmono : Monotone H) (hHK : ∀ n, H n ≤ K)
variable (hcover : ∀ g ∈ K, ∃ n, g ∈ H n)

def inducedExhaustionDiagram : SequentialRepresentationDiagram G :=
  ascendingQuotientDiagram (inductionAmbient A)
    (fun n => subgroupCoinvariantRelations (inductionDiagonalAction A) (H n))
    (fun n => inductionRelations_invariant A (H n))
    (fun _ _ h => subgroupCoinvariantRelations_mono _ (hmono h))

def inducedExhaustionColimit :
    (inducedExhaustionDiagram A H hmono).ColimitCocone
      (Rep.ind K.subtype (Rep.res K.subtype A)) :=
  (ascendingQuotientColimit (inductionAmbient A)
    (fun n => subgroupCoinvariantRelations (inductionDiagonalAction A) (H n))
    (fun n => inductionRelations_invariant A (H n))
    (fun _ _ h => subgroupCoinvariantRelations_mono _ (hmono h))
    (subgroupCoinvariantRelations (inductionDiagonalAction A) K)
    (inductionRelations_invariant A K)
    (fun n => subgroupCoinvariantRelations_mono _ (hHK n))
    (fun _ hx => subgroupCoinvariantRelations_exhaustion _ H K hmono hcover hx)).transportIso
      (inductionAmbientQuotientIso A K)

include hmono hHK hcover in
theorem TypeFPInfinity.induction_exhaustion_complete_vanishing (hG : TypeFPInfinity G)
    (p : ℕ)
    (hH : ∀ n, Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind (H n).subtype (Rep.res (H n).subtype A)))) :
    Subsingleton (ShiftedCompletedCohomology p (Rep.ind K.subtype (Rep.res K.subtype A))) := by
  apply hG.shiftedCompleteCohomology_colimit_subsingleton p
    (inducedExhaustionDiagram A H hmono) _ (inducedExhaustionColimit A H K hmono hHK hcover)
  intro n
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (inductionAmbientQuotientIso A (H n))
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p
    ((inducedExhaustionDiagram A H hmono).obj n))
  intro x
  apply e.toLinearEquiv.injective
  exact (hH n).elim _ _

end PolycyclicRecognition

end

end OAI
