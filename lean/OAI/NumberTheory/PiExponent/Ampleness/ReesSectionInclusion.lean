import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue
import OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase

namespace OAI

namespace PiExponent.ReesSectionInclusion
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

private abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

private local instance chartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

private theorem transported_augmentation (n : ℕ)
    (f : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (t : Fin 1 → J) :
    ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a 0 t)
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) f t) =
    freeOpenMap (affineBlowup I).ringCatSheaf (homOfLE le_top) ≫ f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (eqToHom (tupleOpen_eq I a 0 t)) ≫
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (homOfLE _) ≫ f = _
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

def HasFrozenValues (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) (r : R) : Prop :=
  ∀ t : Fin 1 → J,
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top) u t))).val =
      ReesFrozenChart.base I a (tupleSet t) r

theorem section_chart_inclusion (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) (t : Fin 1 → J) :
    ExceptionalAffineChart.functionsOnOpenEquiv
      (chartMap I a (tuple_nonempty 0 t))
      ((affineBlowup I).presheaf.map (homOfLE le_top).op
        ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
          (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) =
      ReesFrozenChart.base I a (tupleSet t) r := by
  have h := hvalue t
  change (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
    (chartHomEquiv I a (tuple_nonempty 0 t) (tuple_mem 0 t 0) n
      (ExceptionalRepresentedTypes.transportSections
        (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
        (tupleOpen_eq I a 0 t)
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (u) t)))).val = _ at h
  rw [chartHomEquiv_pieceEquiv] at h
  erw [ExceptionalRepresentedTypes.representedSectionsTyped_apply,
    ExceptionalAffineChart.representedSectionsEquiv_apply] at h
  erw [transported_augmentation I a n u t] at h
  erw [freeOpenEquiv_naturality] at h
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).mapPresheaf.naturality
      (homOfLE (show (chartMap I a (tuple_nonempty 0 t)).opensRange ≤ ⊤ from le_top)).op)
    (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)
  change (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) =
    (affineBlowup I).presheaf.map (homOfLE le_top).op
      ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) at hn
  change ExceptionalAffineChart.functionsOnOpenEquiv _
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) = _ at h
  rw [hn] at h
  exact h

theorem section_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  apply (O (affineBlowup I)).isSheaf.section_ext
  intro x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((iSup_opens I a ha).ge (Set.mem_univ x))
  let t : Fin 1 → J := fun _ => j
  have heq : (chartMap I a (tuple_nonempty 0 t)).opensRange = opens I a j := by
    change (ReesFrozenChart.chartOpen I a (tuple_nonempty 0 t)).1 = _
    rw [tupleOpen_eq]
    simp only [CechHigher.intersection, t, iInf_const]
  refine ⟨(chartMap I a (tuple_nonempty 0 t)).opensRange, le_top,
    heq.ge hj, ?_⟩
  apply (ExceptionalAffineChart.functionsOnOpenEquiv
    (chartMap I a (tuple_nonempty 0 t))).injective
  exact (section_chart_inclusion I a n u r hvalue t).trans
    (ExceptionalAffineChart.functionsOnOpenEquiv_pullback (projection I)
      (chartMap I a (tuple_nonempty 0 t))
      (ReesFrozenChart.base I a (tupleSet t))
      (ReesFrozenChart.chart_projection I a (tuple_nonempty 0 t)) r).symm

end
end PiExponent.ReesSectionInclusion

end OAI
