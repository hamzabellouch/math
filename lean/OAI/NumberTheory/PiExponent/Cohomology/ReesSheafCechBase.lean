import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport
import OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover
import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames
import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower
import OAI.NumberTheory.PiExponent.Cohomology.CechHigher

namespace OAI

namespace PiExponent.ReesSheafCechBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)

private abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

private local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

abbrev exceptionalPower (n : ℕ) := ((exceptionalLineBundle I).pow n).sheaf

def opens (j : J) : (affineBlowup I).Opens := ((chartCover I).f (a j)).opensRange

omit [Fintype J] in
theorem tuple_mem (q : ℕ) (t : Fin (q + 1) → J) (k : Fin (q + 1)) : t k ∈ tupleSet t :=
  Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

omit [Fintype J] in
theorem tuple_nonempty (q : ℕ) (t : Fin (q + 1) → J) : (tupleSet t).Nonempty :=
  ⟨t 0, tuple_mem q t 0⟩

def freeOpenSectionsEquiv {X : Scheme} (U : X.Opens) (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with map_add' := fun _ _ => rfl }

def freeOpenHomCongr {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : U = V) :
    (schemeFreeOpen X V ⟶ M) ≃+ (schemeFreeOpen X U ⟶ M) where
  toFun b := freeOpenMap X.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap X.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  right_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  map_add' b c := Preadditive.comp_add (C := X.Modules) _ _ _ _ b c

theorem freeOpenHomCongr_restrict {X : Scheme} (M : X.Modules)
    {U U' V V' : X.Opens} (hU : U' = U) (hV : V' = V) (h : V ≤ U)
    (b : schemeFreeOpen X U ⟶ M) :
    freeOpenHomCongr M hV (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (hV.le.trans (h.trans hU.ge))) ≫
        freeOpenHomCongr M hU b := by
  subst hU; subst hV
  simp [freeOpenHomCongr, freeOpenMap]
  erw [Category.id_comp]

theorem tupleOpen_eq (q : ℕ) (t : Fin (q + 1) → J) :
    (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).1 =
      CechHigher.intersection (opens I a) t := by
  change (chartMap I a (tuple_nonempty q t)).opensRange = _
  rw [ReesFrozenChart.chart_opensRange, ReesProductPowerSections.chartMorphism_opensRange]
  apply le_antisymm
  · apply le_iInf
    intro k
    exact Finset.inf_le (tuple_mem q t k)
  · apply Finset.le_inf
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact iInf_le (fun i => opens I a (t i)) k

def genericChartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s)
    (L : PiExponentSeshadri.Geometry.LineBundle (affineBlowup I))
    (ι : L.sheaf ⟶ PiExponentSeshadri.Frames.O (affineBlowup I))
    (hL : PiExponentSeshadri.Geometry.PresentsPullbackIdeal
      (PiExponentSeshadri.IdealPullback.specIdeal I) (projection I) L ι)
    (e : ExceptionalRepresentedTypes.Frame (chartMap I a hs) L)
    (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs) L n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  (ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
    (chartMap I a hs)
    (ReesFrozenChart.base I a s)
    (ReesFrozenChart.chart_projection I a hs) L ι hL e n).trans
      (ReesFrozenPower.pieceEquiv I a hp n).symm

attribute [local irreducible] genericChartHomEquiv

theorem chartFrameTyped_nonempty {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) :
    Nonempty (ExceptionalRepresentedTypes.Frame (chartMap I a hs)
      (exceptionalLineBundle I)) := by
  exact ExceptionalRepresentedTypes.frame_nonempty_of_open
    (chartMap I a hs) (exceptionalLineBundle I)
    (U := (ReesFrozenChart.chartOpen I a hs).1) rfl
    (ReesFrozenChart.chartFrame_nonempty I a hs hp)

def chartFrameTyped {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) :
    ExceptionalRepresentedTypes.Frame (chartMap I a hs) (exceptionalLineBundle I) :=
  (chartFrameTyped_nonempty I a hs hp).some

def chartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  genericChartHomEquiv I a hs hp (exceptionalLineBundle I) (exceptionalInclusion I)
    (exceptional_presents I) (chartFrameTyped I a hs hp) n

theorem chartHomEquiv_pieceEquiv {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n) :
    ReesFrozenPower.pieceEquiv I a hp n (chartHomEquiv I a hs hp n b) =
      ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
        (chartMap I a hs)
        (ReesFrozenChart.base I a s)
        (ReesFrozenChart.chart_projection I a hs)
        (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)
        (chartFrameTyped I a hs hp) n b := by
  unfold chartHomEquiv genericChartHomEquiv
  exact (ReesFrozenPower.pieceEquiv I a hp n).apply_symm_apply _

def tupleHomEquiv (n q : ℕ) (t : Fin (q + 1) → J) :
    (schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n) ≃+ ReesLocalizedIntersections.Piece I a (tupleSet t) n :=
  (ExceptionalRepresentedTypes.transportSections
    (chartMap I a (tuple_nonempty q t)) (exceptionalLineBundle I) n
    (tupleOpen_eq I a q t)).trans
      (chartHomEquiv I a (tuple_nonempty q t) (tuple_mem q t 0) n)

private local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def cochainEquiv (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  letI (t : Fin (q + 1) → J) : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact AddEquiv.piCongrRight (fun t => tupleHomEquiv I a n q t)

theorem tuple_isAffine (q : ℕ) (t : Fin (q + 1) → J) :
    IsAffineOpen (CechHigher.intersection (opens I a) t) := by
  rw [← tupleOpen_eq I a q t]
  exact (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).property

omit [Fintype J] [DecidableEq J] in

theorem iSup_opens (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    (⨆ j, opens I a j) = ⊤ := ReesFiniteCover.iSup_generator_opensRange I a ha

end
end PiExponent.ReesSheafCechBase

end OAI
