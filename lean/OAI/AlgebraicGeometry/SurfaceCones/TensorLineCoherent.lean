import OAI.AlgebraicGeometry.SurfaceCones.CoherentClosedFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor
universe u
instance tensorLeft_additive {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : SheafOfModules.{u} (ringSheaf R)) : (tensorLeft R L).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft R L)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- A line bundle tensored with a coherent sheaf is coherent. The proof descends the tensor sheaf
from its local unit trivializations. -/
lemma coherent_tensor_line {X : Scheme.{0}} (L M : X.Modules)
    (d : LineTrivialization X.sheaf L) [M.IsFinitePresentation] :
    ((tensorLeft X.sheaf L).obj M).IsFinitePresentation := by
  have hloc : ∀ i, (((tensorLeft X.sheaf L).obj M).over (d.obj i)).IsFinitePresentation := by
    intro i
    have : ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι (X := X) (d.obj i))).obj M).IsFinitePresentation :=
      CoherentGlobal.coherent_restrict (Scheme.Opens.ι (X := X) (d.obj i)) M
    have : (M.over (d.obj i)).IsFinitePresentation :=
      CoherentGlobal.coherent_over_of_restrict (d.obj i) M
    let e : ((tensorLeft X.sheaf L).obj M).over (d.obj i) ≅ M.over (d.obj i) :=
      (tensorLeftCompOverIso X.sheaf (d.obj i) L).app M ≪≫
        (tensorLeftIso (X.sheaf.over (d.obj i)) (d.iso i)).app (M.over (d.obj i)) ≪≫
          (tensorUnitLeftIso (X.sheaf.over (d.obj i))).app (M.over (d.obj i))
    exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (d.obj i))).prop_of_iso
      e.symm inferInstance

  let _ := hloc
  exact CoherentLocality.finitePresentation_of_coversTop _ d.obj d.cover

/-- The Cartier line twist on the abelian category of coherent sheaves. -/
def coherentTensorLine {X : Scheme.{0}} (L : X.Modules)
    (d : LineTrivialization X.sheaf L) : CoherentGlobal.Coh X ⥤ CoherentGlobal.Coh X :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).lift
    (CoherentGlobal.cohInclusion X ⋙ tensorLeft X.sheaf L) (fun M => by
      let := M.property
      exact coherent_tensor_line L M.obj d)

instance coherentTensorLine_additive {X : Scheme.{0}} (L : X.Modules)
    (d : LineTrivialization X.sheaf L) : (coherentTensorLine L d).Additive where
  map_add := by
    have : (tensorLeft X.sheaf L).Additive := tensorLeft_additive X.sheaf L
    intros
    apply ObjectProperty.hom_ext
    exact (tensorLeft X.sheaf L).map_add

lemma coherentTensorLine_exact {X : Scheme.{0}} [IsLocallyNoetherian X]
    (L : X.Modules) (d : LineTrivialization X.sheaf L)
    (S : ShortComplex (CoherentGlobal.Coh X)) (he : S.Exact) :
    (S.map (coherentTensorLine L d)).Exact := by
  let tensorAdditive : (tensorLeft X.sheaf L).Additive := tensorLeft_additive X.sheaf L
  let tensorZero : (tensorLeft X.sheaf L).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let tensorHomology := tensorLeft_preservesHomology_of_line X.sheaf L d
  have hbase := he.map (CoherentGlobal.cohInclusion X)
  have hleft := @Functor.PreservesHomology.preservesLeftHomologyOf _ _ _ _ _ _
    (tensorLeft X.sheaf L) tensorZero (S.map (CoherentGlobal.cohInclusion X)) tensorHomology
  have hright := @Functor.PreservesHomology.preservesRightHomologyOf _ _ _ _ _ _
    (tensorLeft X.sheaf L) tensorZero (S.map (CoherentGlobal.cohInclusion X)) tensorHomology
  have ht := @ShortComplex.Exact.map _ _ _ _ _ _ _ hbase
    (tensorLeft X.sheaf L) tensorZero hleft hright
  exact ((S.map (coherentTensorLine L d)).exact_map_iff_of_faithful
    (CoherentGlobal.cohInclusion X)).mp ht

instance coherentTensorLine_preservesHomology {X : Scheme.{0}} [IsLocallyNoetherian X]
    (L : X.Modules) (d : LineTrivialization X.sheaf L) :
    (coherentTensorLine L d).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (coherentTensorLine_exact L d)

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CoherentLocality
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]

/-- The finite free sheaf has the presentation with no relations. -/
def freePresentation (I : Type u) : (SheafOfModules.free (R := R) I).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (R := R) PEmpty ⟶ SheafOfModules.free I)
    (𝟙 _) (by simp)
    (CokernelCofork.IsColimit.ofπ (𝟙 _) (by simp)
      (fun f _ => f) (fun _ _ => by simp) (fun _ _ _ h => by simpa using h))

instance freePresentation_finite (I : Type u) [Finite I] :
    (freePresentation R I).IsFinite := by
  constructor
  · constructor
    change Finite I
    infer_instance
  · constructor
    change Finite PEmpty
    infer_instance

lemma finitePresentation_free (I : Type u) [Finite I] :
    (SheafOfModules.free (R := R) I).IsFinitePresentation :=
  finitePresentation_of_presentation (freePresentation R I)

lemma finitePresentation_unit : (SheafOfModules.unit R).IsFinitePresentation := by
  exact (SheafOfModules.isFinitePresentation R).prop_of_iso
    (coproductUniqueIso (fun (_ : PUnit.{u+1}) => SheafOfModules.unit R))
      (finitePresentation_free R PUnit.{u+1})
end CoherentLocality

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor

/-- Finite presentation of a line sheaf, descended from its unit trivializations rather than
included in the line data. -/
lemma coherent_line {X : Scheme.{0}} (L : X.Modules)
    (d : LineTrivialization X.sheaf L) : L.IsFinitePresentation := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    CoherentLocality.finitePresentation_unit X.ringCatSheaf
  have hp : ((tensorLeft X.sheaf L).obj (SheafOfModules.unit _)).IsFinitePresentation :=
    coherent_tensor_line L _ d
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (rightUnitIso X.sheaf L) hp

/-- The resolution morphism for an Cartier line ideal, inside the category of coherent sheaves. The
source is the tensor twist. -/
def coherentIdealAction {X : Scheme.{0}} (L : X.Modules)
    (d : LineTrivialization X.sheaf L) (i : L ⟶ SheafOfModules.unit _) :
    coherentTensorLine L d ⟶ 𝟭 (CoherentGlobal.Coh X) where
  app M := ObjectProperty.homMk ((idealAction X.sheaf i).app M.obj)
  naturality {M N} f := by
    apply ObjectProperty.hom_ext
    exact (idealAction X.sheaf i).naturality f.hom

/-- The coherent first Tor object computed by the Cartier line resolution, viewed on the ambient
scheme. -/
def coherentCartierKernel {X : Scheme.{0}} [IsLocallyNoetherian X] (L : X.Modules)
    (d : LineTrivialization X.sheaf L) (i : L ⟶ SheafOfModules.unit _) :
    CoherentGlobal.Coh X ⥤ CoherentGlobal.Coh X :=
  kernel (coherentIdealAction L d i)

def coherentCartierCokernel {X : Scheme.{0}} [IsLocallyNoetherian X] (L : X.Modules)
    (d : LineTrivialization X.sheaf L) (i : L ⟶ SheafOfModules.unit _) :
    CoherentGlobal.Coh X ⥤ CoherentGlobal.Coh X :=
  cokernel (coherentIdealAction L d i)

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))
local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf (R.over U)).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    ((R.over U).obj ⋙ forget₂ CommRingCat RingCat)))

lemma tensorOverIso_inv_adjoint (L M : SheafOfModules.{u} (ringSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf (R.over U)).obj)).homEquiv _ _
      (tensorOverIso R U L M).inv =
    (presheafTensorOverIso R U L.val M.val).inv ≫
      (presheafOver R U).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) L.val M.val)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf (R.over U)).obj)
  change adj.homEquiv _ _ ((PresheafOfModules.sheafification (𝟙 (ringSheaf (R.over U)).obj)).map (presheafTensorOverIso R U L.val M.val).inv ≫
    sheafifyOverMap R U _) = _
  erw [adj.homEquiv_naturality_left]
  dsimp only [adj, sheafifyOverMap]
  erw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply, Equiv.apply_symm_apply]
  rfl

/-- Restriction compatibility for the ideal multiplication. This identifies the global Cartier
resolution with the local principal one. -/
lemma idealAction_over_inv {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R)) :
    (tensorOverIso R U L M).inv ≫
        (SheafOfModules.overFunctor _ U).map ((idealAction R i).app M) =
      (idealAction (R.over U) ((SheafOfModules.overFunctor _ U).map i)).app (M.over U) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf (R.over U)).obj)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_right, tensorOverIso_inv_adjoint]
  have hlocal := idealAction_adjoint (R.over U)
    ((SheafOfModules.overFunctor _ U).map i) (M.over U)
  refine Eq.trans ?_ hlocal.symm
  erw [Category.assoc]
  change (presheafTensorOverIso R U L.val M.val).inv ≫
      (presheafOver R U).map _ ≫ (presheafOver R U).map _ = _
  erw [← Functor.map_comp]
  have hg := idealAction_adjoint R i M
  erw [Adjunction.homEquiv_unit] at hg
  change (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) L.val M.val) ≫
        ((idealAction R i).app M).val = _ at hg
  erw [hg]
  ext V l
  rfl

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierCentrality
universe v u v' u'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Every natural endomorphism of a functor naturally isomorphic to the identity commutes with that
functor. -/
lemma of_iso (T : C ⥤ C) (e : T ≅ 𝟭 C) (ε : T ⟶ 𝟭 C) (X : C) :
    ε.app (T.obj X) = T.map (ε.app X) := by
  have he : T.map (e.hom.app X) = e.hom.app (T.obj X) := by
    apply (cancel_mono (e.hom.app X)).mp
    exact e.hom.naturality (e.hom.app X)
  apply (cancel_mono (e.hom.app X)).mp
  calc
    ε.app (T.obj X) ≫ e.hom.app X = T.map (e.hom.app X) ≫ ε.app X :=
      (ε.naturality (e.hom.app X)).symm
    _ = e.hom.app (T.obj X) ≫ ε.app X := by rw [he]
    _ = T.map (ε.app X) ≫ e.hom.app X := (e.hom.naturality (ε.app X)).symm

/-- Centrality descends through the natural tensor-restriction isomorphism. -/
lemma map_eq (T : C ⥤ C) (U : D ⥤ D) (F : C ⥤ D)
    (ρ : T ⋙ F ≅ F ⋙ U) (ε : T ⟶ 𝟭 C) (δ : U ⟶ 𝟭 D)
    (h : ∀ X, ρ.hom.app X ≫ δ.app (F.obj X) = F.map (ε.app X))
    (hδ : ∀ Y, δ.app (U.obj Y) = U.map (δ.app Y)) (X : C) :
    F.map (ε.app (T.obj X)) = F.map (T.map (ε.app X)) := by
  apply (cancel_mono (ρ.hom.app X)).mp
  calc
    F.map (ε.app (T.obj X)) ≫ ρ.hom.app X =
        ρ.hom.app (T.obj X) ≫ δ.app (F.obj (T.obj X)) ≫ ρ.hom.app X := by
      rw [← h (T.obj X), Category.assoc]
    _ = ρ.hom.app (T.obj X) ≫ U.map (ρ.hom.app X) ≫ δ.app (U.obj (F.obj X)) := by
      exact congrArg (fun f => ρ.hom.app (T.obj X) ≫ f)
        (δ.naturality (ρ.hom.app X)).symm
    _ = ρ.hom.app (T.obj X) ≫ U.map (ρ.hom.app X) ≫ U.map (δ.app (F.obj X)) := by
      rw [hδ]
    _ = ρ.hom.app (T.obj X) ≫ U.map (F.map (ε.app X)) := by
      rw [← U.map_comp, h]
    _ = F.map (T.map (ε.app X)) ≫ ρ.hom.app X :=
      (ρ.hom.naturality (ε.app X)).symm
end CartierCentrality

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Multiplication by a line ideal commutes with its tensor twist, as checked on a trivializing
cover. -/
lemma idealAction_central {L : SheafOfModules.{u} (ringSheaf R)}
    (d : LineTrivialization R L) (i : L ⟶ SheafOfModules.unit _)
    (M : SheafOfModules.{u} (ringSheaf R)) :
    (idealAction R i).app ((tensorLeft R L).obj M) =
      (tensorLeft R L).map ((idealAction R i).app M) := by
  apply (SheafOfModules.toSheaf (ringSheaf R)).map_injective
  apply SheafLocality.hom_ext_of_coversTop d.cover
  intro a
  let V := d.obj a
  let F := SheafOfModules.overFunctor (ringSheaf R) V
  let T := tensorLeft R L
  let U := tensorLeft (R.over V) (L.over V)
  let δ := idealAction (R.over V) (F.map i)
  have hδ (N : SheafOfModules.{u} (ringSheaf (R.over V))) :
      δ.app (U.obj N) = U.map (δ.app N) :=
    CartierCentrality.of_iso U
      (tensorLeftIso (R.over V) (d.iso a) ≪≫ tensorUnitLeftIso (R.over V)) δ N
  have h (N : SheafOfModules.{u} (ringSheaf R)) :
      (tensorLeftCompOverIso R V L).hom.app N ≫ δ.app (F.obj N) =
        F.map ((idealAction R i).app N) := by
    have hN := idealAction_over_inv R V i N
    change (tensorLeftCompOverIso R V L).inv.app N ≫
      F.map ((idealAction R i).app N) = δ.app (F.obj N) at hN
    rw [← hN]
    exact Iso.hom_inv_id_app_assoc (tensorLeftCompOverIso R V L) N _
  exact congrArg ((SheafOfModules.toSheaf (ringSheaf (R.over V))).map)
    (CartierCentrality.map_eq T U F (tensorLeftCompOverIso R V L)
      (idealAction R i) δ h hδ M)
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierAnnihilator
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
  (T : C ⥤ C) [T.PreservesZeroMorphisms]
  (ε : T ⟶ 𝟭 C)
  (hc : ∀ X, ε.app (T.obj X) = T.map (ε.app X))

include hc in
/-- The kernel of a central Cartier action is annihilated by that same action. Naturality alone
would not suffice without centrality. -/
lemma kernel_annihilated (M : C) : ε.app (kernel (ε.app M)) = 0 := by
  apply (cancel_mono (kernel.ι (ε.app M))).mp
  rw [zero_comp]
  rw [← show T.map (kernel.ι (ε.app M)) ≫ ε.app (T.obj M) =
    ε.app (kernel (ε.app M)) ≫ kernel.ι (ε.app M) from ε.naturality _]
  change T.map (kernel.ι (ε.app M)) ≫ ε.app (T.obj M) = 0
  rw [hc, ← T.map_comp, kernel.condition, T.map_zero]

omit [T.PreservesZeroMorphisms] in
/-- Right exactness and centrality make the cokernel a module on the Cartier zero locus. -/
lemma cokernel_annihilated [T.PreservesEpimorphisms] (M : C) :
    ε.app (cokernel (ε.app M)) = 0 := by
  apply (cancel_epi (T.map (cokernel.π (ε.app M)))).mp
  rw [comp_zero, ε.naturality]
  exact cokernel.condition (ε.app M)
end CartierAnnihilator

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor

/-- Centrality for the coherent Cartier resolution. -/
lemma coherentIdealAction_central {X : Scheme.{0}} (L : X.Modules)
    (d : LineTrivialization X.sheaf L) (i : L ⟶ SheafOfModules.unit _)
    (M : CoherentGlobal.Coh X) :
    (coherentIdealAction L d i).app ((coherentTensorLine L d).obj M) =
      (coherentTensorLine L d).map ((coherentIdealAction L d i).app M) := by
  apply ObjectProperty.hom_ext
  exact idealAction_central X.sheaf d i M.obj

/-- The first Cartier Tor object is annihilated by the ideal as a coherent sheaf on the ambient
scheme. -/
lemma coherentCartierKernel_annihilated {X : Scheme.{0}} [IsLocallyNoetherian X]
    (L : X.Modules) (d : LineTrivialization X.sheaf L)
    (i : L ⟶ SheafOfModules.unit _) (M : CoherentGlobal.Coh X) :
    (coherentIdealAction L d i).app
      (kernel ((coherentIdealAction L d i).app M)) = 0 :=
  CartierAnnihilator.kernel_annihilated (coherentTensorLine L d)
    (coherentIdealAction L d i) (coherentIdealAction_central L d i) M

/-- The coherent restriction object is killed by the ideal. -/
lemma coherentCartierCokernel_annihilated {X : Scheme.{0}} [IsLocallyNoetherian X]
    (L : X.Modules) (d : LineTrivialization X.sheaf L)
    (i : L ⟶ SheafOfModules.unit _) (M : CoherentGlobal.Coh X) :
    (coherentIdealAction L d i).app
      (cokernel ((coherentIdealAction L d i).app M)) = 0 := by
  let : PreservesFiniteColimits (coherentTensorLine L d) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : (coherentTensorLine L d).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  exact CartierAnnihilator.cokernel_annihilated (coherentTensorLine L d)
    (coherentIdealAction L d i) M
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSheafTensor

private local instance unitSectionSMul {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) :
    SMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op U)) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule.toSMul

private local instance schemeSectionSMul {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) :
    SMul Γ(X, U) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule.toSMul

/-- Vanishing of the ideal action implies annihilation of every section. -/
lemma idealAction_annihilates_sections {X : Scheme.{0}} {L : X.Modules}
    (i : L ⟶ SheafOfModules.unit _) (M : X.Modules)
    (h : (idealAction X.sheaf i).app M = 0)
    (U : X.Opens) (l : L.val.obj (op U)) (m : M.val.obj (op U)) :
    (i.val.app (op U) l) • m = 0 := by
  have he := idealAction_pure X.sheaf i M (op U) l m
  rw [h] at he
  exact he.symm

lemma affine_idealAction_torsion {R : CommRingCat.{0}} {L : (Spec R).Modules}
    (i : L ⟶ SheafOfModules.unit _) (M : (Spec R).Modules)
    (h : (idealAction (Spec R).sheaf i).app M = 0)
    (t : R) (l : L.val.obj (op ⊤))
    (hl : i.val.app (op ⊤) l = (Scheme.ΓSpecIso R).inv.hom t) :
    Module.IsTorsionBy R (moduleSpecΓFunctor.obj M) t := by
  change ∀ m : M.val.obj (op ⊤), (Scheme.ΓSpecIso R).inv.hom t • m = 0
  intro m
  rw [← hl]
  exact idealAction_annihilates_sections i M h ⊤ l m

/-- The coherent Cartier kernel descends to the affine principal divisor. The section hypothesis
just identifies the local Cartier equation with a section of the given ideal line. -/
lemma coherentCartierKernel_principal_descent {R : CommRingCat.{0}}
    [IsNoetherianRing R] (L : (Spec R).Modules)
    (d : LineTrivialization (Spec R).sheaf L) (i : L ⟶ SheafOfModules.unit _)
    (M : CoherentGlobal.Coh (Spec R)) (t : R) (l : L.val.obj (op ⊤))
    (hl : i.val.app (op ⊤) l = (Scheme.ΓSpecIso R).inv.hom t) :
    ∃ N : (Spec (CommRingCat.of (R ⧸ Ideal.span ({t} : Set R)))).Modules,
      N.IsFinitePresentation ∧ Nonempty
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))))).obj N ≅
          (kernel ((coherentIdealAction L d i).app M)).obj) := by
  let K := kernel ((coherentIdealAction L d i).app M)
  have : K.obj.IsFinitePresentation := K.property
  apply CoherentGlobal.exists_principal_descent t K.obj
  apply affine_idealAction_torsion i K.obj _ t l hl
  exact congrArg (fun e => e.hom) (coherentCartierKernel_annihilated L d i M)

/-- The coherent cokernel (ordinary restriction) descends as well. -/
lemma coherentCartierCokernel_principal_descent {R : CommRingCat.{0}}
    [IsNoetherianRing R] (L : (Spec R).Modules)
    (d : LineTrivialization (Spec R).sheaf L) (i : L ⟶ SheafOfModules.unit _)
    (M : CoherentGlobal.Coh (Spec R)) (t : R) (l : L.val.obj (op ⊤))
    (hl : i.val.app (op ⊤) l = (Scheme.ΓSpecIso R).inv.hom t) :
    ∃ N : (Spec (CommRingCat.of (R ⧸ Ideal.span ({t} : Set R)))).Modules,
      N.IsFinitePresentation ∧ Nonempty
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))))).obj N ≅
          (cokernel ((coherentIdealAction L d i).app M)).obj) := by
  let K := cokernel ((coherentIdealAction L d i).app M)
  have : K.obj.IsFinitePresentation := K.property
  apply CoherentGlobal.exists_principal_descent t K.obj
  apply affine_idealAction_torsion i K.obj _ t l hl
  exact congrArg (fun e => e.hom) (coherentCartierCokernel_annihilated L d i M)
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TopologicalSpace
namespace CoherentGlobal
open Scheme.Modules

lemma affine_chart_torsion {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules)
    (h : ∀ (r : Γ(Y, ⊤)), f.appTop r = 0 → ∀ m : Γ(M, ⊤), r • m = 0) :
    Module.IsTorsionBySet Γ(Y, ⊤)
      (moduleSpecΓFunctor.obj ((pushforward Y.isoSpec.hom).obj M))
      (RingHom.ker f.appTop.hom) := by
  intro m ⟨r, hr⟩
  change (M.smul (Y.isoSpec.hom.app ⊤ ((Spec Γ(Y, ⊤)).presheaf.map (𝟙 (op ⊤))
    ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r))) : Γ(M, ⊤) ⟶ Γ(M, ⊤)).hom m = 0
  have hm := h r hr
  have he : Y.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r) = r := by
    simp [Scheme.isoSpec_hom]
  have hid := congrArg (fun g : Γ(Spec Γ(Y, ⊤), ⊤) ⟶ Γ(Spec Γ(Y, ⊤), ⊤) =>
      Y.isoSpec.hom.appTop (g ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r)))
    ((Spec Γ(Y, ⊤)).presheaf.map_id (op ⊤))
  change Y.isoSpec.hom.appTop ((Spec Γ(Y, ⊤)).presheaf.map (𝟙 (op ⊤))
    ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r)) =
    Y.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom r) at hid
  erw [hid, he]
  exact hm m

lemma annihilated_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (h : ∀ (U : Y.Opens) (r : Γ(Y, U)), f.app U r = 0 →
      ∀ m : Γ(M, U), r • m = 0) (U : Y.Opens) :
    ∀ (r : Γ(U.toScheme, ⊤)), (f ∣_ U).appTop r = 0 →
      ∀ m : Γ((restrictFunctor U.ι).obj M, ⊤), r • m = 0 := by
  intro r hr m
  have hf : f.app (U.ι ''ᵁ ⊤) r = 0 := by
    rw [morphismRestrict_appTop] at hr
    apply (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).1
    change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (f.app (U.ι ''ᵁ ⊤) r) = 0 at hr
    exact hr.trans (map_zero _).symm
  have hm := h (U.ι ''ᵁ ⊤) r hf m
  change (M.smul ((U.ι.appIso ⊤).inv r) :
    Γ(M, U.ι ''ᵁ ⊤) ⟶ Γ(M, U.ι ''ᵁ ⊤)).hom m = 0
  have hi : (U.ι.appIso ⊤).inv r = r := by
    erw [Scheme.Opens.ι_appIso]
    rfl
  erw [hi]
  exact hm

lemma exists_closed_preimage_of_annihilated {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsFinitePresentation]
    (h : ∀ (U : Y.Opens) (r : Γ(Y, U)), f.app U r = 0 →
      ∀ m : Γ(M, U), r • m = 0) :
    ∃ N : Coh X, Nonempty ((pushforward f).obj N.obj ≅ M) := by
  have hlocal (U : Y.affineOpens) :
      ∃ N : (f ⁻¹ᵁ U.1).toScheme.Modules, N.IsFinitePresentation ∧
        Nonempty ((pushforward (f ∣_ U.1)).obj N ≅ (restrictFunctor U.1.ι).obj M) := by
    have : ((restrictFunctor U.1.ι).obj M).IsFinitePresentation := coherent_restrict _ M
    apply exists_affine_closed_preimage (f ∣_ U.1)
    exact affine_chart_torsion _ _ (annihilated_restrict f M h U.1)
  choose N hN e using hlocal
  exact exists_coherent_closed_preimage f (fun U : Y.affineOpens => U.1)
    (iSup_affineOpens_eq_top Y) M N (fun U => (e U).some) hN

end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y)
/-- The map from the ambient structure sheaf to the pushed-forward structure sheaf; its section maps
are precisely the scheme comorphism. -/
def structureMap : SheafOfModules.unit Y.ringCatSheaf ⟶
    (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
/-- The ideal sheaf of a closed immersion, defined as a sheaf kernel. -/
def idealSheaf : Y.Modules := kernel (structureMap f)
def idealι : idealSheaf f ⟶ SheafOfModules.unit Y.ringCatSheaf := kernel.ι _

lemma ideal_section_lift (U : Y.Opens) (r : Γ(Y, U)) (hr : f.app U r = 0) :
    ∃ l : (idealSheaf f).val.obj (op U), (idealι f).val.app (op U) l = r := by
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let a := structureMap f
  let e := PreservesKernel.iso E a ≪≫ ModuleCat.kernelIsoKer (E.map a)
  have hker : (E.map a).hom r = 0 := hr
  let z : (E.map a).hom.ker := ⟨r, hker⟩
  refine ⟨e.inv z, ?_⟩
  have he : e.inv ≫ E.map (kernel.ι a) = ModuleCat.ofHom (E.map a).hom.ker.subtype := by
    dsimp only [e, Iso.trans_inv]
    erw [Category.assoc, PreservesKernel.iso_inv_ι, ModuleCat.kernelIsoKer_inv_kernel_ι]
  exact ConcreteCategory.congr_hom he z

/-- Killing the ideal action is sufficient for descent to the actual closed subscheme. No support or
divisor-category object is postulated. -/
lemma exists_coherent_preimage {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : Y.Modules) [M.IsFinitePresentation]
    (h : (ActualSheafTensor.idealAction Y.sheaf (idealι f)).app M = 0) :
    ∃ N : CoherentGlobal.Coh X, Nonempty ((pushforward f).obj N.obj ≅ M) := by
  apply CoherentGlobal.exists_closed_preimage_of_annihilated f M
  intro U r hr m
  obtain ⟨l, hl⟩ := ideal_section_lift f U r hr
  rw [← hl]
  exact ActualSheafTensor.idealAction_annihilates_sections (idealι f) M h U l m
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The canonical pure-tensor section of the tensor sheaf. -/
def pure (M N : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (tensor R M N).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val)).app U)
      (x ⊗ₜ[R.obj.obj U] y)

lemma tensor_hom_ext {M N Z : SheafOfModules.{u} (ringSheaf R)}
    {f g : tensor R M N ⟶ Z}
    (h : ∀ U (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (pure R M N U x y) = g.val.app U (pure R M N U x y)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).homEquiv _ _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn (R := R.obj.obj U) with
  | tmul x y => exact h U x y
  | add x y hx hy => erw [map_add, map_add, hx, hy]

lemma tensorLeftMap_pure {M M' : SheafOfModules.{u} (ringSheaf R)}
    (g : M ⟶ M') (N : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((tensorLeftMap R g).app N).val.app U (pure R M N U x y) =
      pure R M' N U (g.val.app U x) y := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.naturality
    (g.val ▷ N.val)
  exact (congrArg (fun k => k.app U (x ⊗ₜ[R.obj.obj U] y)) h).symm

private local instance sectionSMul (N : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) :
    SMul (R.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule.toSMul

lemma leftUnitIso_pure (N : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) (r : R.obj.obj U) (y : N.val.obj U) :
    (leftUnitIso R N).hom.val.app U (pure R (SheafOfModules.unit _) N U r y) = r • y := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  have h : adj.homEquiv _ _ (leftUnitIso R N).hom = (λ_ N.val).hom := by
    apply (adj.homEquiv _ _).symm.injective
    erw [Equiv.symm_apply_apply, adj.homEquiv_counit]
    rfl
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.app U (r ⊗ₜ[R.obj.obj U] y)) h
end ActualSheafTensor

end

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace TensorChangeScalars
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
  (M N : ModuleCat.{u} R)

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e

/-- The identity on underlying sections, with the scalar action transported along a coefficient-ring
isomorphism. -/
def transportEquiv : M ≃ₛₗ[e.toRingHom]
    ((ModuleCat.restrictScalars e.symm.toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e.symm (e r) • x
    rw [e.symm_apply_apply]

/-- Restriction through a ring isomorphism commutes with tensor product. The formula on pure tensors
is literally the identity on both factors. -/
def tensorEquiv :
    ((ModuleCat.restrictScalars e.symm.toRingHom).obj (ModuleCat.of R (M ⊗[R] N))) ≃ₗ[S]
      (((ModuleCat.restrictScalars e.symm.toRingHom).obj M) ⊗[S]
        ((ModuleCat.restrictScalars e.symm.toRingHom).obj N)) where
  toFun := TensorProduct.congr (transportEquiv e M) (transportEquiv e N)
  invFun := (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)).symm
  left_inv := (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)).left_inv
  right_inv := (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)).right_inv
  map_add' := (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)).map_add
  map_smul' r z := by
    change (TensorProduct.congr (transportEquiv e M) (transportEquiv e N))
      ((e.symm r) • (z : M ⊗[R] N)) =
      r • (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)) z
    calc
      _ = e.toRingHom (e.symm r) •
          (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)) z :=
        (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)).map_smulₛₗ _ _
      _ = _ := congrArg
        (fun a : S => a • (TensorProduct.congr (transportEquiv e M) (transportEquiv e N)) z)
        (e.apply_symm_apply r)

@[simp] lemma tensorEquiv_tmul (x : M) (y : N) :
    tensorEquiv e M N (x ⊗ₜ[R] y) = (transportEquiv e M x) ⊗ₜ[S] (transportEquiv e N y) := rfl

@[simp] lemma tensorEquiv_symm_tmul
    (x : (ModuleCat.restrictScalars e.symm.toRingHom).obj M)
    (y : (ModuleCat.restrictScalars e.symm.toRingHom).obj N) :
    (tensorEquiv e M N).symm (x ⊗ₜ[S] y) = x ⊗ₜ[R] y := rfl
end TensorChangeScalars

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ModuleSheafification
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [Functor.IsCocontinuous F J K]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The canonical sheafification comparison for modules and any continuous cocontinuous site
functor, including nontrivial scalar transport. -/
def comparison (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.sheafification (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
      (SheafOfModules.pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))

lemma comparison_toSheaf (P : PresheafOfModules.{u} R.obj) :
    (SheafOfModules.toSheaf S).map (comparison F φ P) =
      (F.pushforwardContinuousSheafificationCompatibility AddCommGrpCat J K).hom.app
        P.presheaf := by
  unfold comparison
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (F.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat J K P.presheaf).symm

instance comparison_isIso (P : PresheafOfModules.{u} R.obj) : IsIso (comparison F φ P) := by
  have : IsIso ((SheafOfModules.toSheaf S).map (comparison F φ P)) := by
    rw [comparison_toSheaf]
    exact inferInstanceAs (IsIso
      (((F.pushforwardContinuousSheafificationCompatibility AddCommGrpCat J K).app P.presheaf).hom))
  exact isIso_of_reflects_iso (comparison F φ P) (SheafOfModules.toSheaf S)
omit [Functor.IsCocontinuous F J K] in
/-- The defining unit identity of the comparison, retained so that projection formulas can be
checked on sections without unfolding sheafification. -/
lemma comparison_unit (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app
        ((PresheafOfModules.pushforward φ.hom).obj P) ≫
      (SheafOfModules.forget S).map (comparison F φ P) =
    (PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) := by
  change PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj) (comparison F φ P) = _
  exact Equiv.apply_symm_apply _ _

end ModuleSheafification


end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
open Scheme.Modules
variable (X : Scheme.{0}) (U : X.Opens)

/-- The coefficient-ring map for open-scheme restriction. -/
def schemeRingRestrictHom : U.toScheme.ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X)).obj
      X.ringCatSheaf :=
  ⟨Functor.whiskerRight
    ({ app V := (U.ι.appIso V.unop).inv } :
      U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf)
    (forget₂ CommRingCat RingCat)⟩

/-- The concrete presheaf restriction underlying open-scheme restriction. -/
def schemePresheafRestrict : PresheafOfModules.{0} X.ringCatSheaf.obj ⥤
    PresheafOfModules.{0} U.toScheme.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (schemeRingRestrictHom X U).hom

/-- Canonical open restriction comparison for module sheafification. -/
def schemeSheafifyRestrictMap (P : PresheafOfModules.{0} X.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
        ((schemePresheafRestrict X U).obj P) ⟶
      (restrictFunctor U.ι).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) :=
  ModuleSheafification.comparison U.ι.opensFunctor (schemeRingRestrictHom X U) P

instance schemeSheafifyRestrictMap_isIso (P : PresheafOfModules.{0} X.ringCatSheaf.obj) :
    IsIso (schemeSheafifyRestrictMap X U P) :=
  ModuleSheafification.comparison_isIso U.ι.opensFunctor (schemeRingRestrictHom X U) P

/-- Tensor presheaves commute with restriction to an open subscheme. -/
def schemePresheafTensorRestrictIso (M N : PresheafOfModules.{0} X.ringCatSheaf.obj) :
    (schemePresheafRestrict X U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) M N) ≅
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.sheaf.obj)
      ((schemePresheafRestrict X U).obj M) ((schemePresheafRestrict X U).obj N) :=
  PresheafOfModules.isoMk (fun V =>
    (TensorChangeScalars.tensorEquiv (U.ι.appIso V.unop).commRingCatIsoToRingEquiv
      (M.obj (op (U.ι ''ᵁ V.unop))) (N.obj (op (U.ι ''ᵁ V.unop)))).toModuleIso)
    (by
      intro V W g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy => erw [map_add, map_add, hx, hy])

/-- The tensor sheaf commutes with open-scheme restriction. -/
def tensorSchemeRestrictIso (M N : X.Modules) :
    (restrictFunctor U.ι).obj (tensor X.sheaf M N) ≅
      tensor U.toScheme.sheaf ((restrictFunctor U.ι).obj M) ((restrictFunctor U.ι).obj N) :=
  (letI := schemeSheafifyRestrictMap_isIso X U
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val)
   asIso (schemeSheafifyRestrictMap X U
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (schemePresheafTensorRestrictIso X U M.val N.val)
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor
open Scheme.Modules
variable {X : Scheme.{0}} (L : X.Modules) (d : LineTrivialization X.sheaf L)

/-- A slice-site line trivialization is an trivialization on the corresponding open subscheme; no
extra local freeness hypothesis is added. -/
def LineTrivialization.schemeIso (i : d.I) :
    (restrictFunctor (Scheme.Opens.ι (d.obj i))).obj L ≅ SheafOfModules.unit (Scheme.Opens.toScheme (d.obj i)).ringCatSheaf :=
  ((overFunctorEquiv (d.obj i)).app L).symm ≪≫
    (overEquiv (d.obj i)).functor.mapIso (d.iso i) ≪≫
    (overFunctorEquiv (d.obj i)).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    restrictUnitIso (Scheme.Opens.ι (d.obj i))
end ActualSheafTensor

end

end OAI
