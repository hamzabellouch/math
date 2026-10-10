import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeCategory
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

namespace OAI

section

/-! # Semantic class identifications in the Kan–Quillen theorem

Goerss–Jardine, Theorems I.11.3–I.11.4 and Corollary II.8.6 identify
the boundary and horn lifting classes with the geometric realization
weak equivalences and Kan fibrations. Algebraic factorization, retract
stability and two-out-of-three give the other model axioms.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

/-- The semantic class identifications and source cancellation
supply the Kan–Quillen model axioms. -/
theorem kanQuillenInput_of_remaining_semantics
    (hpre : realizationWeakEquivalences.{0}.HasOfPrecompProperty realizationWeakEquivalences)
    (hb : I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0})
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) :
    KanQuillenPublishedInput.{0} := by
  let h2 : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := {
    toIsStableUnderComposition := inferInstance
    toHasOfPostcompProperty := inferInstance
    toHasOfPrecompProperty := hpre }
  exact kanQuillenInput_of_semantic_classes h2 hb hh

/-- The two semantic class identifications of the Kan–Quillen theorem
suffice, using the homotopy-group proof of two-out-of-three. -/
theorem kanQuillenInput_of_class_identifications
    (hb : I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0})
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) :
    KanQuillenPublishedInput.{0} :=
  kanQuillenInput_of_semantic_classes inferInstance hb hh

end Thomason.Construction

end

section

/-! # Reduction of the semantic KQ input to the anodyne identification

From the single published equality identifying anodyne maps, the concrete
cylinder lifts prove boundary-lifting maps weak. Factorization and a second
arrow retract then identify the trivial Kan fibrations. No model-category
conclusion or equivalent higher-category transfer assertion is assumed.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

/-- The boundary identification follows from the anodyne identification,
the explicit cylinder construction, and the two proved algebraic WFS. -/
theorem boundary_class_of_anodyne_class
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) :
    I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0} := by
  have hend₀ (X : SSet.{0}) : realizationWeakEquivalences (SSet.ι₀ (X := X)) := by
    have ha := anodyne_iota_zero X
    rw [hh] at ha
    exact ha.2
  have hend₁ (X : SSet.{0}) : realizationWeakEquivalences (SSet.ι₁ (X := X)) := by
    have ha := anodyne_iota_one X
    rw [hh] at ha
    exact ha.2
  have hw {X Y : SSet.{0}} (f : X ⟶ Y) (hf : I.rlp f) :
      realizationWeakEquivalences f :=
    boundary_rlp_weak_of_endpoints f hf (hend₀ X) (hend₁ X)
  apply le_antisymm
  · intro X Y f hf
    have hm : (monomorphisms SSet.{0}).rlp f := by rwa [SSet.rlp_monomorphisms]
    exact ⟨antitone_rlp J_le_monomorphisms f hm, hw f hf⟩
  · intro X Y f hf
    let := boundary_weakFactorizationSystem
    let d := factorizationData (monomorphisms SSet.{0}) I.rlp f
    have hq := hw d.p d.hp
    have hiw : realizationWeakEquivalences d.i := by
      apply realizationWeakEquivalences.of_postcomp d.i d.p hq
      simpa only [d.fac] using hf.2
    have hia : SSet.anodyneExtensions d.i := by
      rw [hh]
      exact ⟨d.hi, hiw⟩
    let : HasLiftingProperty d.i f := hia f hf.1
    let sq : CommSq (𝟙 X) d.i f d.p := ⟨(Category.id_comp f).trans d.fac.symm⟩
    let r : RetractArrow f d.p := {
      i := Arrow.homMk d.i (𝟙 Y) (d.fac.trans (Category.comp_id f).symm)
      r := Arrow.homMk sq.lift (𝟙 Y) (sq.fac_right.trans (Category.comp_id d.p).symm)
      retract := by
        apply Arrow.hom_ext
        · exact sq.fac_left
        · simp }
    exact I.rlp.of_retract r d.hp

/-- Only the anodyne/realization identification remains as a KQ input. -/
theorem kanQuillenInput_of_anodyne_class
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) :
    KanQuillenPublishedInput.{0} :=
  kanQuillenInput_of_class_identifications (boundary_class_of_anodyne_class hh) hh

end Thomason.Construction

end

section

/-!
# Gluing a stationary strict cylinder through an arbitrary pushout

This is the omega-dimensional gluing lemma of Section 3. It uses only the
published cocontinuous right Gray cylinder; neither attaching map is assumed
injective, free or cofibrant.
-/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory CategoryTheory.Limits

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)

/-- A stationary cylinder descends across every pushout. The last two
conclusions identify its endpoint maps on both pushout pieces. -/
theorem glue_stationary_cylinder {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (P : G.cylinder.obj B ⟶ B)
    (hP : G.cylinder.map i ≫ P = G.projection.app A ≫ i) :
    ∃ Q : G.cylinder.obj Y ⟶ Y,
      G.cylinder.map b ≫ Q = P ≫ b ∧
      G.cylinder.map j ≫ Q = G.projection.app X ≫ j ∧
      (∀ δ, j ≫ ((G.endpoint δ).app Y ≫ Q) = j) ∧
      (∀ δ, b ≫ ((G.endpoint δ).app Y ≫ Q) = ((G.endpoint δ).app B ≫ P) ≫ b) := by
  have := G.preservesColimits
  have hc : G.cylinder.map i ≫ (P ≫ b) =
      G.cylinder.map a ≫ (G.projection.app X ≫ j) := by
    calc
      _ = (G.cylinder.map i ≫ P) ≫ b := (Category.assoc _ _ _).symm
      _ = (G.projection.app A ≫ i) ≫ b := congrArg (fun k => k ≫ b) hP
      _ = G.projection.app A ≫ (a ≫ j) := by rw [Category.assoc, hp.w]
      _ = (G.projection.app A ≫ a) ≫ j := (Category.assoc _ _ _).symm
      _ = (G.cylinder.map a ≫ G.projection.app X) ≫ j :=
        congrArg (fun k => k ≫ j) (G.projection.naturality a).symm
      _ = _ := Category.assoc _ _ _
  obtain ⟨Q, hb, hj⟩ := (hp.map G.cylinder).exists_desc (P ≫ b) (G.projection.app X ≫ j) hc
  refine ⟨Q, hb, hj, ?_, ?_⟩
  · intro δ
    calc
      _ = (j ≫ (G.endpoint δ).app Y) ≫ Q := (Category.assoc _ _ _).symm
      _ = ((G.endpoint δ).app X ≫ G.cylinder.map j) ≫ Q :=
        congrArg (fun k => k ≫ Q) ((G.endpoint δ).naturality j)
      _ = (G.endpoint δ).app X ≫ (G.projection.app X ≫ j) := by rw [Category.assoc, hj]
      _ = ((G.endpoint δ).app X ≫ G.projection.app X) ≫ j := (Category.assoc _ _ _).symm
      _ = (𝟙 X : X ⟶ X) ≫ j := congrArg (fun k => k ≫ j) (G.endpoint_projection δ X)
      _ = j := Category.id_comp j
  · intro δ
    calc
      _ = (b ≫ (G.endpoint δ).app Y) ≫ Q := (Category.assoc _ _ _).symm
      _ = ((G.endpoint δ).app B ≫ G.cylinder.map b) ≫ Q :=
        congrArg (fun k => k ≫ Q) ((G.endpoint δ).naturality b)
      _ = (G.endpoint δ).app B ≫ (P ≫ b) := by rw [Category.assoc, hb]
      _ = _ := (Category.assoc _ _ _).symm

end Thomason.Construction.RightGrayInput

end

section

/-!
# Gluing cylinders in positive finite dimension

The inclusion of finite-dimensional strict categories need not preserve
pushouts. Instead, the actual right Gray adjunction and its truncated
internal hom turn the finite pushout directly into the needed gluing
property for ambient right cylinders.
-/

namespace Thomason.Construction.RightGrayInput

open CategoryTheory

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (t : GrayTruncationInput G) {n : ℕ}

include t

/-- Finite pushouts glue the ambient right Gray cylinders because their
maps into a finite target are represented by a finite internal hom. -/
theorem glue_finite_stationary_cylinder
    {A B X Y : StrictOmegaCategory.Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (P : G.cylinder.obj B.val ⟶ B.val)
    (hP : G.cylinder.map i ≫ P = G.projection.app A.val ≫ i) :
    ∃ Q : G.cylinder.obj Y.val ⟶ Y.val,
      G.cylinder.map b ≫ Q = P ≫ b ∧
      G.cylinder.map j ≫ Q = G.projection.app X.val ≫ j ∧
      (∀ δ, (StrictOmegaCategory.inclusion (n + 1)).map j ≫
        ((G.endpoint δ).app Y.val ≫ Q) = (StrictOmegaCategory.inclusion (n + 1)).map j) ∧
      (∀ δ, (StrictOmegaCategory.inclusion (n + 1)).map b ≫
        ((G.endpoint δ).app Y.val ≫ Q) = ((G.endpoint δ).app B.val ≫ P) ≫
          (StrictOmegaCategory.inclusion (n + 1)).map b) := by
  let ib : A.val ⟶ B.val := (StrictOmegaCategory.inclusion (n + 1)).map i
  let ab : A.val ⟶ X.val := (StrictOmegaCategory.inclusion (n + 1)).map a
  let bb : B.val ⟶ Y.val := (StrictOmegaCategory.inclusion (n + 1)).map b
  let jb : X.val ⟶ Y.val := (StrictOmegaCategory.inclusion (n + 1)).map j
  have hw : ib ≫ bb = ab ≫ jb := hp.w
  let H : StrictOmegaCategory.Truncated (n + 1) :=
    ⟨G.internalHom.obj Y.val, t.truncated n Y⟩
  let f : B ⟶ H := G.adjunction.homEquiv B.val Y.val (P ≫ b)
  let g : X ⟶ H := G.adjunction.homEquiv X.val Y.val (G.projection.app X.val ≫ j)
  have hc : G.cylinder.map ib ≫ (P ≫ bb) =
      G.cylinder.map ab ≫ (G.projection.app X.val ≫ jb) := by
    calc
      _ = (G.cylinder.map ib ≫ P) ≫ bb := (Category.assoc _ _ _).symm
      _ = (G.projection.app A.val ≫ ib) ≫ bb := congrArg (fun k => k ≫ bb) hP
      _ = G.projection.app A.val ≫ (ab ≫ jb) := by rw [Category.assoc, hw]
      _ = (G.projection.app A.val ≫ ab) ≫ jb := (Category.assoc _ _ _).symm
      _ = (G.cylinder.map ab ≫ G.projection.app X.val) ≫ jb :=
        congrArg (fun k => k ≫ jb) (G.projection.naturality ab).symm
      _ = _ := Category.assoc _ _ _
  have hfg : i ≫ f = a ≫ g :=
    (G.adjunction.homEquiv_naturality_left i (P ≫ b)).symm.trans
      ((congrArg (G.adjunction.homEquiv A.val Y.val) hc).trans
        (G.adjunction.homEquiv_naturality_left a (G.projection.app X.val ≫ j)))
  obtain ⟨q, hb, hj⟩ := hp.exists_desc f g hfg
  let Q : G.cylinder.obj Y.val ⟶ Y.val := (G.adjunction.homEquiv Y.val Y.val).symm q
  have hbQ : G.cylinder.map b ≫ Q = P ≫ b := by
    apply (G.adjunction.homEquiv B.val Y.val).injective
    exact (G.adjunction.homEquiv_naturality_left b Q).trans
      ((congrArg (fun k => b ≫ k) ((G.adjunction.homEquiv Y.val Y.val).apply_symm_apply q)).trans hb)
  have hjQ : G.cylinder.map j ≫ Q = G.projection.app X.val ≫ j := by
    apply (G.adjunction.homEquiv X.val Y.val).injective
    exact (G.adjunction.homEquiv_naturality_left j Q).trans
      ((congrArg (fun k => j ≫ k) ((G.adjunction.homEquiv Y.val Y.val).apply_symm_apply q)).trans hj)
  refine ⟨Q, hbQ, hjQ, ?_, ?_⟩
  · intro δ
    calc
      _ = (jb ≫ (G.endpoint δ).app Y.val) ≫ Q := (Category.assoc _ _ _).symm
      _ = ((G.endpoint δ).app X.val ≫ G.cylinder.map jb) ≫ Q :=
        congrArg (fun k => k ≫ Q) ((G.endpoint δ).naturality jb)
      _ = (G.endpoint δ).app X.val ≫ (G.projection.app X.val ≫ jb) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => (G.endpoint δ).app X.val ≫ k) hjQ)
      _ = ((G.endpoint δ).app X.val ≫ G.projection.app X.val) ≫ jb := (Category.assoc _ _ _).symm
      _ = (𝟙 X.val : X.val ⟶ X.val) ≫ jb :=
        congrArg (fun k => k ≫ jb) (G.endpoint_projection δ X.val)
      _ = jb := Category.id_comp jb
  · intro δ
    calc
      _ = (bb ≫ (G.endpoint δ).app Y.val) ≫ Q := (Category.assoc _ _ _).symm
      _ = ((G.endpoint δ).app B.val ≫ G.cylinder.map bb) ≫ Q :=
        congrArg (fun k => k ≫ Q) ((G.endpoint δ).naturality bb)
      _ = (G.endpoint δ).app B.val ≫ (P ≫ bb) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => (G.endpoint δ).app B.val ≫ k) hbQ)
      _ = _ := (Category.assoc _ _ _).symm

end Thomason.Construction.RightGrayInput

end

section

/-! # Full fibres of the original attaching pushout

First lift a given unlabelled pushout to its actual slice. The published
fibre-colimit theorem then applies to these original four maps. Constant
labels are identified with the original category, on every strict cell.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

section Slice

variable {C : Type*} [Category* C] {L A B X Y : C}
  {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}

/-- Compatible labels lift the given pushout itself to the slice. -/
theorem isPushout_over (hp : IsPushout i a b j)
    (pA : A ⟶ L) (pB : B ⟶ L) (pX : X ⟶ L) (pY : Y ⟶ L)
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout (Over.homMk i hi : Over.mk pA ⟶ Over.mk pB)
      (Over.homMk a ha : Over.mk pA ⟶ Over.mk pX)
      (Over.homMk b hb : Over.mk pB ⟶ Over.mk pY)
      (Over.homMk j hj : Over.mk pX ⟶ Over.mk pY) := by
  apply IsPushout.of_map_of_faithful (Over.forget L)
  exact hp

end Slice

namespace StrictOmegaCategory

/-- The constant strict label, including every positive-dimensional cell. -/
def constantLabel (C : StrictOmegaCategory.{0}) (e : Fin 2) :
    C ⟶ StrictPoset.category (Fin 2) := orderedLabel (fun _ => e) (fun _ => le_rfl)

theorem constantLabel_apply (C : StrictOmegaCategory.{0}) (e : Fin 2) (x : C) :
    (constantLabel C e).toFun x = StrictPoset.identity e := rfl

/-- The fibre of a constant label over its value is the entire original category. -/
def constantFiberIso (C : StrictOmegaCategory.{0}) (e : Fin 2) :
    labelFiber (constantLabel C e) e ≅ C where
  hom := labelFiberInclusion (constantLabel C e) e
  inv :=
    { toFun x := ⟨x, (fullCell_label_iff (constantLabel C e) e x).mpr rfl⟩
      map_face _ _ _ := Subtype.ext rfl
      map_comp _ _ _ _ _ := Subtype.ext rfl }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- The other endpoint fibre of a constant label has no cells. -/
theorem constantFiber_empty (C : StrictOmegaCategory.{0}) (e d : Fin 2) (hed : e ≠ d) :
    IsEmpty (labelFiber (constantLabel C e) d) := by
  refine ⟨fun x => hed ?_⟩
  have he := (fullCell_label_iff (constantLabel C e) d x.val).mp x.property
  exact congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he

end StrictOmegaCategory

namespace PublishedLabelFiberInput

variable (f : PublishedLabelFiberInput)

include f

/-- The fibre square is a pushout for the original unlabelled attachment,
once its four strict labels commute. -/
theorem omega_pushout_fibers (e : Fin 2)
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ StrictPoset.category (Fin 2)) (pB : B ⟶ StrictPoset.category (Fin 2))
    (pX : X ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout (labelFiberMap pA pB e i hi) (labelFiberMap pA pX e a ha)
      (labelFiberMap pB pY e b hb) (labelFiberMap pX pY e j hj) :=
  f.omega_isPushout e (isPushout_over hp pA pB pX pY hi ha hb hj)

/-- If the original map identifies its source with a whole label fibre,
then the attached copy of `X` is again precisely that full fibre. In
particular the arbitrary attaching map creates no new identifications in `X`. -/
theorem omega_attaching_map_mono (e : Fin 2)
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = constantLabel A e)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X e)
    [IsIso (labelFiberMap (constantLabel A e) pB e i hi)] : Mono j := by
  have ha : a ≫ constantLabel X e = constantLabel A e := by
    apply Hom.ext
    rfl
  have hpF := f.omega_pushout_fibers e hp (constantLabel A e) pB
    (constantLabel X e) pY hi ha hb hj
  have : IsIso (labelFiberMap (constantLabel X e) pY e j hj) := hpF.isIso_inr_of_isIso
  have he : (constantFiberIso X e).inv ≫
      labelFiberMap (constantLabel X e) pY e j hj ≫ labelFiberInclusion pY e = j := by
    apply Hom.ext
    rfl
  rw [← he]
  infer_instance

/-- The same compatibility theorem uses the finite-category pushout itself. -/
theorem finite_pushout_fibers (n : ℕ) (e : Fin 2)
    {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ finiteInterval n) (pB : B ⟶ finiteInterval n)
    (pX : X ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout
      ((finiteLabelFiberFunctor n e).map (Over.homMk i hi : Over.mk pA ⟶ Over.mk pB))
      ((finiteLabelFiberFunctor n e).map (Over.homMk a ha : Over.mk pA ⟶ Over.mk pX))
      ((finiteLabelFiberFunctor n e).map (Over.homMk b hb : Over.mk pB ⟶ Over.mk pY))
      ((finiteLabelFiberFunctor n e).map (Over.homMk j hj : Over.mk pX ⟶ Over.mk pY)) :=
  f.finite_isPushout n e (isPushout_over hp pA pB pX pY hi ha hb hj)

end PublishedLabelFiberInput
end Thomason.Construction

end

section

/-! # Object covers and Street covers of arbitrary attachments

The proved object/codiscrete adjunction makes the two legs of any strict
pushout jointly surjective on objects. Hence compatible sieve covers on
the summands cover its actual Street nerve after attachment.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

/-- Every object of an arbitrary strict pushout comes from one of its two legs. -/
theorem pushout_objects_covered {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (y : Objects Y) :
    (∃ x : Objects B, b.toOneFunctor.obj x = y) ∨
      ∃ x : Objects X, j.toOneFunctor.obj x = y :=
  Types.eq_or_eq_of_isPushout (hp.map objectFunctor) y

/-- Binary object covers survive attachment even when the attaching functor
identifies old objects or cells. -/
theorem pushout_label_cover {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (p q : Y ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    (hb : ∀ x : Objects B, p.toFun (b.toFun x.val) = StrictPoset.identity e ∨
      q.toFun (b.toFun x.val) = StrictPoset.identity e)
    (hj : ∀ x : Objects X, p.toFun (j.toFun x.val) = StrictPoset.identity e ∨
      q.toFun (j.toFun x.val) = StrictPoset.identity e) :
    ∀ y : Objects Y, p.toFun y.val = StrictPoset.identity e ∨
      q.toFun y.val = StrictPoset.identity e := by
  intro y
  rcases pushout_objects_covered hp y with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact hb x
  · exact hj x

/-- The object-cover argument also uses genuine finite-category pushouts. -/
theorem finite_pushout_label_cover {n : ℕ} {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (p q : Y.val ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    (hb : ∀ x : Objects B.val, p.toFun (b.toFun x.val) = StrictPoset.identity e ∨
      q.toFun (b.toFun x.val) = StrictPoset.identity e)
    (hj : ∀ x : Objects X.val, p.toFun (j.toFun x.val) = StrictPoset.identity e ∨
      q.toFun (j.toFun x.val) = StrictPoset.identity e) :
    ∀ y : Objects Y.val, p.toFun y.val = StrictPoset.identity e ∨
      q.toFun y.val = StrictPoset.identity e := by
  intro y
  rcases finite_pushout_objects_covered hp y with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact hb x
  · exact hj x

end Thomason.Construction.StrictOmegaCategory

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- The post-attachment sieve cover is a cover of actual Street simplices. -/
theorem pushout_sieve_street_cover
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (p q : Y ⟶ StrictPoset.category (Fin 2))
    (hb : ∀ x : Objects B, p.toFun (b.toFun x.val) = StrictPoset.identity 0 ∨
      q.toFun (b.toFun x.val) = StrictPoset.identity 0)
    (hj : ∀ x : Objects X, p.toFun (j.toFun x.val) = StrictPoset.identity 0 ∨
      q.toFun (j.toFun x.val) = StrictPoset.identity 0) :
    h.fiberStreetSubcomplex p 0 ⊔ h.fiberStreetSubcomplex q 0 = ⊤ :=
  h.sieve_street_cover p q (pushout_label_cover hp p q 0 hb hj)

/-- No preservation of pushouts by the inclusion into omega-categories is
needed for the positive finite-dimensional Street cover. -/
theorem finite_pushout_sieve_street_cover
    {n : ℕ} {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (p q : Y.val ⟶ StrictPoset.category (Fin 2))
    (hb : ∀ x : Objects B.val, p.toFun (b.toFun x.val) = StrictPoset.identity 0 ∨
      q.toFun (b.toFun x.val) = StrictPoset.identity 0)
    (hj : ∀ x : Objects X.val, p.toFun (j.toFun x.val) = StrictPoset.identity 0 ∨
      q.toFun (j.toFun x.val) = StrictPoset.identity 0) :
    h.fiberStreetSubcomplex p 0 ⊔ h.fiberStreetSubcomplex q 0 = ⊤ :=
  h.sieve_street_cover p q (finite_pushout_label_cover hp p q 0 hb hj)

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Acyclic span maps induce actual weak equivalences on pushouts

The proof splits the comparison into two cobase changes: the map at C,
then the relative map at B. Both are acyclic cofibrations by KQ lifting.
-/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable abbrev middle {X Y : Diagram} (f : X ⟶ Y) :=
  Limits.pushout X.left (f.a ≫ Y.right)

noncomputable def toMiddle {X Y : Diagram} (f : X ⟶ Y) : pushout X ⟶ middle f :=
  Limits.pushout.desc (Limits.pushout.inl _ _) (f.c ≫ Limits.pushout.inr _ _) (by
    rw [← Category.assoc, f.right_w, ← Limits.pushout.condition])

noncomputable def fromMiddle {X Y : Diagram} (f : X ⟶ Y) : middle f ⟶ pushout Y :=
  Limits.pushout.desc (f.b ≫ Limits.pushout.inl _ _) (Limits.pushout.inr _ _) (by
    rw [← Category.assoc, f.left_w, Category.assoc, Limits.pushout.condition,
      ← Category.assoc])

noncomputable def relativeToMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout X.left f.a ⟶ middle f :=
  Limits.pushout.desc (Limits.pushout.inl _ _) (Y.right ≫ Limits.pushout.inr _ _)
    (by rw [← Category.assoc, ← Limits.pushout.condition])

@[reassoc (attr := simp)] theorem inl_toMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inl X.left X.right ≫ toMiddle f = Limits.pushout.inl _ _ :=
  Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_toMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inr X.left X.right ≫ toMiddle f = f.c ≫ Limits.pushout.inr _ _ :=
  Limits.pushout.inr_desc _ _ _

@[reassoc (attr := simp)] theorem inl_fromMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inl X.left (f.a ≫ Y.right) ≫ fromMiddle f =
      f.b ≫ Limits.pushout.inl _ _ := Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_fromMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inr X.left (f.a ≫ Y.right) ≫ fromMiddle f =
      Limits.pushout.inr _ _ := Limits.pushout.inr_desc _ _ _

@[reassoc (attr := simp)] theorem inl_relativeToMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inl X.left f.a ≫ relativeToMiddle f = Limits.pushout.inl _ _ :=
  Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_relativeToMiddle {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inr X.left f.a ≫ relativeToMiddle f =
      Y.right ≫ Limits.pushout.inr _ _ := Limits.pushout.inr_desc _ _ _

theorem toMiddle_isPushout {X Y : Diagram} (f : X ⟶ Y) :
    IsPushout (Limits.pushout.inr X.left X.right) f.c
      (toMiddle f) (Limits.pushout.inr X.left (f.a ≫ Y.right)) := by
  have ht : IsPushout X.left (X.right ≫ f.c)
      (Limits.pushout.inl X.left (f.a ≫ Y.right))
      (Limits.pushout.inr X.left (f.a ≫ Y.right)) := by
    rw [f.right_w]
    exact IsPushout.of_hasPushout _ _
  have ht' : IsPushout X.left (X.right ≫ f.c)
      (Limits.pushout.inl X.left X.right ≫ toMiddle f)
      (Limits.pushout.inr X.left (f.a ≫ Y.right)) := by simpa using ht
  exact ht'.of_top (inr_toMiddle f) (IsPushout.of_hasPushout _ _)

theorem fromMiddle_isPushout {X Y : Diagram} (f : X ⟶ Y) :
    IsPushout (relativeB f) (relativeToMiddle f)
      (Limits.pushout.inl Y.left Y.right) (fromMiddle f) := by
  have hl : IsPushout (Limits.pushout.inr X.left f.a) Y.right
      (relativeToMiddle f) (Limits.pushout.inr X.left (f.a ≫ Y.right)) := by
    have ht : IsPushout X.left (f.a ≫ Y.right)
        (Limits.pushout.inl X.left f.a ≫ relativeToMiddle f)
        (Limits.pushout.inr X.left (f.a ≫ Y.right)) := by
      simpa using (IsPushout.of_hasPushout X.left (f.a ≫ Y.right))
    exact ht.of_top (inr_relativeToMiddle f) (IsPushout.of_hasPushout _ _)
  have ht : IsPushout (Limits.pushout.inr X.left f.a ≫ relativeB f) Y.right
      (Limits.pushout.inl Y.left Y.right)
      (Limits.pushout.inr X.left (f.a ≫ Y.right) ≫ fromMiddle f) := by
    simpa using (IsPushout.of_hasPushout Y.left Y.right)
  apply ht.of_left _ hl
  apply Limits.pushout.hom_ext <;> simp [Limits.pushout.condition]

theorem toMiddle_fromMiddle {X Y : Diagram} (f : X ⟶ Y) :
    toMiddle f ≫ fromMiddle f = pushoutMap f := by
  apply Limits.pushout.hom_ext <;> simp

/-- The relative B map is acyclic when the A and B maps are weak
and the A and relative maps are cofibrations. -/
theorem relativeB_weak {X Y : Diagram} (f : X ⟶ Y)
    (kq : KanQuillenPublishedInput.{0}) (hi : Cofibration f)
    (ha : realizationWeakEquivalences f.a) (hb : realizationWeakEquivalences f.b) :
    realizationWeakEquivalences (relativeB f) := by
  have := kq.twoOutOfThree
  have := kq.fibrationFactorization
  let T := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
  have hT : T = J.rlp.llp := (MorphismProperty.llp_eq_of_wfs _ _).symm
  have : T.IsStableUnderCobaseChange := by rw [hT]; infer_instance
  have hleg := T.pushout_inl X.left f.a ⟨hi.monoA, ha⟩
  apply realizationWeakEquivalences.of_precomp (Limits.pushout.inl X.left f.a) _ hleg.2
  simpa using hb

/-- A span cofibration which is weak at each object induces a weak equivalence
of the actual simplicial pushouts. This derives the comparison from KQ. -/
theorem pushoutMap_weak_of_cofibration {X Y : Diagram} (f : X ⟶ Y)
    (kq : KanQuillenPublishedInput.{0}) (hi : Cofibration f)
    (ha : realizationWeakEquivalences f.a) (hb : realizationWeakEquivalences f.b)
    (hc : realizationWeakEquivalences f.c) : realizationWeakEquivalences (pushoutMap f) := by
  have := kq.twoOutOfThree
  have := kq.fibrationFactorization
  let T := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
  have hT : T = J.rlp.llp := (MorphismProperty.llp_eq_of_wfs _ _).symm
  have : T.IsStableUnderCobaseChange := by rw [hT]; infer_instance
  have hu := T.of_isPushout (toMiddle_isPushout f) ⟨hi.monoC, hc⟩
  have hv := T.of_isPushout (fromMiddle_isPushout f).flip
    ⟨hi.monoRelative, relativeB_weak f kq hi ha hb⟩
  rw [← toMiddle_fromMiddle f]
  exact realizationWeakEquivalences.comp_mem _ _ hu.2 hv.2

end Thomason.Construction.SimplicialSpan

end

section

/-!
# Actual generators for the Thomason lifting classes

The adjoints are the constructed `c Sd²` and `Ex² N`. The weak-equivalence
criterion uses only the already identified Kan--Quillen and extension inputs.
This establishes the generator interface without assuming a transferred model
structure or acyclicity of the new attaching maps.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

/-- The two actual adjoints transport a right lifting class to the image
of its generators, including the isomorphisms in `MorphismProperty.map`. -/
theorem rlp_map_eq_inverseImage {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (P : MorphismProperty C) :
    (P.map L).rlp = P.rlp.inverseImage R := by
  apply MorphismProperty.ext
  intro X Y p
  constructor
  · intro hp A B i hi
    exact (adj.hasLiftingProperty_iff i p).mp (hp (L.map i) (P.map_mem_map L i hi))
  · intro hp A B j hj
    obtain ⟨A', B', i, hi, ⟨e⟩⟩ := hj
    exact (HasLiftingProperty.iff_of_arrow_iso_left e p).mp
      ((adj.hasLiftingProperty_iff i p).mpr (hp i hi))

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Twice-subdivided boundary generators, categorified by the actual left adjoint. -/
noncomputable def thomasonGeneratingCofibrations : MorphismProperty StrictOmegaCategory.{0} :=
  I.map h.thomasonLeft

/-- Twice-subdivided horn generators, categorified by the actual left adjoint. -/
noncomputable def thomasonGeneratingAcyclicCofibrations : MorphismProperty StrictOmegaCategory.{0} :=
  J.map h.thomasonLeft

/-- Horn lifting after `Ex² N` is exactly lifting against the strict horn generators. -/
theorem thomasonFibrations_eq_generating_rlp :
    h.thomasonFibrations = h.thomasonGeneratingAcyclicCofibrations.rlp :=
  (rlp_map_eq_inverseImage h.thomasonAdjunction J).symm

/-- Boundary lifting against actual strict generators detects precisely
fibrations that are actual Street-nerve weak equivalences. -/
theorem thomason_trivialFibrations_eq_generating_rlp
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    h.thomasonFibrations ⊓ h.streetWeakEquivalences =
      h.thomasonGeneratingCofibrations.rlp :=
  (h.thomason_trivialFibrations_eq_boundary_lifting kq hj).trans
    (rlp_map_eq_inverseImage h.thomasonAdjunction I).symm

/-- The prescribed cofibrations are the left lifting class generated by
these boundary maps, before any model structure is asserted. -/
theorem thomasonCofibrations_eq_generating_llp_rlp
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    h.thomasonCofibrations = h.thomasonGeneratingCofibrations.rlp.llp :=
  congrArg MorphismProperty.llp (h.thomason_trivialFibrations_eq_generating_rlp kq hj)

/-- In particular the boundary generators are genuine prescribed cofibrations. -/
theorem generatingCofibrations_le_cofibrations
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    h.thomasonGeneratingCofibrations ≤ h.thomasonCofibrations := by
  rw [h.thomasonCofibrations_eq_generating_llp_rlp kq hj]
  exact h.thomasonGeneratingCofibrations.le_llp_rlp

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

noncomputable def thomasonRight : StrictOmegaCategory.Truncated.{0} (n + 1) ⥤ SSet.{0} :=
  h.finiteStreetNerve (n + 1) ⋙ SSet.ex ⋙ SSet.ex

noncomputable def thomasonFibrations :
    MorphismProperty (StrictOmegaCategory.Truncated.{0} (n + 1)) :=
  J.rlp.inverseImage (thomasonRight (n := n) h)

noncomputable def thomasonWeakEquivalences :
    MorphismProperty (StrictOmegaCategory.Truncated.{0} (n + 1)) :=
  realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n + 1))

noncomputable def thomasonGeneratingCofibrations :
    MorphismProperty (StrictOmegaCategory.Truncated.{0} (n + 1)) :=
  I.map (r.thomasonLeft h)

noncomputable def thomasonGeneratingAcyclicCofibrations :
    MorphismProperty (StrictOmegaCategory.Truncated.{0} (n + 1)) :=
  J.map (r.thomasonLeft h)

/-- The actual finite-dimensional horn lifting criterion. -/
theorem thomasonFibrations_eq_generating_rlp :
    thomasonFibrations (n := n) h = (r.thomasonGeneratingAcyclicCofibrations h).rlp :=
  (rlp_map_eq_inverseImage (r.thomasonAdjunction h) J).symm

/-- In every positive finite dimension, strict boundary lifting is equivalent
to horn lifting together with the actual Street weak-equivalence condition. -/
theorem thomason_trivialFibrations_eq_generating_rlp
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    thomasonFibrations (n := n) h ⊓ thomasonWeakEquivalences (n := n) h =
      (r.thomasonGeneratingCofibrations h).rlp := by
  have := kq.twoOutOfThree
  change _ = (I.map (r.thomasonLeft h)).rlp
  rw [rlp_map_eq_inverseImage (r.thomasonAdjunction h) I]
  apply MorphismProperty.ext
  intro X Y f
  change (J.rlp ((thomasonRight (n := n) h).map f) ∧
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map f)) ↔
      I.rlp ((thomasonRight (n := n) h).map f)
  rw [← kq.trivialFibrations_eq_boundary_rlp]
  apply and_congr Iff.rfl
  exact (realization_ex_twice_iff hj ((h.finiteStreetNerve (n + 1)).map f)).symm

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # A precise interface for the prescribed model structure

The classes are fixed before the axioms are supplied. The model below is
Mathlib's actual `ModelCategory`, with cofibrations defined by lifting
against the prescribed trivial fibrations. Properness uses unrestricted
base and cobase change, and local presentability has its usual meaning.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe v u

/-- The model axioms and proper/local-presentability conclusions needed
from the published abstract transfer theorem. This is data to be proved or
supplied by a precisely stated published implication, not a global axiom. -/
structure ProperCombinatorialAxioms (C : Type u) [Category.{v} C]
    (W F : MorphismProperty C) : Prop where
  finiteLimits : HasFiniteLimits C
  finiteColimits : HasFiniteColimits C
  locallyPresentable : IsLocallyPresentable.{v} C
  cofibrationFactorization : MorphismProperty.IsWeakFactorizationSystem (F ⊓ W).llp (F ⊓ W)
  fibrationFactorization : MorphismProperty.IsWeakFactorizationSystem ((F ⊓ W).llp ⊓ W) F
  leftProper : W.IsStableUnderCobaseChangeAgainst (F ⊓ W).llp
  rightProper : W.IsStableUnderBaseChangeAgainst F

namespace ProperCombinatorialAxioms

variable {C : Type u} [Category.{v} C] {W F : MorphismProperty C}

/-- Assemble the genuine model-category structure with the prescribed classes. -/
@[instance_reducible]
noncomputable def model (a : ProperCombinatorialAxioms C W F)
    [W.HasTwoOutOfThreeProperty] : ModelCategory C := by
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  letI : CategoryWithFibrations C := ⟨F⟩
  letI : CategoryWithCofibrations C := ⟨(F ⊓ W).llp⟩
  letI : (weakEquivalences C).HasTwoOutOfThreeProperty := ‹W.HasTwoOutOfThreeProperty›
  letI := a.finiteLimits
  letI := a.finiteColimits
  letI : MorphismProperty.IsWeakFactorizationSystem
      (cofibrations C) (trivialFibrations C) := a.cofibrationFactorization
  letI : MorphismProperty.IsWeakFactorizationSystem
      (trivialCofibrations C) (fibrations C) := a.fibrationFactorization
  exact ModelCategory.mk' C

/-- The weak class of this model is the original semantic class. -/
theorem model_weakEquivalences (a : ProperCombinatorialAxioms C W F)
    [W.HasTwoOutOfThreeProperty] :
    @weakEquivalences C _ (a.model.categoryWithWeakEquivalences) = W := rfl

/-- Its fibrations are the prescribed right-adjoint lifting class. -/
theorem model_fibrations (a : ProperCombinatorialAxioms C W F)
    [W.HasTwoOutOfThreeProperty] :
    @fibrations C _ (a.model.categoryWithFibrations) = F := rfl

/-- Its cofibrations are precisely the left lifting class specified in the paper. -/
theorem model_cofibrations (a : ProperCombinatorialAxioms C W F)
    [W.HasTwoOutOfThreeProperty] :
    @cofibrations C _ (a.model.categoryWithCofibrations) = (F ⊓ W).llp := rfl

end ProperCombinatorialAxioms
end Thomason.Construction

end

section

/-! # The actual Quillen adjunction preserves simplicial weak equivalences

Lifting gives preservation of (trivial) cofibrations by the constructed
left adjoint. Since all simplicial sets are cofibrant, Brown's factorization
then proves preservation of every realization weak equivalence. This bridge
uses the transferred model axioms, but no Street-localization theorem.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace ThomasonAdjunction

variable {C : Type 1} [Category.{0} C]
  {L : SSet.{0} ⥤ C} {N : C ⥤ SSet.{0}}
  (adj : L ⊣ (N ⋙ SSet.ex ⋙ SSet.ex)) (kq : KanQuillenPublishedInput.{0})
  (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))

include adj kq hj in
/-- The actual left adjoint takes every simplicial monomorphism to a
cofibration for the prescribed Thomason lifting classes. -/
theorem left_preserves_cofibrations {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] :
    (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓
      realizationWeakEquivalences.inverseImage N).llp (L.map f) := by
  have := kq.cofibrationFactorization
  have := kq.twoOutOfThree
  intro A B p hp
  apply (adj.hasLiftingProperty_iff f p).mpr
  exact MorphismProperty.hasLiftingProperty_of_wfs
    (W₁ := MorphismProperty.monomorphisms SSet.{0})
    (W₂ := J.rlp ⊓ realizationWeakEquivalences) f _ (by infer_instance)
    ⟨hp.1, (realization_ex_twice_iff hj (N.map p)).mpr hp.2⟩

variable (a : ProperCombinatorialAxioms C (realizationWeakEquivalences.inverseImage N)
  (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex)))

include adj kq a in
/-- Actual KQ trivial cofibrations become trivial Thomason cofibrations. -/
theorem left_preserves_trivialCofibrations {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f]
    (hf : realizationWeakEquivalences f) :
    ((J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓
      realizationWeakEquivalences.inverseImage N).llp ⊓
        realizationWeakEquivalences.inverseImage N) (L.map f) := by
  have := kq.fibrationFactorization
  have hl : (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex)).llp (L.map f) := by
    intro A B p hp
    apply (adj.hasLiftingProperty_iff f p).mpr
    exact MorphismProperty.hasLiftingProperty_of_wfs
      (W₁ := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences)
      (W₂ := J.rlp) f _ ⟨by infer_instance, hf⟩ hp
  have := a.fibrationFactorization
  exact (congrArg (fun P : MorphismProperty C => P (L.map f))
    (MorphismProperty.llp_eq_of_wfs
      ((J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex) ⊓
        realizationWeakEquivalences.inverseImage N).llp ⊓
          realizationWeakEquivalences.inverseImage N)
      (J.rlp.inverseImage (N ⋙ SSet.ex ⋙ SSet.ex)))).mp hl

include adj kq a in
/-- Brown's factorization upgrades trivial-cofibration preservation to
preservation of every actual simplicial realization weak equivalence. -/
theorem left_preserves_weakEquivalences {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (N.map (L.map f)) := by
  let : ModelCategory SSet.{0} := kq.model
  let : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have (Z : SSet.{0}) : IsCofibrant Z :=
    SSet.modelCategoryQuillen.cofibration_of_mono (initial.to Z)
  let b : CofibrantBrownFactorization f := Classical.choice inferInstance
  have hi : realizationWeakEquivalences b.i :=
    (weakEquivalence_iff b.i).mp inferInstance
  have hs : realizationWeakEquivalences b.s :=
    (weakEquivalence_iff b.s).mp inferInstance
  have hLi := (left_preserves_trivialCofibrations adj kq a b.i hi).2
  have hLs := (left_preserves_trivialCofibrations adj kq a b.s hs).2
  have := kq.twoOutOfThree
  have hLp : realizationWeakEquivalences (N.map (L.map b.p)) := by
    apply realizationWeakEquivalences.of_precomp (N.map (L.map b.s)) _ hLs
    rw [← N.map_comp, ← L.map_comp, b.s_p, L.map_id, N.map_id]
    exact realizationWeakEquivalences.id_mem _
  rw [← b.fac, L.map_comp, N.map_comp]
  exact realizationWeakEquivalences.comp_mem _ _ hLi hLp

end ThomasonAdjunction
end Thomason.Construction

end

end OAI
