import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

namespace OAI

section

/-! # Boundary lifting constructs actual simplicial deformation data

No weak-equivalence assertion is used in the construction. It uses only the
proved generation of monomorphisms by boundaries and two concrete lifts.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

/-- A section and an actual simplicial homotopy to its other composite. -/
structure BoundaryRetraction {X Y : SSet.{u}} (f : X ⟶ Y) where
  section_ : Y ⟶ X
  section_comp : section_ ≫ f = 𝟙 Y
  homotopy : SSet.Homotopy (f ≫ section_) (𝟙 X)

/-- Every map lifting against boundaries admits explicit simplicial
retraction data. -/
noncomputable def boundaryRetraction {X Y : SSet.{u}} (f : X ⟶ Y) (hf : I.rlp f) :
    BoundaryRetraction f := by
  have hp : (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp f := by
    rwa [SSet.rlp_monomorphisms]
  let b : (⊥ : Y.Subcomplex).toSSet ⟶ X := SSet.Subcomplex.isInitialBot.to X
  let bY := (⊥ : Y.Subcomplex).ι
  letI : HasLiftingProperty bY f := hp bY (by infer_instance)
  let sq₀ : CommSq b bY f (𝟙 Y) := ⟨SSet.Subcomplex.isInitialBot.hom_ext _ _⟩
  let s := sq₀.lift
  have hs : s ≫ f = 𝟙 Y := sq₀.fac_right
  have hs' : (f ≫ s) ≫ f = f := by rw [Category.assoc, hs, Category.comp_id]
  let j := SimplicialCylinder.inclusion X
  letI : HasLiftingProperty j f := hp j (by infer_instance)
  let sq : CommSq (SimplicialCylinder.desc (f ≫ s) (𝟙 X)) j f
      (fst X Δ[1] ≫ f) := ⟨by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (congr_app hs' m) x
    | inr x => rfl⟩
  refine ⟨s, hs, { h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · rw [← SimplicialCylinder.zero_inclusion X, Category.assoc, sq.fac_left,
      SimplicialCylinder.zero_desc]
    rfl
  · rw [← SimplicialCylinder.one_inclusion X, Category.assoc, sq.fac_left,
      SimplicialCylinder.one_desc]
    rfl
  · apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end Thomason.Construction

end

section

/-! # A cylinder boundary with two arbitrary endpoint maps -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

noncomputable section

/-- Assemble two maps on the two components of an interval boundary. -/
def intervalBoundaryFamily {K X : SSet.{u}} (f₀ f₁ : K ⟶ X) :
    K ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ X where
  app m := ↾fun z => if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0 then
    f₀.app m z.1 else f₁.app m z.1
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro z
    have ht : (SSet.stdSimplex.objEquiv
        (((SSet.boundary 1 : SSet.{u}).map f) z.2).val).toOrderHom 0 =
        (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 :=
      interval_boundary_constant z.2 (f.unop.toOrderHom 0)
    change (if (SSet.stdSimplex.objEquiv
        (((SSet.boundary 1 : SSet.{u}).map f) z.2).val).toOrderHom 0 = 0 then
      f₀.app n (K.map f z.1) else f₁.app n (K.map f z.1)) =
      X.map f (if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0 then
        f₀.app m z.1 else f₁.app m z.1)
    rw [ht]
    split_ifs
    · exact NatTrans.naturality_apply f₀ f z.1
    · exact NatTrans.naturality_apply f₁ f z.1

theorem intervalBoundaryFamily_zero {K X : SSet.{u}} (f₀ f₁ : K ⟶ X) :
    K ◁ SSet.boundary.ι (1 : Fin 2) ≫ intervalBoundaryFamily f₀ f₁ =
      fst K (Δ[0] : SSet.{u}) ≫ f₀ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  have hz : (SSet.stdSimplex.objEquiv z.2).toOrderHom 0 = 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  change (if (SimplexCategory.δ (1 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv z.2).toOrderHom 0) = 0 then
        f₀.app m z.1 else f₁.app m z.1) = f₀.app m z.1
  rw [hz]
  rfl

theorem intervalBoundaryFamily_one {K X : SSet.{u}} (f₀ f₁ : K ⟶ X) :
    K ◁ SSet.boundary.ι (0 : Fin 2) ≫ intervalBoundaryFamily f₀ f₁ =
      fst K (Δ[0] : SSet.{u}) ≫ f₁ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  have hz : (SSet.stdSimplex.objEquiv z.2).toOrderHom 0 = 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  change (if (SimplexCategory.δ (0 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv z.2).toOrderHom 0) = 0 then
        f₀.app m z.1 else f₁.app m z.1) = f₁.app m z.1
  rw [hz]
  rfl

theorem intervalBoundaryFamily_naturality {A K X : SSet.{u}}
    (i : A ⟶ K) (f₀ f₁ : K ⟶ X) :
    i ▷ (SSet.boundary 1 : SSet.{u}) ≫ intervalBoundaryFamily f₀ f₁ =
      intervalBoundaryFamily (i ≫ f₀) (i ≫ f₁) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  rfl

theorem intervalBoundaryFamily_restriction {K X : SSet.{u}} (a : K ⊗ Δ[1] ⟶ X) :
    K ◁ (SSet.boundary 1).ι ≫ a =
      intervalBoundaryFamily (SSet.ι₀ ≫ a) (SSet.ι₁ ≫ a) := by
  apply interval_boundary_tensor_hom_ext
  · rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_zero_face, Category.assoc, intervalBoundaryFamily_zero]
  · rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_one_face, Category.assoc, intervalBoundaryFamily_one]

theorem intervalBoundaryFamily_endpoints {K X : SSet.{u}} (e : K ⊗ Δ[1] ⟶ X)
    (f₀ f₁ : K ⟶ X)
    (h : K ◁ (SSet.boundary 1).ι ≫ e = intervalBoundaryFamily f₀ f₁) :
    SSet.ι₀ ≫ e = f₀ ∧ SSet.ι₁ ≫ e = f₁ := by
  constructor
  · have hh := congrArg (fun f => zeroFaceSection K ≫ K ◁ SSet.boundary.ι (1 : Fin 2) ≫ f) h
    rw [intervalBoundaryFamily_zero] at hh
    simpa only [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_zero_face, zeroFaceSection_fst, Category.id_comp] using hh
  · have hh := congrArg (fun f => zeroFaceSection K ≫ K ◁ SSet.boundary.ι (0 : Fin 2) ≫ f) h
    rw [intervalBoundaryFamily_one] at hh
    simpa only [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_one_face, zeroFaceSection_fst, Category.id_comp] using hh

end

end Thomason.Construction

end

section

/-! # Right cancellation of anodyne extensions along monomorphisms

First extend the entire composite. The boundary-cylinder lifting theorem
then joins the two lifts over the middle object, and a relative cylinder
lift makes their restrictions agree exactly.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

theorem anodyne_right_cancellation {A B C : SSet.{0}} (a : A ⟶ B) (b : B ⟶ C)
    [Mono b] (ha : SSet.anodyneExtensions a) (hab : SSet.anodyneExtensions (a ≫ b)) :
    SSet.anodyneExtensions b := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {f g} sq => ?_⟩
  let : HasLiftingProperty (a ≫ b) p := hab p hp
  let s : CommSq (a ≫ f) (a ≫ b) p g := ⟨by
    rw [Category.assoc, sq.w, Category.assoc]⟩
  let hA : A ⊗ Δ[1] ⟶ E := fst A Δ[1] ≫ a ≫ f
  let cB := intervalBoundaryFamily f (b ≫ s.lift)
  let hB : B ⊗ Δ[1] ⟶ F := fst B Δ[1] ≫ b ≫ g
  have hA₀ : SSet.ι₀ ≫ hA = a ≫ f := by simp [hA]
  have hA₁ : SSet.ι₁ ≫ hA = a ≫ f := by simp [hA]
  have hc : a ▷ (SSet.boundary 1 : SSet.{0}) ≫ cB =
      A ◁ (SSet.boundary 1).ι ≫ hA := by
    dsimp only [cB]
    rw [intervalBoundaryFamily_naturality, intervalBoundaryFamily_restriction,
      hA₀, hA₁, ← Category.assoc, s.fac_left]
  have hpa : hA ≫ p = a ▷ Δ[1] ≫ hB := by
    simp [hA, hB, Category.assoc, sq.w]
  have hpc : cB ≫ p = B ◁ (SSet.boundary 1).ι ≫ hB := by
    apply interval_boundary_tensor_hom_ext
    · rw [← Category.assoc, intervalBoundaryFamily_zero, Category.assoc, sq.w]
      simp [hB]
    · rw [← Category.assoc, intervalBoundaryFamily_one]
      simp only [Category.assoc, s.fac_right]
      simp [hB]
  obtain ⟨H, _, hH, hHp⟩ := exists_kan_boundary_cylinder_lift a ha p hA cB hB hc hpa hpc
  obtain ⟨hH₀, hH₁⟩ := intervalBoundaryFamily_endpoints H f (b ≫ s.lift) hH
  have hbase : H ≫ p = b ▷ Δ[1] ≫ (fst C Δ[1] ≫ g) := by
    rw [hHp]
    simp [hB]
  have hs : s.lift ≫ p = SSet.ι₁ ≫ (fst C Δ[1] ≫ g) := by
    rw [s.fac_right]
    simp
  obtain ⟨K, _, hK, hKp⟩ := exists_kan_cylinder_lift_one b p s.lift H
    (fst C Δ[1] ≫ g) hH₁ hbase hs
  refine ⟨⟨{ l := SSet.ι₀ ≫ K, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hK, hH₀]
  · rw [Category.assoc, hKp]
    simp

end

end Thomason.Construction

end

section

/-! # Finite unions of compatible anodyne subcomplex extensions

This is the finite gluing step for extended faces. Intersections remain
in the same family, so their known anodyne inclusions suffice; no anodyne
property is assumed for the union itself.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem anodyne_subcomplex_congr {X : SSet.{0}} {A B C D : X.Subcomplex}
    (hA : A = C) (hB : B = D) (hAB : A ≤ B) (hCD : C ≤ D) :
    SSet.anodyneExtensions (SSet.Subcomplex.homOfLE hAB) ↔
      SSet.anodyneExtensions (SSet.Subcomplex.homOfLE hCD) := by
  subst C
  subst D
  rfl

private theorem finite_anodyne_union_aux {X : SSet.{0}} (n : ℕ) :
    ∀ (F : Finset X.Subcomplex), F.card = n →
      ∀ (C : Set X.Subcomplex) (J : X.Subcomplex),
        (∀ A ∈ C, ∀ B ∈ C, A ⊓ B ∈ C) →
        (∀ A ∈ C, SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show J ⊓ A ≤ A from inf_le_right))) →
        (∀ A ∈ F, A ∈ C) →
        SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show J ≤ J ⊔ F.sup id from le_sup_left)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hF C J hC hJ hFC
    rcases F.eq_empty_or_nonempty with rfl | hne
    · apply (anodyne_subcomplex_congr rfl (by simp) _ (le_refl J)).mpr
      exact SSet.anodyneExtensions.of_isIso (𝟙 J.toSSet)
    · obtain ⟨B, hB⟩ := hne
      let G := F.erase B
      have hG : G.card < n := by
        rw [← hF]
        exact Finset.card_erase_lt_of_mem hB
      have hGC : ∀ A ∈ G, A ∈ C := fun A hA => hFC A (Finset.mem_of_mem_erase hA)
      have hBC := hFC B hB
      let U := J ⊔ G.sup id
      have hJU : SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show J ≤ U from le_sup_left)) := ih G.card hG G rfl C J hC hJ hGC
      let H := G.image (fun A => A ⊓ B)
      let D : Set X.Subcomplex := {A | A ∈ C ∧ A ≤ B}
      have hH : H.card < n := lt_of_le_of_lt (Finset.card_image_le) hG
      have hD : ∀ A ∈ D, ∀ A' ∈ D, A ⊓ A' ∈ D := by
        intro A hA A' hA'
        exact ⟨hC A hA.1 A' hA'.1, inf_le_left.trans hA.2⟩
      have hJD : ∀ A ∈ D, SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show (J ⊓ B) ⊓ A ≤ A from inf_le_right)) := by
        intro A hA
        have he : (J ⊓ B) ⊓ A = J ⊓ A := by
          rw [inf_assoc, inf_eq_right.mpr hA.2]
        exact (anodyne_subcomplex_congr he rfl _ _).mpr (hJ A hA.1)
      have hHD : ∀ A ∈ H, A ∈ D := by
        intro A hA
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        exact ⟨hC A' (hGC A' hA') B hBC, inf_le_right⟩
      have hJI := ih H.card hH H rfl D (J ⊓ B) hD hJD hHD
      have hinter : (J ⊓ B) ⊔ H.sup id = U ⊓ B := by
        have h₁ : (J ⊔ G.sup id) ⊓ B = (J ⊓ B) ⊔ ((G.sup id) ⊓ B) :=
          by ext d x; exact or_and_right
        have h₂ : (G.sup id) ⊓ B = G.sup (fun A => A ⊓ B) := by
          induction G using Finset.induction_on with
          | empty => simp
          | @insert A G hAG ihG =>
            rw [Finset.sup_insert, Finset.sup_insert, ← ihG]
            ext d x
            exact or_and_right
        calc
          _ = (J ⊓ B) ⊔ G.sup (fun A => A ⊓ B) := by
            dsimp only [H]
            rw [Finset.sup_image]
            rfl
          _ = (J ⊓ B) ⊔ ((G.sup id) ⊓ B) := congrArg ((J ⊓ B) ⊔ ·) h₂.symm
          _ = _ := h₁.symm
      have hJI' : SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show J ⊓ B ≤ U ⊓ B from inf_le_inf le_sup_left le_rfl)) := by
        exact (anodyne_subcomplex_congr rfl hinter _ _).mp hJI
      have hIB : SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show U ⊓ B ≤ B from inf_le_right)) := by
        apply anodyne_right_cancellation (SSet.Subcomplex.homOfLE
          (show J ⊓ B ≤ U ⊓ B from inf_le_inf le_sup_left le_rfl))
          (SSet.Subcomplex.homOfLE (show U ⊓ B ≤ B from inf_le_right)) hJI'
        simpa only [SSet.Subcomplex.homOfLE_comp] using hJ B hBC
      have hs : SSet.Subcomplex.BicartSq (U ⊓ B) U B (U ⊔ B) := ⟨rfl, rfl⟩
      have hUU : SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show U ≤ U ⊔ B from le_sup_left)) :=
        SSet.anodyneExtensions.of_isPushout hs.isPushout hIB
      have hall := SSet.anodyneExtensions.comp_mem _ _ hJU hUU
      have htarget : U ⊔ B = J ⊔ F.sup id := by
        rw [show F = insert B G from (Finset.insert_erase hB).symm,
          Finset.sup_insert]
        dsimp only [U]
        rw [sup_assoc, sup_comm (G.sup id) B]
        rfl
      have hall' : SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
          (show J ≤ U ⊔ B from le_sup_left.trans le_sup_left)) := by
        simpa only [SSet.Subcomplex.homOfLE_comp] using hall
      exact (anodyne_subcomplex_congr rfl htarget _ _).mp hall'

/-- A finite family closed under intersections glues relative anodyne
inclusions into an anodyne inclusion of its union. -/
theorem finite_anodyne_union {X : SSet.{0}} (F : Finset X.Subcomplex)
    (C : Set X.Subcomplex) (J : X.Subcomplex)
    (hC : ∀ A ∈ C, ∀ B ∈ C, A ⊓ B ∈ C)
    (hJ : ∀ A ∈ C, SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show J ⊓ A ≤ A from inf_le_right)))
    (hFC : ∀ A ∈ F, A ∈ C) :
    SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show J ≤ J ⊔ F.sup id from le_sup_left)) :=
  finite_anodyne_union_aux F.card F rfl C J hC hJ hFC

end

end Thomason.Construction

end

section

/-! # Homotopies of pairs and anodyne inclusions

The relative cylinder lifting property allows a lifting problem to be
transported along a compatible homotopy of its domain pair. This uses the
proved horn pushout-product theorem, with no weak-equivalence characterization.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

/-- Compatible homotopies from a pair map through an anodyne arrow to the
identity transport every exact Kan lifting problem. No retraction identities
for the intervening pair maps are needed. -/
theorem anodyne_of_arrow_homotopies {A B C D : SSet.{0}}
    (i : A ⟶ B) [Mono i] (j : C ⟶ D) (hj : SSet.anodyneExtensions j)
    (rA : A ⟶ C) (rB : B ⟶ D) (sA : C ⟶ A) (sB : D ⟶ B)
    (hr : i ≫ rB = rA ≫ j) (hs : j ≫ sB = sA ≫ i)
    (HA : SSet.Homotopy (rA ≫ sA) (𝟙 A))
    (HB : SSet.Homotopy (rB ≫ sB) (𝟙 B))
    (hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i) : SSet.anodyneExtensions i := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let : HasLiftingProperty j p := hj p hp
  let sq' : CommSq (sA ≫ a) j p (sB ≫ b) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hs, Category.assoc]⟩
  let f := rB ≫ sq'.lift
  have hi : i ≫ f = (rA ≫ sA) ≫ a := by
    dsimp [f]
    rw [← Category.assoc, hr, Category.assoc, sq'.fac_left, ← Category.assoc]
  have h₀ : SSet.ι₀ ≫ (HA.h ≫ a) = i ≫ f := by
    rw [← Category.assoc, HA.h₀, hi]
  have hb : (HA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (HB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hH, Category.assoc]
  have hf : f ≫ p = SSet.ι₀ ≫ (HB.h ≫ b) := by
    dsimp [f]
    rw [Category.assoc, sq'.fac_right]
    simpa only [Category.assoc] using
      congrArg (fun q : B ⟶ B => q ≫ b) HB.h₀.symm
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift i p f (HA.h ≫ a)
    (HB.h ≫ b) h₀ hb hf
  refine ⟨⟨{ l := SSet.ι₁ ≫ e, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hei,
      ← Category.assoc, HA.h₁, Category.id_comp]
  · rw [Category.assoc, hep, ← Category.assoc, HB.h₁, Category.id_comp]

/-- The same transport works for compatible homotopies with the opposite
orientation, using the final-endpoint cylinder lifting property. -/
theorem anodyne_of_arrow_homotopies_reverse {A B C D : SSet.{0}}
    (i : A ⟶ B) [Mono i] (j : C ⟶ D) (hj : SSet.anodyneExtensions j)
    (rA : A ⟶ C) (rB : B ⟶ D) (sA : C ⟶ A) (sB : D ⟶ B)
    (hr : i ≫ rB = rA ≫ j) (hs : j ≫ sB = sA ≫ i)
    (HA : SSet.Homotopy (𝟙 A) (rA ≫ sA))
    (HB : SSet.Homotopy (𝟙 B) (rB ≫ sB))
    (hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i) : SSet.anodyneExtensions i := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let : HasLiftingProperty j p := hj p hp
  let sq' : CommSq (sA ≫ a) j p (sB ≫ b) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hs, Category.assoc]⟩
  let f := rB ≫ sq'.lift
  have hi : i ≫ f = (rA ≫ sA) ≫ a := by
    dsimp [f]
    rw [← Category.assoc, hr, Category.assoc, sq'.fac_left, ← Category.assoc]
  have h₁ : SSet.ι₁ ≫ (HA.h ≫ a) = i ≫ f := by
    rw [← Category.assoc, HA.h₁, hi]
  have hb : (HA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (HB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hH, Category.assoc]
  have hf : f ≫ p = SSet.ι₁ ≫ (HB.h ≫ b) := by
    dsimp [f]
    rw [Category.assoc, sq'.fac_right]
    simpa only [Category.assoc] using
      congrArg (fun q : B ⟶ B => q ≫ b) HB.h₁.symm
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift_one i p f (HA.h ≫ a)
    (HB.h ≫ b) h₁ hb hf
  refine ⟨⟨{ l := SSet.ι₀ ≫ e, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hei,
      ← Category.assoc, HA.h₀, Category.id_comp]
  · rw [Category.assoc, hep, ← Category.assoc, HB.h₀, Category.id_comp]

/-- A two-step compatible zigzag of homotopies of pairs also transports
anodyne lifting. This is the shape of the elementary face-poset collapse. -/
theorem anodyne_of_arrow_homotopy_zigzag {A B C D : SSet.{0}}
    (i : A ⟶ B) [Mono i] (j : C ⟶ D) (hj : SSet.anodyneExtensions j)
    (rA : A ⟶ C) (rB : B ⟶ D) (sA : C ⟶ A) (sB : D ⟶ B)
    (hr : i ≫ rB = rA ≫ j) (hs : j ≫ sB = sA ≫ i)
    (uA : A ⟶ A) (uB : B ⟶ B)
    (HA : SSet.Homotopy (rA ≫ sA) uA) (HB : SSet.Homotopy (rB ≫ sB) uB)
    (hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i)
    (GA : SSet.Homotopy (𝟙 A) uA) (GB : SSet.Homotopy (𝟙 B) uB)
    (hG : i ▷ Δ[1] ≫ GB.h = GA.h ≫ i) : SSet.anodyneExtensions i := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let : HasLiftingProperty j p := hj p hp
  let sq' : CommSq (sA ≫ a) j p (sB ≫ b) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hs, Category.assoc]⟩
  let f := rB ≫ sq'.lift
  have hi : i ≫ f = (rA ≫ sA) ≫ a := by
    dsimp [f]
    rw [← Category.assoc, hr, Category.assoc, sq'.fac_left, ← Category.assoc]
  have h₀ : SSet.ι₀ ≫ (HA.h ≫ a) = i ≫ f := by
    rw [← Category.assoc, HA.h₀, hi]
  have hb : (HA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (HB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hH, Category.assoc]
  have hf : f ≫ p = SSet.ι₀ ≫ (HB.h ≫ b) := by
    dsimp [f]
    rw [Category.assoc, sq'.fac_right]
    simpa only [Category.assoc] using
      congrArg (fun q : B ⟶ B => q ≫ b) HB.h₀.symm
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift i p f (HA.h ≫ a)
    (HB.h ≫ b) h₀ hb hf
  let g := SSet.ι₁ ≫ e
  have hgi : i ≫ g = uA ≫ a := by
    dsimp [g]
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hei,
      ← Category.assoc, HA.h₁]
  have hgp : g ≫ p = uB ≫ b := by
    dsimp [g]
    rw [Category.assoc, hep, ← Category.assoc, HB.h₁]
  have g₁ : SSet.ι₁ ≫ (GA.h ≫ a) = i ≫ g := by
    rw [← Category.assoc, GA.h₁, hgi]
  have gb : (GA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (GB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hG, Category.assoc]
  have gf : g ≫ p = SSet.ι₁ ≫ (GB.h ≫ b) := by
    rw [hgp, ← Category.assoc, GB.h₁]
  obtain ⟨e', _, hei', hep'⟩ := exists_kan_cylinder_lift_one i p g (GA.h ≫ a)
    (GB.h ≫ b) g₁ gb gf
  refine ⟨⟨{ l := SSet.ι₀ ≫ e', fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hei',
      ← Category.assoc, GA.h₀, Category.id_comp]
  · rw [Category.assoc, hep', ← Category.assoc, GB.h₀, Category.id_comp]

end

end Thomason.Construction

end

section

/-! # Transport of Kan lifting along a cospan of homotopies of pairs -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

noncomputable section

/-- The reversed orientation of the two-step pair homotopy also transports
anodyne lifting. This is the orientation of the explicit horn contraction. -/
theorem anodyne_of_arrow_homotopy_cospan {A B C D : SSet.{0}}
    (i : A ⟶ B) [Mono i] (j : C ⟶ D) (hj : SSet.anodyneExtensions j)
    (rA : A ⟶ C) (rB : B ⟶ D) (sA : C ⟶ A) (sB : D ⟶ B)
    (hr : i ≫ rB = rA ≫ j) (hs : j ≫ sB = sA ≫ i)
    (uA : A ⟶ A) (uB : B ⟶ B)
    (HA : SSet.Homotopy uA (rA ≫ sA)) (HB : SSet.Homotopy uB (rB ≫ sB))
    (hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i)
    (GA : SSet.Homotopy uA (𝟙 A)) (GB : SSet.Homotopy uB (𝟙 B))
    (hG : i ▷ Δ[1] ≫ GB.h = GA.h ≫ i) : SSet.anodyneExtensions i := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let : HasLiftingProperty j p := hj p hp
  let sq' : CommSq (sA ≫ a) j p (sB ≫ b) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hs, Category.assoc]⟩
  let f := rB ≫ sq'.lift
  have hi : i ≫ f = (rA ≫ sA) ≫ a := by
    dsimp [f]
    rw [← Category.assoc, hr, Category.assoc, sq'.fac_left, ← Category.assoc]
  have h₁ : SSet.ι₁ ≫ (HA.h ≫ a) = i ≫ f := by
    rw [← Category.assoc, HA.h₁, hi]
  have hb : (HA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (HB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hH, Category.assoc]
  have hf : f ≫ p = SSet.ι₁ ≫ (HB.h ≫ b) := by
    dsimp [f]
    rw [Category.assoc, sq'.fac_right]
    simpa only [Category.assoc] using
      congrArg (fun q : B ⟶ B => q ≫ b) HB.h₁.symm
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift_one i p f (HA.h ≫ a)
    (HB.h ≫ b) h₁ hb hf
  let g := SSet.ι₀ ≫ e
  have hgi : i ≫ g = uA ≫ a := by
    dsimp [g]
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hei,
      ← Category.assoc, HA.h₀]
  have hgp : g ≫ p = uB ≫ b := by
    dsimp [g]
    rw [Category.assoc, hep, ← Category.assoc, HB.h₀]
  have g₀ : SSet.ι₀ ≫ (GA.h ≫ a) = i ≫ g := by
    rw [← Category.assoc, GA.h₀, hgi]
  have gb : (GA.h ≫ a) ≫ p = i ▷ Δ[1] ≫ (GB.h ≫ b) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← hG, Category.assoc]
  have gf : g ≫ p = SSet.ι₀ ≫ (GB.h ≫ b) := by
    rw [hgp, ← Category.assoc, GB.h₀]
  obtain ⟨e', _, hei', hep'⟩ := exists_kan_cylinder_lift i p g (GA.h ≫ a)
    (GB.h ≫ b) g₀ gb gf
  refine ⟨⟨{ l := SSet.ι₁ ≫ e', fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hei',
      ← Category.assoc, GA.h₁, Category.id_comp]
  · rw [Category.assoc, hep', ← Category.assoc, GB.h₁, Category.id_comp]

end

end Thomason.Construction

end

section

/-! # Kan lifting of cylinders with both endpoints fixed -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

noncomputable section

theorem intervalBoundary_endpoints {K X : SSet.{u}} (e : K ⊗ Δ[1] ⟶ X)
    (x₀ x₁ : X _⦋0⦌)
    (h : K ◁ (SSet.boundary 1).ι ≫ e =
      snd K (SSet.boundary 1 : SSet.{u}) ≫ intervalBoundaryMap x₀ x₁) :
    SSet.ι₀ ≫ e = SSet.const x₀ ∧ SSet.ι₁ ≫ e = SSet.const x₁ := by
  constructor
  · have hh := congrArg (fun f => zeroFaceSection K ≫ K ◁ SSet.boundary.ι (1 : Fin 2) ≫ f) h
    simp only [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_zero_face, zeroFaceSection_fst, Category.id_comp] at hh
    simpa only [Category.assoc, whiskerLeft_snd_assoc, intervalBoundaryMap_zero,
      SSet.comp_const] using hh
  · have hh := congrArg (fun f => zeroFaceSection K ≫ K ◁ SSet.boundary.ι (0 : Fin 2) ≫ f) h
    simp only [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_one_face, zeroFaceSection_fst, Category.id_comp] at hh
    simpa only [Category.assoc, whiskerLeft_snd_assoc, intervalBoundaryMap_one,
      SSet.comp_const] using hh

/-- An anodyne parameter extension lifts a cylinder over a Kan fibration
while preserving two specified constant endpoints exactly. -/
theorem exists_kan_fixed_endpoint_lift {A K E B : SSet.{u}}
    (i : A ⟶ K) (hi : SSet.anodyneExtensions i)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (x₀ x₁ : E _⦋0⦌) (a : A ⊗ Δ[1] ⟶ E) (b : K ⊗ Δ[1] ⟶ B)
    (ha₀ : SSet.ι₀ ≫ a = SSet.const x₀) (ha₁ : SSet.ι₁ ≫ a = SSet.const x₁)
    (hb₀ : SSet.ι₀ ≫ b = SSet.const (p.app _ x₀))
    (hb₁ : SSet.ι₁ ≫ b = SSet.const (p.app _ x₁))
    (hab : a ≫ p = i ▷ Δ[1] ≫ b) :
    ∃ e : K ⊗ Δ[1] ⟶ E, i ▷ Δ[1] ≫ e = a ∧ e ≫ p = b ∧
      SSet.ι₀ ≫ e = SSet.const x₀ ∧ SSet.ι₁ ≫ e = SSet.const x₁ := by
  let c := snd K (SSet.boundary 1 : SSet.{u}) ≫ intervalBoundaryMap x₀ x₁
  have hc : i ▷ (SSet.boundary 1 : SSet.{u}) ≫ c = A ◁ (SSet.boundary 1).ι ≫ a := by
    dsimp only [c]
    rw [← Category.assoc, whiskerRight_snd,
      intervalBoundary_restriction a x₀ x₁ ha₀ ha₁]
  have hb : c ≫ p = K ◁ (SSet.boundary 1).ι ≫ b := by
    dsimp only [c]
    rw [Category.assoc, intervalBoundaryMap_postcomp,
      intervalBoundary_restriction b _ _ hb₀ hb₁]
  obtain ⟨e, hei, heb, hep⟩ := exists_kan_boundary_cylinder_lift i hi p a c b hc hab hb
  obtain ⟨he₀, he₁⟩ := intervalBoundary_endpoints e x₀ x₁ heb
  exact ⟨e, hei, hep, he₀, he₁⟩

end

end Thomason.Construction

end

section

/-! # Composition generation of the actual orientals

The finite ordered splitting lowers the degree of agreement with a single
atom. At degree zero the positive residual has augmentation zero. This
discharges the precise simplex-generation consequence of Steiner's theorem.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- The upper table is zero or agrees with one higher-dimensional atom. -/
def AboveAtomOrZero (h : NormalizedSimplexIdentities) {m : ℕ}
    (r : ℕ) (X : h.object m) : Prop :=
  (∀ n, r < n → ∀ side, X.table side n = 0) ∨
  ∃ a : AtomIndex m, r < a.1 ∧
    ∀ n, r < n → ∀ side, X.table side n = (atomCell h a).table side n

/-- A cell with no positive-dimensional chains is the corresponding vertex atom. -/
theorem eq_vertex_atom_of_above_zero (h : NormalizedSimplexIdentities) {m : ℕ}
    (X : h.object m) (hz : ∀ n, 0 < n → ∀ side, X.table side n = 0) :
    ∃ b : Basis m 0, X = basisAtom h b := by
  obtain ⟨i, hi⟩ := positive_augmentation_one (X.table false 0)
    (X.positive false 0) (X.augmentation false)
  have he : X.table true 0 = X.table false 0 := by
    have hb := X.boundary false 0
    rw [hz 1 (by omega) false, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  have hv : IsBasisAtom h (vertexBasis i) X := by
    refine ⟨?_, ?_, ?_⟩
    · intro side
      cases side
      · exact hi
      · exact he.trans hi
    · intro side n hn
      omega
    · intro side n hn
      exact hz n hn side
  exact ⟨vertexBasis i, hv.unique h (basisAtom_isBasisAtom h _)⟩

/-- Lowering one degree expresses the upper table as a finite sum of atoms. -/
theorem upper_atom_decomposition (h : NormalizedSimplexIdentities) {m : ℕ}
    (r : ℕ) (X : h.object m) (hx : AboveAtomOrZero h (r+1) X) :
    ∃ as : List (AtomIndex m),
      (∀ a ∈ as, r < a.1) ∧
      ∀ n, r < n → ∀ side, X.table side n =
        (Cell.PositiveTable.ofCells (as.map (atomCell h))).table side n := by
  rcases hx with hz | ⟨a, ha, he⟩
  · let z : Chains m (r+1) := X.table false (r+1)
    refine ⟨chainAtomIndices z, ?_, ?_⟩
    · intro a ha
      rw [chainAtomIndices_degree z a ha]
      omega
    · intro n hn side
      by_cases heq : n = r+1
      · subst n
        rw [chainAtomIndices_table h z (X.positive false (r+1)) side]
        cases side
        · rfl
        · have hb := X.boundary false (r+1)
          rw [hz (r+1+1) (by omega) false, map_zero] at hb
          exact sub_eq_zero.mp hb.symm
      · have hnr : r+1 < n := by omega
        rw [hz n hnr side, chainAtomIndices_above h z n hnr side]
  · let A := atomCell h a
    let z : Chains m (r+1) := X.table false (r+1) - A.table false (r+1)
    have hz : z ∈ positive m (r+1) := atom_residual_positive X A
      (atomCell_isBasisAtom h a) (r+1) ha (he (r+1+1) (by omega) false)
    refine ⟨a :: chainAtomIndices z, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · rw [chainAtomIndices_degree z b hb]
        omega
    · intro n hn side
      change X.table side n = A.table side n +
        (Cell.PositiveTable.ofCells ((chainAtomIndices z).map (atomCell h))).table side n
      by_cases heq : n = r+1
      · subst n
        rw [chainAtomIndices_table h z hz side]
        have hs := atom_residual_sides X A (r+1) (he (r+1+1) (by omega) false)
        cases side
        · dsimp [z]
          abel
        · change X.table true (r+1) = A.table true (r+1) +
            (X.table false (r+1) - A.table false (r+1))
          rw [hs]
          abel
      · have hnr : r+1 < n := by omega
        rw [chainAtomIndices_above h z n hnr side, add_zero]
        exact he n hnr side

/-- Sorting an upper atom sum supplies actual iterated strict composites. -/
theorem predicate_of_upper_atom_sum (h : NormalizedSimplexIdentities) {m : ℕ}
    (r : ℕ) (P : h.object m → Prop)
    (hbase : ∀ X, AboveAtomOrZero h r X → P X)
    (hcomp : ∀ n x y hxy, P x → P y → P ((h.object m).comp n x y hxy))
    (as : List (AtomIndex m)) (hd : ∀ a ∈ as, r < a.1)
    (X : h.object m)
    (he : ∀ n, r < n → ∀ side, X.table side n =
      (Cell.PositiveTable.ofCells (as.map (atomCell h))).table side n) : P X := by
  have hd' : ∀ a ∈ sortAtoms as, r < a.1 := fun a ha =>
    hd a ((sortAtoms_perm as).mem_iff.mp ha)
  have hsep : ((sortAtoms as).map (atomCell h)).Pairwise (fun A B =>
      ∀ b : Basis m r, A.table false r b = 0 ∨ B.table true r b = 0) := by
    rw [List.pairwise_map]
    apply (sortAtoms_pairwise as).imp_of_mem
    intro a b ha hb hab c
    exact ordered_basisAtoms_disjoint (atomCell_isBasisAtom h a)
      (atomCell_isBasisAtom h b) (hd' a ha) (hd' b hb) hab c
  apply ordered_sum_induction h r P (fun Y hY => hbase Y (Or.inl hY))
    (hcomp r) ((sortAtoms as).map (atomCell h)) hsep
  · intro A hA Y hY
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
    exact hbase Y (Or.inr ⟨a, hd' a ha, hY⟩)
  · intro n hn side
    exact (he n hn side).trans (sortAtoms_table h as side n).symm

/-- Every composition-closed predicate containing the constructed atoms
contains every cell of the concrete oriental. -/
theorem generated_by_basisAtoms (h : NormalizedSimplexIdentities) (m : ℕ)
    (P : h.object m → Prop)
    (hatom : ∀ p (b : Basis m p), P (basisAtom h b))
    (hcomp : ∀ n x y hxy, P x → P y → P ((h.object m).comp n x y hxy)) :
    ∀ X, P X := by
  have hlevel : ∀ r (X : h.object m), AboveAtomOrZero h r X → P X := by
    intro r
    induction r with
    | zero =>
      intro X hx
      rcases hx with hz | ⟨a, ha, he⟩
      · obtain ⟨b, rfl⟩ := eq_vertex_atom_of_above_zero h X hz
        exact hatom 0 b
      · have heq := eq_atom_of_above_zero X (atomCell h a)
          (atomCell_isBasisAtom h a) ha he
        rw [heq]
        exact hatom a.1 a.2
    | succ r ih =>
      intro X hx
      obtain ⟨as, hd, he⟩ := upper_atom_decomposition h r X hx
      exact predicate_of_upper_atom_sum h r P ih hcomp as hd X he
  intro X
  apply hlevel m X
  exact Or.inl (fun n hn side => NormalizedSimplexIdentities.chains_eq_zero_above hn _)

end SimplexComplex

/-- Normalized simplex complexes satisfy the basis-atom generation
property. -/
theorem simplexGenerationInput (h : NormalizedSimplexIdentities) :
    PublishedSimplexGenerationInput h where
  generated m P hatom hcomp := SimplexComplex.generated_by_basisAtoms h m P hatom hcomp

/-- All atom data, including generation, are constructed from normalized
simplex identities. -/
noncomputable def simplexAtoms (h : NormalizedSimplexIdentities) : SimplexAtomsInput h :=
  (simplexGenerationInput h).toSimplexAtomsInput

end Thomason.Construction

end

section

/-! # Strict functors from orientals are determined by their atom images -/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory

/-- Atom generation detects equality of strict functors into any strict
omega-category, including the naturality squares for the Gray comparison. -/
theorem hom_ext_atoms (h : NormalizedSimplexIdentities) {m : ℕ}
    {D : StrictOmegaCategory} (F G : h.object m ⟶ D)
    (he : ∀ p (b : Basis m p), F.toFun (basisAtom h b) = G.toFun (basisAtom h b)) : F = G := by
  apply StrictOmegaCategory.Hom.ext
  funext X
  apply generated_by_basisAtoms h m (fun X => F.toFun X = G.toFun X) he
  intro n x y hxy hx hy
  have hf : D.target n (F.toFun x) = D.source n (F.toFun y) :=
    (F.map_face true n x).symm.trans
      ((congrArg F.toFun hxy).trans (F.map_face false n y))
  have hg : D.target n (G.toFun x) = D.source n (G.toFun y) :=
    (G.map_face true n x).symm.trans
      ((congrArg G.toFun hxy).trans (G.map_face false n y))
  rw [F.map_comp n x y hxy hf, G.map_comp n x y hxy hg]
  congr 1

end Thomason.Construction.SimplexComplex

end

section

/-! # Stationary simplicial deformations give anodyne inclusions -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A monomorphism with an actual simplicial retraction and stationary
simplicial deformation has the left lifting property against every Kan
fibration. No realization-to-simplicial approximation is assumed. -/
theorem anodyne_of_simplicial_deformation {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (H : SSet.Homotopy (r ≫ i) (𝟙 B))
    (hs : i ▷ Δ[1] ≫ H.h = fst A Δ[1] ≫ i) : SSet.anodyneExtensions i := by
  intro E F p hp
  have : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp
  refine ⟨fun {a b} sq => ?_⟩
  let f := r ≫ a
  let h := fst A Δ[1] ≫ a
  let c := H.h ≫ b
  have h₀ : SSet.ι₀ ≫ h = i ≫ f := by
    dsimp [h, f]
    rw [← Category.assoc i r, hir, Category.id_comp]
    simp
  have hb : h ≫ p = i ▷ Δ[1] ≫ c := by
    dsimp [h, c]
    rw [Category.assoc, sq.w, ← Category.assoc (i ▷ Δ[1]), hs, Category.assoc]
  have hf : f ≫ p = SSet.ι₀ ≫ c := by
    dsimp [f, c]
    rw [Category.assoc, sq.w, ← Category.assoc SSet.ι₀, H.h₀, Category.assoc]
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift i p f h c h₀ hb hf
  refine ⟨⟨{ l := SSet.ι₁ ≫ e, fac_left := ?_, fac_right := ?_ }⟩⟩
  · have hn : i ≫ SSet.ι₁ = SSet.ι₁ ≫ i ▷ Δ[1] := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, hei]
    dsimp [h]
    simp
  · rw [Category.assoc, hep]
    dsimp [c]
    rw [← Category.assoc, H.h₁, Category.id_comp]

end

end Thomason.Construction

end

section

/-! # The congruence for intelligent finite truncation

At the top surviving dimension identify the two faces of every higher
cell, and close these identifications under composition. Lower-dimensional
boundaries remain equal as actual cells; this is what allows the quotient
compositions to retain their original matching conditions.
-/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

open CategoryTheory

variable (C : StrictOmegaCategory.{0}) (n : ℕ)

def topFace (a : Bool) (x : C) : C.bounded n :=
  ⟨C.face a n x, C.face_dimensionLE a n x⟩

/-- The least composition congruence killing all cells above dimension n. -/
inductive Rel : C.bounded n → C.bounded n → Prop
  | refl (x) : Rel x x
  | symm {x y} : Rel x y → Rel y x
  | trans {x y z} : Rel x y → Rel y z → Rel x z
  | collapse (x : C) : Rel (topFace C n false x) (topFace C n true x)
  | compose (m : ℕ) (x y x' y' : C.bounded n)
      (h : (C.bounded n).target m x = (C.bounded n).source m y)
      (h' : (C.bounded n).target m x' = (C.bounded n).source m y') :
      Rel x x' → Rel y y' →
        Rel ((C.bounded n).comp m x y h) ((C.bounded n).comp m x' y' h')

variable {C n}

/-- The generating identifications never change a surviving lower face. -/
theorem Rel.lower_faces {x y : C.bounded n} (h : Rel C n x y)
    (a : Bool) (k : ℕ) (hk : k < n) : C.face a k x.val = C.face a k y.val := by
  induction h with
  | refl x => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | collapse z =>
    change C.face a k (C.face false n z) = C.face a k (C.face true n z)
    simp only [C.globular, hk, ite_true]
  | compose m x y x' y' hm hm' hx hy ihx ihy =>
    change C.face a k (C.comp m x.val y.val _) = C.face a k (C.comp m x'.val y'.val _)
    by_cases hkm : k ≤ m
    · rw [C.face_comp_le a hkm, C.face_comp_le a hkm]
      cases a
      · exact ihx
      · exact ihy
    · have hmk : m < k := by omega
      have hc : C.target m (C.face a k x.val) = C.source m (C.face a k y.val) := by
        simpa only [source, target, bounded, C.globular, hmk, ite_true] using congrArg Subtype.val hm
      have hc' : C.target m (C.face a k x'.val) = C.source m (C.face a k y'.val) := by
        simpa only [source, target, bounded, C.globular, hmk, ite_true] using congrArg Subtype.val hm'
      rw [C.face_comp a k m hmk _ _ _ hc, C.face_comp a k m hmk _ _ _ hc']
      congr 1

/-- Equivalence at the top dimension is equality on lower-dimensional cells. -/
theorem Rel.eq_of_dimensionLE {x y : C.bounded n} (h : Rel C n x y)
    {k : ℕ} (hk : k < n) (hx : C.DimensionLE k x.val) (hy : C.DimensionLE k y.val) :
    x = y := by
  apply Subtype.ext
  exact hx.1.symm.trans ((h.lower_faces false k hk).trans hy.1)

/-- Every strict functor into dimension n kills exactly the imposed generators. -/
theorem Rel.map_eq {D : StrictOmegaCategory.{0}} (hD : D.IsTruncated n) (f : C ⟶ D)
    {x y : C.bounded n} (h : Rel C n x y) : f.toFun x.val = f.toFun y.val := by
  induction h with
  | refl x => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | collapse z =>
    change f.toFun (C.face false n z) = f.toFun (C.face true n z)
    rw [f.map_face, f.map_face]
    exact (hD (f.toFun z)).1.trans (hD (f.toFun z)).2.symm
  | compose m x y x' y' hm hm' hx hy ihx ihy =>
    change f.toFun (C.comp m x.val y.val _) = f.toFun (C.comp m x'.val y'.val _)
    have hc : D.target m (f.toFun x.val) = D.source m (f.toFun y.val) :=
      (f.map_face true m x.val).symm.trans
        ((congrArg f.toFun (congrArg Subtype.val hm)).trans (f.map_face false m y.val))
    have hc' : D.target m (f.toFun x'.val) = D.source m (f.toFun y'.val) :=
      (f.map_face true m x'.val).symm.trans
        ((congrArg f.toFun (congrArg Subtype.val hm')).trans (f.map_face false m y'.val))
    rw [f.map_comp m _ _ _ hc, f.map_comp m _ _ _ hc']
    congr 1

instance truncationSetoid : Setoid (C.bounded n) where
  r := Rel C n
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- Carrier of the intelligent truncation, before equipping its operations. -/
abbrev Cell (C : StrictOmegaCategory.{0}) (n : ℕ) := Quotient (truncationSetoid (C := C) (n := n))

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

end OAI
