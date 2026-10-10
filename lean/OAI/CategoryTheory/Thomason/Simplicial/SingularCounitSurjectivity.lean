import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Transfer.TripleGlobeCylinderPushout
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

namespace OAI

section

/-! # Cellular closure of actual realization deformations -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

noncomputable section

/-- Maps whose actual realizations admit a stationary deformation retraction. -/
def realizationDeformations : MorphismProperty SSet.{0} :=
  fun _ _ f => Nonempty (TopologicalDeformation.Data (SSet.toTop.map f))

theorem realizationDeformations_weak : realizationDeformations ≤ realizationWeakEquivalences := by
  rintro A B f ⟨d⟩
  apply weakEquivalence_of_strongDeformationRetract (SSet.toTop.map f).hom d.retraction.hom _ d.homotopy
  exact congrArg TopCat.Hom.hom d.left_inv

/-- Realized stationary deformations are closed under arbitrary small coproducts. -/
theorem realizationDeformations_coproducts :
    coproducts.{0} realizationDeformations ≤ realizationDeformations := by
  intro A B f hf
  rw [coproducts_iff] at hf
  obtain ⟨α, F, G, c, e, hc, he, φ, hφ⟩ := hf
  let a := discreteCoproductIso F hc
  let b := discreteCoproductIso G he
  let σ := CategoryTheory.Limits.Sigma.map (fun k => φ.app ⟨k⟩)
  have w : σ ≫ b.hom = a.hom ≫ hc.desc (Cocone.mk _ (φ ≫ e.ι)) := by
    apply Sigma.hom_ext
    intro k
    dsimp only [σ]
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, discreteCoproductIso_fac]
    rw [← Category.assoc, discreteCoproductIso_fac, hc.fac]
    rfl
  refine ⟨(realizedCoproductData (fun k => φ.app ⟨k⟩)
    (fun k => (hφ ⟨k⟩).some)).ofIso (SSet.toTop.mapIso a) (SSet.toTop.mapIso b) ?_⟩
  change SSet.toTop.map σ ≫ SSet.toTop.map b.hom =
    SSet.toTop.map a.hom ≫ SSet.toTop.map (hc.desc (Cocone.mk _ (φ ≫ e.ι)))
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, w]

/-- Realized stationary deformations extend over every simplicial pushout. -/
theorem realizationDeformations_pushouts :
    realizationDeformations.pushouts ≤ realizationDeformations := by
  rintro X Y f ⟨A, B, i, a, b, ⟨d⟩, h⟩
  exact ⟨TopologicalDeformation.pushoutData (SSet.toTop.map_isPushout h.flip) d⟩

/-- A countable simplicial sequence of realized deformations has a realized
stationary deformation on its actual colimit inclusion. -/
def realizedSequenceData {F : ℕ ⥤ SSet.{0}} {c : Cocone F} (hc : IsColimit c)
    (d : ∀ n, TopologicalDeformation.Data
      (SSet.toTop.map (F.map (homOfLE (Nat.le_succ n))))) :
    TopologicalDeformation.Data (SSet.toTop.map (c.ι.app 0)) :=
  TopologicalDeformation.Sequential.colimitData (isColimitOfPreserves SSet.toTop hc) d

/-- The precise countable closure used by the horn small-object argument. -/
theorem realizationDeformations_countable :
    realizationDeformations.transfiniteCompositionsOfShape ℕ ≤ realizationDeformations := by
  rintro A B f ⟨h⟩
  let d := realizedSequenceData h.isColimit (fun n => (h.map_mem n (not_isMax n)).some)
  refine ⟨d.ofIso (SSet.toTop.mapIso h.isoBot) (Iso.refl _) ?_⟩
  change SSet.toTop.map (h.incl.app 0) ≫ 𝟙 _ =
    SSet.toTop.map h.isoBot.hom ≫ SSet.toTop.map f
  rw [Category.comp_id, ← SSet.toTop.map_comp]
  apply congrArg (fun g => SSet.toTop.map g)
  calc
    h.incl.app 0 = h.isoBot.hom ≫ (h.isoBot.inv ≫ h.incl.app 0) := by simp
    _ = h.isoBot.hom ≫ f := congrArg (fun g => h.isoBot.hom ≫ g) h.fac

end

end Thomason.Construction

end

section

/-! # Anodyne extensions are actual realization weak equivalences

The countable small-object presentation has stationary deformation
retractions at its cellular stages. Their compatible colimit deformation,
followed by the actual weak-equivalence retract law, proves the semantic
inclusion without assuming Kan–Quillen.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

noncomputable section

/-- Every generating horn has a stationary deformation after realization. -/
theorem horn_generators_deformations : J.{0} ≤ realizationDeformations := by
  intro X Y f hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact ⟨realizedHornData i⟩

/-- All stages in the countable horn construction admit actual deformations. -/
theorem horn_cell_stages_deformations :
    (coproducts.{0} J.{0}).pushouts ≤ realizationDeformations :=
  (pushouts_monotone (coproducts_monotone horn_generators_deformations)).trans
    ((pushouts_monotone realizationDeformations_coproducts).trans
      realizationDeformations_pushouts)

/-- Every countable horn-cell complex is weak for actual geometric realization. -/
theorem horn_cell_complexes_weak :
    (coproducts.{0} J.{0}).pushouts.transfiniteCompositionsOfShape ℕ ≤
      realizationWeakEquivalences :=
  (transfiniteCompositionsOfShape_monotone ℕ horn_cell_stages_deformations).trans
    (realizationDeformations_countable.trans realizationDeformations_weak)

/-- The semantic half of the anodyne characterization, proved without any KQ input. -/
theorem anodyne_realization_weak : SSet.anodyneExtensions.{0} ≤ realizationWeakEquivalences := by
  rw [SSet.anodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]
  rw [retracts_le_iff]
  exact horn_cell_complexes_weak

/-- Anodyne extensions satisfy both parts of the intended trivial-cofibration class. -/
theorem anodyne_mono_realization_weak :
    SSet.anodyneExtensions.{0} ≤ monomorphisms SSet.{0} ⊓ realizationWeakEquivalences := by
  intro X Y f hf
  refine ⟨?_, anodyne_realization_weak f hf⟩
  have hm := antitone_llp (antitone_rlp J_le_monomorphisms) f hf
  rwa [SSet.rlp_monomorphisms, boundary_left_class] at hm

end

end Thomason.Construction

end

section

/-! # Every realized anodyne extension is a stationary deformation inclusion -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty SSet.modelCategoryQuillen

noncomputable section

instance : realizationDeformations.IsStableUnderRetracts where
  of_retract r h := ⟨h.some.ofRetract (r.map SSet.toTop)⟩

/-- The complete cellular construction gives a deformation, including the final arrow retract. -/
theorem anodyne_realization_deformations : SSet.anodyneExtensions.{0} ≤ realizationDeformations := by
  rw [SSet.anodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0, retracts_le_iff]
  exact (transfiniteCompositionsOfShape_monotone ℕ horn_cell_stages_deformations).trans
    realizationDeformations_countable

/-- A chosen actual stationary deformation for any anodyne extension. -/
def anodyneRealizationData {A B : SSet.{0}} (f : A ⟶ B) (hf : SSet.anodyneExtensions f) :
    TopologicalDeformation.Data (SSet.toTop.map f) :=
  (anodyne_realization_deformations f hf).some

/-- Every singular map on an anodyne subobject extends by the constructed retraction. -/
def singularAnodyneExtension {A B : SSet.{0}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) (X : TopCat.{0}) (a : A ⟶ TopCat.toSSet.obj X) :
    B ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv B X ((anodyneRealizationData f hf).retraction ≫
    (sSetTopAdj.homEquiv A X).symm a)

@[reassoc]
theorem singularAnodyneExtension_fac {A B : SSet.{0}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) (X : TopCat.{0}) (a : A ⟶ TopCat.toSSet.obj X) :
    f ≫ singularAnodyneExtension f hf X a = a := by
  rw [singularAnodyneExtension, ← sSetTopAdj.homEquiv_naturality_left,
    ← Category.assoc, (anodyneRealizationData f hf).left_inv, Category.id_comp,
    Equiv.apply_symm_apply]

/-- Singularization preserves the weak status of these actual geometric inclusions. -/
theorem singular_realized_anodyne_weak {A B : SSet.{0}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) :
    realizationWeakEquivalences (TopCat.toSSet.map (SSet.toTop.map f)) :=
  singular_deformation_weak (anodyneRealizationData f hf)

end

end Thomason.Construction

end

section

/-! # Reverse base deformations and anodyne fibre inclusions -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Lift a reverse contraction of the base to a stationary deformation onto the
actual point fibre. The stationarity premise is the exact cylinder equality
on that fibre, not a weak-equivalence or lifting assumption. -/
theorem kan_fiber_deformation_reverse {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (b : B _⦋0⦌)
    (H : SSet.Homotopy (SSet.const b) (𝟙 B))
    (hs : ((simplicialPointFiber p b).ι ≫ p) ▷ Δ[1] ≫ H.h =
      fst (simplicialPointFiber p b).toSSet Δ[1] ≫ (simplicialPointFiber p b).ι ≫ p) :
    ∃ r : E ⟶ (simplicialPointFiber p b).toSSet,
      (simplicialPointFiber p b).ι ≫ r = 𝟙 _ ∧
      ∃ T : SSet.Homotopy (r ≫ (simplicialPointFiber p b).ι) (𝟙 E),
        (simplicialPointFiber p b).ι ▷ Δ[1] ≫ T.h =
          fst (simplicialPointFiber p b).toSSet Δ[1] ≫ (simplicialPointFiber p b).ι ∧
        T.h ≫ p = p ▷ Δ[1] ≫ H.h := by
  let F := simplicialPointFiber p b
  let c := fst F.toSSet (Δ[1] : SSet.{0}) ≫ F.ι
  let d := p ▷ (Δ[1] : SSet.{0}) ≫ H.h
  have hc : SSet.ι₁ ≫ c = F.ι ≫ 𝟙 E := by
    simp only [c, ← Category.assoc, SSet.ι₁_fst, Category.id_comp, Category.comp_id]
  have hd : c ≫ p = F.ι ▷ Δ[1] ≫ d := by
    dsimp only [c, d]
    calc
      (fst F.toSSet Δ[1] ≫ F.ι) ≫ p = fst F.toSSet Δ[1] ≫ F.ι ≫ p :=
        Category.assoc _ _ _
      _ = ((F.ι ≫ p) ▷ Δ[1]) ≫ H.h := hs.symm
      _ = (F.ι ▷ Δ[1] ≫ p ▷ Δ[1]) ≫ H.h :=
        congrArg (fun q => q ≫ H.h) (comp_whiskerRight F.ι p Δ[1])
      _ = F.ι ▷ Δ[1] ≫ p ▷ Δ[1] ≫ H.h := Category.assoc _ _ _
  have h₀ : 𝟙 E ≫ p = SSet.ι₁ ≫ d := by
    dsimp only [d]
    have hn : SSet.ι₁ ≫ p ▷ Δ[1] = p ≫ SSet.ι₁ := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, H.h₁, Category.comp_id, Category.id_comp]
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_cylinder_lift_one F.ι p (𝟙 E) c d hc hd h₀
  let f := SSet.ι₀ ≫ e
  have hf : f ≫ p = SSet.const b := by
    dsimp only [f]
    rw [Category.assoc, hep]
    dsimp only [d]
    have hn : SSet.ι₀ ≫ p ▷ Δ[1] = p ≫ SSet.ι₀ := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, H.h₀, SSet.comp_const]
  let r := simplicialPointFiberLift p b f hf
  have hr : F.ι ≫ r = 𝟙 _ := by
    apply (cancel_mono F.ι).mp
    rw [Category.assoc, simplicialPointFiberLift_ι, Category.id_comp]
    dsimp only [f]
    have hn : F.ι ≫ SSet.ι₀ = SSet.ι₀ ≫ F.ι ▷ Δ[1] := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, hei]
    rfl
  refine ⟨r, hr, ⟨{ h := e, h₀ := ?_, h₁ := he₀, rel := ?_ }, hei, hep⟩⟩
  · exact (simplicialPointFiberLift_ι p b f hf).symm
  · apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property


end

end Thomason.Construction

end

section

/-! # Point fibres over a stationary two-step contraction -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Two simplicial homotopies through a common map suffice for an actual
homotopy inverse after realization. -/
theorem simplicial_retraction_weak_of_zigzag {A E : SSet.{0}}
    (i : A ⟶ E) (r : E ⟶ A) (f : E ⟶ E) (hir : i ≫ r = 𝟙 A)
    (H₀ : SSet.Homotopy f (𝟙 E)) (H₁ : SSet.Homotopy f (r ≫ i)) :
    realizationWeakEquivalences i := by
  apply homotopyEquiv_isWeakHomotopyEquivalence
    (show ContinuousMap.HomotopyEquiv (SSet.toTop.obj A) (SSet.toTop.obj E) from {
      toFun := (SSet.toTop.map i).hom
      invFun := (SSet.toTop.map r).hom
      left_inv := by
        have he := SSet.toTop.congr_map hir
        rw [SSet.toTop.map_comp, SSet.toTop.map_id] at he
        have he' := congrArg TopCat.Hom.hom he
        change (SSet.toTop.map r).hom.comp (SSet.toTop.map i).hom =
          ContinuousMap.id _ at he'
        rw [he']
      right_inv := by
        let h := (RealizedCylinder.homotopy H₁).symm.trans (RealizedCylinder.homotopy H₀)
        exact ⟨{ toContinuousMap := h.toContinuousMap
                 map_zero_left := fun x => (h.apply_zero x).trans
                   (congrArg (fun q => q.hom x) (SSet.toTop.map_comp r i))
                 map_one_left := fun x => (h.apply_one x).trans
                   (congrArg (fun q => q.hom x) (SSet.toTop.map_id E)) }⟩ })

/-- A stationary zigzag from the identity of the base to a constant lifts
relative to the entire point fibre. This includes contractions to interior
vertices, for which no single directed simplicial homotopy exists. -/
theorem kan_fiber_weak_of_zigzag {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (b : B _⦋0⦌) (D : B ⟶ B)
    (H₀ : SSet.Homotopy D (𝟙 B)) (H₁ : SSet.Homotopy D (SSet.const b))
    (hs₀ : ∀ K : SSet.{0}, (SSet.const (X := K) b) ▷ Δ[1] ≫ H₀.h =
      fst K Δ[1] ≫ SSet.const b)
    (hs₁ : ∀ K : SSet.{0}, (SSet.const (X := K) b) ▷ Δ[1] ≫ H₁.h =
      fst K Δ[1] ≫ SSet.const b) :
    realizationWeakEquivalences (simplicialPointFiber p b).ι := by
  let F := simplicialPointFiber p b
  let c := fst F.toSSet (Δ[1] : SSet.{0}) ≫ F.ι
  let d₀ := p ▷ (Δ[1] : SSet.{0}) ≫ H₀.h
  let d₁ := p ▷ (Δ[1] : SSet.{0}) ≫ H₁.h
  have hc₀ : SSet.ι₁ ≫ c = F.ι ≫ 𝟙 E := by
    simp only [c, ← Category.assoc, SSet.ι₁_fst, Category.id_comp, Category.comp_id]
  have hrel (H : B ⊗ Δ[1] ⟶ B)
      (hs : (SSet.const (X := F.toSSet) b) ▷ Δ[1] ≫ H =
        fst F.toSSet Δ[1] ≫ SSet.const b) :
      c ≫ p = F.ι ▷ Δ[1] ≫ (p ▷ Δ[1] ≫ H) := by
    dsimp only [c]
    rw [Category.assoc, simplicialPointFiber_ι_comp]
    rw [← Category.assoc, ← comp_whiskerRight, simplicialPointFiber_ι_comp, hs]
  have hnat (ε : E ⟶ E ⊗ (Δ[1] : SSet.{0}))
      (η : B ⟶ B ⊗ (Δ[1] : SSet.{0}))
      (h : ε ≫ p ▷ Δ[1] = p ≫ η) (H : B ⊗ Δ[1] ⟶ B) :
      ε ≫ (p ▷ Δ[1] ≫ H) = p ≫ η ≫ H := by rw [← Category.assoc, h, Category.assoc]
  have hn₀ : SSet.ι₀ ≫ p ▷ (Δ[1] : SSet.{0}) = p ≫ SSet.ι₀ := by
    apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  have hn₁ : SSet.ι₁ ≫ p ▷ (Δ[1] : SSet.{0}) = p ≫ SSet.ι₁ := by
    apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  have hd₀ : 𝟙 E ≫ p = SSet.ι₁ ≫ d₀ := by
    dsimp only [d₀]
    rw [hnat _ _ hn₁, H₀.h₁, Category.comp_id, Category.id_comp]
  obtain ⟨e₀, he₀, hei₀, hep₀⟩ := exists_kan_cylinder_lift_one F.ι p (𝟙 E) c d₀
    hc₀ (hrel H₀.h (hs₀ _)) hd₀
  let f := SSet.ι₀ ≫ e₀
  have hif : F.ι ≫ f = F.ι := by
    have hn : F.ι ≫ SSet.ι₀ = SSet.ι₀ ≫ F.ι ▷ (Δ[1] : SSet.{0}) := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    dsimp only [f]
    rw [← Category.assoc, hn, Category.assoc, hei₀]
    simp only [c, ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  have hfp : f ≫ p = p ≫ D := by
    dsimp only [f]
    rw [Category.assoc, hep₀]
    dsimp only [d₀]
    rw [hnat _ _ hn₀, H₀.h₀]
  have hc₁ : SSet.ι₀ ≫ c = F.ι ≫ f := by
    rw [hif]
    simp only [c, ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  have hd₁ : f ≫ p = SSet.ι₀ ≫ d₁ := by
    dsimp only [d₁]
    rw [hfp, hnat _ _ hn₀, H₁.h₀]
  obtain ⟨e₁, he₁, hei₁, hep₁⟩ := exists_kan_cylinder_lift F.ι p f c d₁
    hc₁ (hrel H₁.h (hs₁ _)) hd₁
  let g := SSet.ι₁ ≫ e₁
  have hgp : g ≫ p = SSet.const b := by
    dsimp only [g]
    rw [Category.assoc, hep₁]
    dsimp only [d₁]
    rw [hnat _ _ hn₁, H₁.h₁, SSet.comp_const]
  let r := simplicialPointFiberLift p b g hgp
  have hr : F.ι ≫ r = 𝟙 _ := by
    apply (cancel_mono F.ι).mp
    rw [Category.assoc, simplicialPointFiberLift_ι, Category.id_comp]
    have hn : F.ι ≫ SSet.ι₁ = SSet.ι₁ ≫ F.ι ▷ (Δ[1] : SSet.{0}) := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    dsimp only [g]
    rw [← Category.assoc, hn, Category.assoc, hei₁]
    simp only [c, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  apply simplicial_retraction_weak_of_zigzag F.ι r f hr
  · exact { h := e₀, h₀ := rfl, h₁ := he₀, rel := by
              apply NatTrans.ext
              funext j
              apply ConcreteCategory.hom_ext
              intro z
              exact False.elim z.1.property }
  · exact { h := e₁, h₀ := he₁, h₁ := (simplicialPointFiberLift_ι p b g hgp).symm,
            rel := by
              apply NatTrans.ext
              funext j
              apply ConcreteCategory.hom_ext
              intro z
              exact False.elim z.1.property }

end

end Thomason.Construction

end

section

/-! # Reduction of the singular-unit comparison to Kan complexes

Anodyne replacement is constructed from the already proved algebraic
factorization. Both sides of the unit naturality square are weak by the
actual deformation construction, so the unit test is unchanged.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra SSet.modelCategoryQuillen

noncomputable section

/-- The genuine singular-unit weak test is invariant under anodyne extension. -/
theorem singular_unit_anodyne_iff {A B : SSet.{0}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) :
    realizationWeakEquivalences (sSetTopAdj.unit.app A) ↔
      realizationWeakEquivalences (sSetTopAdj.unit.app B) := by
  have hw := anodyne_realization_weak f hf
  have hg := singular_realized_anodyne_weak f hf
  have hn : f ≫ sSetTopAdj.unit.app B = sSetTopAdj.unit.app A ≫
      TopCat.toSSet.map (SSet.toTop.map f) := sSetTopAdj.unit.naturality f
  constructor
  · intro hA
    apply realizationWeakEquivalences.of_precomp f _ hw
    rw [hn]
    exact realizationWeakEquivalences.comp_mem _ _ hA hg
  · intro hB
    apply realizationWeakEquivalences.of_postcomp _ _ hg
    rw [← hn]
    exact realizationWeakEquivalences.comp_mem _ _ hw hB

/-- The actual horn factorization of the map to the terminal simplicial set. -/
def kanReplacementFactorization (K : SSet.{0}) :
    MapFactorizationData SSet.anodyneExtensions J.rlp (terminal.from K) := by
  let := horn_weakFactorizationSystem
  exact factorizationData SSet.anodyneExtensions J.rlp (terminal.from K)

/-- The object produced by that factorization is Kan. -/
theorem kanReplacement_kan (K : SSet.{0}) :
    SSet.KanComplex (kanReplacementFactorization K).Z := by
  change Fibration (terminal.from (kanReplacementFactorization K).Z)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  have he : terminal.from (kanReplacementFactorization K).Z =
      (kanReplacementFactorization K).p := Subsingleton.elim _ _
  rw [he]
  exact (kanReplacementFactorization K).hp

/-- The singular-unit comparison on any simplicial set is exactly its test
on the constructed Kan replacement. -/
theorem singular_unit_kan_replacement_iff (K : SSet.{0}) :
    realizationWeakEquivalences (sSetTopAdj.unit.app K) ↔
      realizationWeakEquivalences (sSetTopAdj.unit.app (kanReplacementFactorization K).Z) :=
  singular_unit_anodyne_iff _ (kanReplacementFactorization K).hi

/-- It suffices to prove the unit weak theorem on actual Kan complexes. -/
theorem singular_unit_weak_of_kan_cases
    (h : ∀ K : SSet.{0}, SSet.KanComplex K →
      realizationWeakEquivalences (sSetTopAdj.unit.app K)) (K : SSet.{0}) :
    realizationWeakEquivalences (sSetTopAdj.unit.app K) :=
  (singular_unit_kan_replacement_iff K).mpr (h _ (kanReplacement_kan K))

end

end Thomason.Construction

end

section

/-! # Points in the singular realization and the actual evaluation counit -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- A point of a space gives the corresponding vertex in its singular realization. -/
def singularVertex (X : TopCat.{0}) (x : X) : SSet.toTop.obj (TopCat.toSSet.obj X) :=
  (SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{0}))
    (TopCat.toSSetObj₀Equiv.symm x))).hom default

/-- Adjunction identifies a constant singular vertex with the actual constant map. -/
theorem singularVertex_map_counit (X : TopCat.{0}) (x : X) :
    SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{0}))
      (TopCat.toSSetObj₀Equiv.symm x)) ≫ sSetTopAdj.counit.app X =
      TopCat.ofHom (ContinuousMap.const _ x) := by
  change (sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) X).symm
    (SSet.const (TopCat.toSSetObj₀Equiv.symm x)) = _
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, sSetTopAdj_homEquiv_stdSimplex_zero]
  rfl

/-- Evaluation sends the canonical singular vertex back to its original point. -/
theorem counit_singularVertex (X : TopCat.{0}) (x : X) :
    (sSetTopAdj.counit.app X).hom (singularVertex X x) = x :=
  congrArg (fun f => f.hom default) (singularVertex_map_counit X x)

/-- The actual evaluation counit is surjective, before taking components. -/
theorem singular_counit_surjective (X : TopCat.{0}) :
    Function.Surjective (sSetTopAdj.counit.app X).hom :=
  fun x => ⟨singularVertex X x, counit_singularVertex X x⟩

/-- In particular the actual counit is surjective on path components. -/
theorem singular_counit_components_surjective (X : TopCat.{0}) :
    Function.Surjective (HomotopyMaps.componentsMap (sSetTopAdj.counit.app X).hom) := by
  intro x
  induction x using ZerothHomotopy.rec with
  | mk x =>
    exact ⟨ZerothHomotopy.mk (singularVertex X x),
      congrArg ZerothHomotopy.mk (counit_singularVertex X x)⟩

end

end Thomason.Construction

end

section

/-! # The actual weak-equivalence test from barycentric boundary lifting -/

namespace Thomason.Construction.CubicalLifting

open CategoryTheory Topology

noncomputable section

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  (hf : ∀ n, HasLiftingProperty (RealizedCube.boundaryInclusion n) f)

include hf in
/-- All based homotopy groups, including degree zero, are injective under
    the cubical boundary lifting hypothesis. -/
theorem groupMap_injective (n : ℕ) (x : X) :
    Function.Injective (HomotopyMaps.groupMap f.hom n x) := by
  intro a b he
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨H⟩ : GenLoop.Homotopic (HomotopyMaps.loopMap f.hom p)
          (HomotopyMaps.loopMap f.hom q) := Quotient.exact he
      exact Quotient.sound ⟨(liftHomotopy f p q H hf).homotopy⟩

/-- A positive-dimensional based loop lifts with every boundary value fixed. -/
def liftLoop {x : X} (n : ℕ) (p : GenLoop (Fin (n+1)) Y (f.hom x)) :
    GenLoop (Fin (n+1)) X x := by
  let := hf n
  let sq : CommSq (TopCat.const x) (RealizedCube.boundaryInclusion n) f
      (TopCat.ofHom p.val) := ⟨by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro t
    exact (p.property t.val t.property).symm⟩
  refine ⟨sq.lift.hom, ?_⟩
  intro t ht
  exact ConcreteCategory.congr_hom sq.fac_left ⟨t, ht⟩

include hf in
theorem liftLoop_comp {x : X} (n : ℕ) (p : GenLoop (Fin (n+1)) Y (f.hom x))
    (t : Fin (n+1) → unitInterval) : f.hom (liftLoop f hf n p t) = p t := by
  let := hf n
  exact ConcreteCategory.congr_hom (CommSq.fac_right (sq :=
    (show CommSq (TopCat.const x) (RealizedCube.boundaryInclusion n) f
      (TopCat.ofHom p.val) from ⟨by
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro u
        exact (p.property u.val u.property).symm⟩))) t

include hf in
theorem groupMap_surjective (n : ℕ) (x : X) :
    Function.Surjective (HomotopyMaps.groupMap f.hom (n+1) x) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    refine ⟨Quotient.mk _ (liftLoop f hf n p), ?_⟩
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    exact liftLoop_comp f hf n p

include hf in
theorem componentsMap_injective : Function.Injective (HomotopyMaps.componentsMap f.hom) := by
  intro a b he
  induction a using ZerothHomotopy.rec with
  | mk a =>
    induction b using ZerothHomotopy.rec with
    | mk b =>
      obtain ⟨r⟩ : Joined (f.hom a) (f.hom b) := Quotient.exact he
      let p : GenLoop (Fin 0) X a := ⟨ContinuousMap.const _ a, by
        rintro t ⟨i, _⟩
        exact Fin.elim0 i⟩
      let q : GenLoop (Fin 0) X a := ⟨ContinuousMap.const _ b, by
        rintro t ⟨i, _⟩
        exact Fin.elim0 i⟩
      let H : (HomotopyMaps.loopMap f.hom p).val.HomotopyRel
          (HomotopyMaps.loopMap f.hom q).val (Cube.boundary (Fin 0)) := {
        toFun z := r z.1
        continuous_toFun := r.continuous.comp continuous_fst
        map_zero_left _ := r.source
        map_one_left _ := r.target
        prop' _ _ ht := by obtain ⟨i, _⟩ := ht; exact Fin.elim0 i }
      let d := liftHomotopy f p q H hf
      exact ZerothHomotopy.sound {
        toFun t := d.homotopy (t, fun i => Fin.elim0 i)
        continuous_toFun := d.homotopy.continuous.comp (by fun_prop)
        source' := d.homotopy.apply_zero _
        target' := d.homotopy.apply_one _ }

/-- Barycentric boundary lifting also forces surjectivity on actual points.
    Only the singular adjunction and its explicit evaluation map are used. -/
theorem surjective_of_barycentric
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n) f) :
    Function.Surjective f.hom := by
  let d := boundaryRetraction (TopCat.toSSet.map f)
    ((RealizationPrism.singular_boundary_rlp_iff f).mpr hp)
  let r := SSet.toTop.map d.section_ ≫ sSetTopAdj.counit.app X
  have hn : SSet.toTop.map (TopCat.toSSet.map f) ≫ sSetTopAdj.counit.app Y =
      sSetTopAdj.counit.app X ≫ f := sSetTopAdj.counit.naturality f
  have hr : r ≫ f = sSetTopAdj.counit.app Y := by
    dsimp [r]
    rw [Category.assoc, ← hn, ← Category.assoc,
      ← SSet.toTop.map_comp, d.section_comp, SSet.toTop.map_id, Category.id_comp]
  intro y
  obtain ⟨z, hz⟩ := singular_counit_surjective Y y
  exact ⟨r.hom z, (ConcreteCategory.congr_hom hr z).trans hz⟩

/-- The elementary topological lifting test gives the actual bijections on
    components and on every positive homotopy group, independently of the
    remaining singular comparison and Kan--Quillen hypotheses. -/
theorem weak_of_barycentric
    (hp : ∀ n, HasLiftingProperty (RealizationPrism.boundaryInclusion n) f) :
    IsWeakHomotopyEquivalence f.hom := by
  have hc := RealizedCube.boundary_lifting_of_barycentric f hp
  refine ⟨⟨componentsMap_injective f hc, ?_⟩, fun n x =>
    ⟨groupMap_injective f hc (n+1) x, groupMap_surjective f hc n x⟩⟩
  intro a
  induction a using ZerothHomotopy.rec with
  | mk y =>
    obtain ⟨x, rfl⟩ := surjective_of_barycentric f hp y
    exact ⟨ZerothHomotopy.mk x, rfl⟩

end

end Thomason.Construction.CubicalLifting

end

section

/-! # Paths between canonical points of the singular realization -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- The canonical point of the singular realization is natural on continuous maps. -/
theorem singularVertex_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    (SSet.toTop.map (TopCat.toSSet.map f)).hom (singularVertex X x) =
      singularVertex Y (f.hom x) := by
  have he : SSet.const (X := (Δ[0] : SSet.{0})) (TopCat.toSSetObj₀Equiv.symm x) ≫
      TopCat.toSSet.map f = SSet.const (TopCat.toSSetObj₀Equiv.symm (f.hom x)) := by
    rw [SSet.const_comp]
    rfl
  change (SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{0}))
      (TopCat.toSSetObj₀Equiv.symm x)) ≫ SSet.toTop.map (TopCat.toSSet.map f)).hom default = _
  rw [← SSet.toTop.map_comp, he]
  rfl

/-- Every actual path gives a path between the corresponding singular vertices. -/
def singularVertexPath {X : TopCat.{0}} {x y : X} (p : Path x y) :
    Path (singularVertex X x) (singularVertex X y) := by
  let P := SSet.toTop.obj (Δ[0] : SSet.{0})
  let f : P ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  let g : P ⟶ X := TopCat.ofHom (ContinuousMap.const _ y)
  let H : f.hom.Homotopy g.hom := {
    toFun q := p q.1
    continuous_toFun := p.continuous.comp continuous_fst
    map_zero_left := fun _ => p.source
    map_one_left := fun _ => p.target }
  let R := RealizedCylinder.homotopy (singularHomotopy H)
  let z := singularVertex P default
  exact {
    toFun t := R (t, z)
    continuous_toFun := R.continuous.comp (by fun_prop)
    source' := (R.map_zero_left z).trans (singularVertex_naturality f default)
    target' := (R.map_one_left z).trans (singularVertex_naturality g default) }

/-- A singular zero-simplex is exactly the canonical vertex of its evaluated point. -/
theorem singular_zero_simplex_eq_vertex (X : TopCat.{0})
    (a : (Δ[0] : SSet.{0}) ⟶ TopCat.toSSet.obj X)
    (z : SSet.toTop.obj (Δ[0] : SSet.{0})) :
    (SSet.toTop.map a).hom z =
      singularVertex X ((sSetTopAdj.counit.app X).hom ((SSet.toTop.map a).hom z)) := by
  let f := (sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) X).symm a
  have ha : a = SSet.const (TopCat.toSSetObj₀Equiv.symm (f.hom default)) := by
    have he := sSetTopAdj_homEquiv_stdSimplex_zero f
    exact (sSetTopAdj.homEquiv _ _).apply_symm_apply a |>.symm.trans he
  have hz : z = default := Subsingleton.elim _ _
  subst z
  have hx : (sSetTopAdj.counit.app X).hom ((SSet.toTop.map a).hom default) = f.hom default := rfl
  rw [hx, ha]
  rfl

end

end Thomason.Construction

end

section

/-! # The actual singular counit is bijective on path components -/

namespace Thomason.Construction

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- Every point of the singular realization is connected to the vertex of its evaluation. -/
theorem singular_point_joined_vertex (X : TopCat.{0})
    (x : SSet.toTop.obj (TopCat.toSSet.obj X)) :
    Joined x (singularVertex X ((sSetTopAdj.counit.app X).hom x)) := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation (TopCat.toSSet.obj X) x
  let k : SimplexCategory.mk 0 ⟶ j.left :=
    SimplexCategory.Hom.mk (OrderHom.const _ 0)
  let a := SSet.stdSimplex.map k ≫ j.hom
  let u := (SSet.toTopSimplex.inv.app j.left).hom p
  let v := (SSet.toTop.map (SSet.stdSimplex.map k)).hom default
  let : ContractibleSpace ((SSet.stdSimplex ⋙ SSet.toTop).obj j.left) :=
    standard_simplex_realization_contractible j.left.len
  have h : Joined ((SSet.toTop.map j.hom).hom u) ((SSet.toTop.map j.hom).hom v) :=
    (PathConnectedSpace.joined u v).map (SSet.toTop.map j.hom).hom.continuous
  have hv : (SSet.toTop.map j.hom).hom v = (SSet.toTop.map a).hom default := by
    rw [SSet.toTop.map_comp]
    rfl
  change Joined ((RealizationPrism.leg (TopCat.toSSet.obj X) j).hom p)
    ((SSet.toTop.map j.hom).hom v) at h
  rw [hv, singular_zero_simplex_eq_vertex X a default] at h
  let ε := (sSetTopAdj.counit.app X).hom
  have he := h.map ε.continuous
  rw [counit_singularVertex] at he
  exact h.trans (show Joined (singularVertex X (ε ((SSet.toTop.map a).hom default)))
      (singularVertex X (ε ((RealizationPrism.leg (TopCat.toSSet.obj X) j).hom p))) from
    ⟨(singularVertexPath he.somePath).symm⟩)

/-- The path-component part of the genuine singular counit weak-equivalence test. -/
theorem singular_counit_components_bijective (X : TopCat.{0}) :
    Function.Bijective (HomotopyMaps.componentsMap (sSetTopAdj.counit.app X).hom) := by
  refine ⟨?_, singular_counit_components_surjective X⟩
  intro x y h
  induction x using ZerothHomotopy.rec with
  | mk x =>
    induction y using ZerothHomotopy.rec with
    | mk y =>
      have hp : Joined ((sSetTopAdj.counit.app X).hom x)
          ((sSetTopAdj.counit.app X).hom y) := Quotient.exact h
      exact ZerothHomotopy.sound ((singular_point_joined_vertex X x).somePath.trans
        ((singularVertexPath hp.somePath).trans (singular_point_joined_vertex X y).somePath.symm))

end

end Thomason.Construction

end

section

/-! # Exact component compatibility and degree-zero acyclic lifting -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Singular realization induces the same bijectivity test on path components
as the original continuous map, using the proved counit component isomorphisms. -/
theorem singular_map_components_bijective_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    Function.Bijective (HomotopyMaps.componentsMap
      (SSet.toTop.map (TopCat.toSSet.map p)).hom) ↔
      Function.Bijective (HomotopyMaps.componentsMap p.hom) := by
  have hc := congrArg (fun f => HomotopyMaps.componentsMap f.hom)
    (sSetTopAdj.counit.naturality p)
  change HomotopyMaps.componentsMap
      ((sSetTopAdj.counit.app Y).hom.comp (SSet.toTop.map (TopCat.toSSet.map p)).hom) =
    HomotopyMaps.componentsMap (p.hom.comp (sSetTopAdj.counit.app X).hom) at hc
  rw [HomotopyMaps.componentsMap_comp, HomotopyMaps.componentsMap_comp] at hc
  rw [← (singular_counit_components_bijective Y).of_comp_iff', hc]
  exact Function.Bijective.of_comp_iff _ (singular_counit_components_bijective X)

/-- The zero-dimensional part of an actual singular weak equivalence suffices
for strict point surjectivity when the singular map is also Kan. -/
theorem singular_acyclic_surjective {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    Function.Surjective p.hom :=
  singular_fibration_surjective_of_components p
    ((singular_map_components_bijective_iff p).mp hp.1).2

/-- For a surjective continuous map, singularization lifts the degree-zero
boundary. This proves the zero-dimensional lifting statement explicitly. -/
theorem singular_boundary_zero_lifting_of_surjective {X Y : TopCat.{0}}
    (p : X ⟶ Y) (hp : Function.Surjective p.hom) :
    HasLiftingProperty (SSet.boundary 0).ι (TopCat.toSSet.map p) := by
  rw [SSet.boundary_zero]
  refine ⟨fun {a b} sq => ?_⟩
  let f := (sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) Y).symm b
  obtain ⟨x, hx⟩ := hp (f.hom default)
  let g : SSet.toTop.obj (Δ[0] : SSet.{0}) ⟶ X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  have hg : g ≫ p = f := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change p.hom x = f.hom z
    rw [Subsingleton.elim z default]
    exact hx
  have hl : sSetTopAdj.homEquiv (Δ[0] : SSet.{0}) X g ≫ TopCat.toSSet.map p = b := by
    rw [← sSetTopAdj.homEquiv_naturality_right, hg]
    exact (sSetTopAdj.homEquiv _ _).apply_symm_apply b
  exact ⟨⟨{
    l := sSetTopAdj.homEquiv _ _ g
    fac_left := SSet.Subcomplex.isInitialBot.hom_ext _ _
    fac_right := hl }⟩⟩

/-- The first case of the published acyclic Kan lifting implication is proved
for actual singular maps, with no comparison-W assumption. -/
theorem singular_acyclic_boundary_zero {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    HasLiftingProperty (SSet.boundary 0).ι (TopCat.toSSet.map p) :=
  singular_boundary_zero_lifting_of_surjective p (singular_acyclic_surjective p hp)

end

end Thomason.Construction

end

section

/-! # Based cubical lifts through the actual singular counit -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- The adjoint of a constant topological map is the corresponding constant singular map. -/
theorem singular_adjoint_const (K : SSet.{0}) (X : TopCat.{0}) (x : X) :
    sSetTopAdj.homEquiv K X (TopCat.const x) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  rw [Adjunction.homEquiv_unit, TopCat.toSSet_map_const, SSet.comp_const]

/-- Realization of a constant singular map has its value at the canonical vertex. -/
theorem realized_singular_const (K : SSet.{0}) (X : TopCat.{0}) (x : X)
    (p : SSet.toTop.obj K) :
    (SSet.toTop.map (SSet.const (X := K) (TopCat.toSSetObj₀Equiv.symm x))).hom p =
      singularVertex X x := by
  let a : K ⟶ (Δ[0] : SSet.{0}) := SSet.const (SSet.yonedaEquiv (𝟙 _))
  have h := SSet.toTop.congr_map (SSet.comp_const a (TopCat.toSSetObj₀Equiv.symm x))
  rw [SSet.toTop.map_comp] at h
  have hp : (SSet.toTop.map a).hom p = default := Subsingleton.elim _ _
  have he := congrArg (fun f => f.hom p) h
  change (SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{0}))
      (TopCat.toSSetObj₀Equiv.symm x))).hom ((SSet.toTop.map a).hom p) = _ at he
  rw [hp] at he
  exact he.symm

namespace RealizedCube

/-- Each boundary face of a based cube becomes the constant singular simplex. -/
theorem singularMap_face {X : TopCat.{0}} {x : X} (n : ℕ)
    (p : GenLoop (Fin (n+1)) X x) (i : Fin (n+1)) (e : Bool) :
    face n i e ≫ singularMap (n+1) p.val =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  change face n i e ≫ sSetTopAdj.homEquiv _ _
    (TopCat.ofHom (p.val.comp (coordinates (n+1)))) = _
  rw [← Adjunction.homEquiv_naturality_left]
  have h : SSet.toTop.map (face n i e) ≫
      TopCat.ofHom (p.val.comp (coordinates (n+1))) = TopCat.const x := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change p (coordinates (n+1) ((SSet.toTop.map (face n i e)).hom z)) = x
    rw [coordinates_face]
    apply p.property
    refine ⟨i, ?_⟩
    rw [Fin.insertNth_apply_same]
    cases e
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [h, singular_adjoint_const]

/-- The realized lift of a based cube is constant on its entire topological boundary. -/
theorem singularMap_boundary {X : TopCat.{0}} {x : X} (n : ℕ)
    (p : GenLoop (Fin (n+1)) X x) (t : Fin (n+1) → unitInterval)
    (ht : t ∈ Cube.boundary (Fin (n+1))) :
    (SSet.toTop.map (singularMap (n+1) p.val)).hom (sectionMap (n+1) t) =
      singularVertex X x := by
  obtain ⟨i, hi⟩ := ht
  obtain ⟨e, he⟩ : ∃ e : Bool, t i = endpoint e := by
    rcases hi with hi | hi
    · exact ⟨false, hi⟩
    · exact ⟨true, hi⟩
  have hface : t = Fin.insertNth i (endpoint e) (Fin.removeNth i t) := by
    rw [← he, Fin.insertNth_self_removeNth]
  rw [hface, section_face]
  have h := SSet.toTop.congr_map (singularMap_face n p i e)
  rw [SSet.toTop.map_comp] at h
  have hv := congrArg (fun f => f.hom (sectionMap n (Fin.removeNth i t))) h
  exact hv.trans (realized_singular_const _ X x _)

/-- Every based topological cube has a based lift through singular realization. -/
def liftLoop {X : TopCat.{0}} {x : X} (n : ℕ) (p : GenLoop (Fin (n+1)) X x) :
    GenLoop (Fin (n+1)) (SSet.toTop.obj (TopCat.toSSet.obj X)) (singularVertex X x) :=
  ⟨(SSet.toTop.map (singularMap (n+1) p.val)).hom.comp (sectionMap (n+1)),
    singularMap_boundary n p⟩

/-- The lift evaluates to the original loop pointwise. -/
theorem liftLoop_evaluation {X : TopCat.{0}} {x : X} (n : ℕ)
    (p : GenLoop (Fin (n+1)) X x) (t : Fin (n+1) → unitInterval) :
    (sSetTopAdj.counit.app X).hom (liftLoop n p t) = p t :=
  singularMap_evaluation (n+1) p.val t

end RealizedCube

end

end Thomason.Construction

end

section

/-! # The positive homotopy-group surjectivity of singular evaluation at vertices -/

namespace Thomason.Construction

noncomputable section

private theorem basedGroupMap_surjective_iff {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) {a : A} {b : B}
    (e : f a = b) (n : ℕ) :
    Function.Surjective (HomotopyMaps.basedGroupMap f e n) ↔
      Function.Surjective (HomotopyMaps.groupMap f n a) := by
  subst b
  rfl

/-- The based singular counit is surjective on every positive homotopy group. -/
theorem singular_counit_basedGroupMap_surjective (X : TopCat.{0}) (x : X) (n : ℕ) :
    Function.Surjective (HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app X).hom
      (counit_singularVertex X x) (n+1)) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    refine ⟨Quotient.mk _ (RealizedCube.liftLoop n p), ?_⟩
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    exact RealizedCube.liftLoop_evaluation n p t

/-- The same surjectivity in the exact, untransported weak-equivalence convention. -/
theorem singular_counit_groupMap_surjective_vertex (X : TopCat.{0}) (x : X) (n : ℕ) :
    Function.Surjective (HomotopyMaps.groupMap (sSetTopAdj.counit.app X).hom
      (n+1) (singularVertex X x)) := by
  exact (basedGroupMap_surjective_iff _ (counit_singularVertex X x) (n+1)).mp
    (singular_counit_basedGroupMap_surjective X x n)

/-- The actual singular counit is surjective on every positive homotopy group,
including basepoints that are not singular vertices. -/
theorem singular_counit_groupMap_surjective (X : TopCat.{0})
    (x : SSet.toTop.obj (TopCat.toSSet.obj X)) (n : ℕ) :
    Function.Surjective (HomotopyMaps.groupMap (sSetTopAdj.counit.app X).hom (n+1) x) := by
  exact (HomotopyMaps.groupMap_surjective_path n (sSetTopAdj.counit.app X).hom
    (singular_point_joined_vertex X x).somePath).mpr
      (singular_counit_groupMap_surjective_vertex X ((sSetTopAdj.counit.app X).hom x) n)

end

end Thomason.Construction

end

end OAI
