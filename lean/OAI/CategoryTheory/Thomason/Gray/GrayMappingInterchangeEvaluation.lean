import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.GridGlobeCylinderComparison
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeAtoms
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition

namespace OAI

section

/-! # Direct Gray–Street–realization compatibility

The explicitly constructed Street-nerve prism realizes to a continuous
homotopy. Consequently Gray deformations and finite relative prisms satisfy
the actual semantic weak-equivalence test without a Kan–Quillen input.
The right-Gray cylinder comparison is an explicit hypothesis.
-/

namespace Thomason.Construction

open CategoryTheory

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (aw : SimplexComplex.AlexanderWhitneyInput h)

include aw

/-- A strict Gray homotopy induces an actual continuous homotopy of realizations. -/
noncomputable def realizedHomotopy {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    (SSet.toTop.map (h.streetNerve.map ((G.endpoint false).app X ≫ P))).hom.Homotopy
      (SSet.toTop.map (h.streetNerve.map ((G.endpoint true).app X ≫ P))).hom :=
  RealizedCylinder.homotopy (G.nerveHomotopy aw P)

/-- Gray homotopies preserve the semantic Thomason weak test directly. -/
theorem cylinder_weakEquivalence_iff_direct {X Y : StrictOmegaCategory.{0}}
    (P : G.cylinder.obj X ⟶ Y) :
    h.streetWeakEquivalences ((G.endpoint false).app X ≫ P) ↔
      h.streetWeakEquivalences ((G.endpoint true).app X ≫ P) :=
  RealizedCylinder.weakEquivalence_iff (G.nerveHomotopy aw P)

/-- A Gray deformation retraction is weak on both maps without a model structure. -/
theorem deformation_retract_weakEquivalences_direct {A X : StrictOmegaCategory.{0}}
    (i : A ⟶ X) (r : X ⟶ A) (hi : i ≫ r = 𝟙 A)
    (P : G.cylinder.obj X ⟶ X)
    (h₀ : (G.endpoint false).app X ≫ P = r ≫ i)
    (h₁ : (G.endpoint true).app X ≫ P = 𝟙 X) :
    h.streetWeakEquivalences i ∧ h.streetWeakEquivalences r := by
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  have : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty
  have : h.streetWeakEquivalences.IsStableUnderRetracts :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).IsStableUnderRetracts
  have hri : h.streetWeakEquivalences (r ≫ i) := by
    have hc := G.cylinder_weakEquivalence_iff_direct aw P
    rw [h₀, h₁] at hc
    exact hc.mpr (h.streetWeakEquivalences.id_mem X)
  let retract : RetractArrow i (r ≫ i) := {
    i := Arrow.homMk i (𝟙 X) (by simp [← Category.assoc, hi])
    r := Arrow.homMk r (𝟙 X) (by simp)
    retract := by apply Arrow.hom_ext <;> simp [hi] }
  have hwi : h.streetWeakEquivalences i := h.streetWeakEquivalences.of_retract retract hri
  refine ⟨hwi, ?_⟩
  apply h.streetWeakEquivalences.of_precomp i r hwi
  rw [hi]
  exact h.streetWeakEquivalences.id_mem A

end RightGrayInput

namespace RelativePrismData

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (G : RightGrayInput h) (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)
  (aw : SimplexComplex.AlexanderWhitneyInput h)

include G t aw

/-- The finite-dimensional relative prism bridge needs no Kan–Quillen axioms. -/
theorem finite_weakEquivalence_iff_direct :
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap D.first))) ↔
    h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap D.last))) := by
  let X : StrictOmegaCategory := (r.reflect.obj (h.categorification.obj (nerve E))).val
  let W : (X ⟶ X) → Prop := fun f => h.streetWeakEquivalences f
  exact (congrArg W (D.finitePrism_endpoint h G t r false)).symm.to_iff.trans
    ((G.cylinder_weakEquivalence_iff_direct aw (D.finitePrism h G t r)).trans
      (congrArg W (D.finitePrism_endpoint h G t r true)).to_iff)

end RelativePrismData

end Thomason.Construction

end

section

/-! # Natural continuous cone pieces for an ordinary poset nerve -/

namespace Thomason.Construction.ConePrism

open CategoryTheory CategoryTheory.Limits

/-- The barycentric cone in the universe-lifted simplex used by realization. -/
noncomputable def liftedBarycentric (n : ℕ) :
    TopologicalInterval.cylinder.obj (SimplexCategory.toTop.{0}.obj (.mk n)) ⟶
      SimplexCategory.toTop.{0}.obj (.mk (n+1)) :=
  TopCat.ofHom ⟨fun p => ULift.up (barycentric n (p.1.down, p.2)), by fun_prop⟩

/-- Naturality before descending through geometric realization. -/
theorem liftedBarycentric_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    TopologicalInterval.cylinder.map (SimplexCategory.toTop.{0}.map f) ≫
      liftedBarycentric n.len =
    liftedBarycentric m.len ≫
      SimplexCategory.toTop.{0}.map (SimplexCategory.Hom.mk (ordinalMap f.toOrderHom)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact congrArg ULift.up (barycentric_naturality f.toOrderHom p.1.down p.2).symm

variable {P : Type} [PartialOrder P] (v : P) (hv : ∀ x, x ≤ v)

/-- The cone piece on one original simplex of the ordinary nerve. -/
noncomputable def piece (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    TopologicalInterval.cylinder.obj ((RealizationPrism.diagram (nerve P)).obj j) ⟶
      SSet.toTop.obj (nerve P) :=
  liftedBarycentric j.left.len ≫ RealizationPrism.leg (nerve P) (coneIndex v hv j)

/-- All face and degeneracy operators preserve the explicit cone pieces. -/
theorem piece_naturality {j k : CostructuredArrow SSet.stdSimplex (nerve P)} (f : j ⟶ k) :
    TopologicalInterval.cylinder.map ((RealizationPrism.diagram (nerve P)).map f) ≫
      piece v hv k = piece v hv j := by
  change TopologicalInterval.cylinder.map (SimplexCategory.toTop.map f.left) ≫
      (liftedBarycentric k.left.len ≫ RealizationPrism.leg (nerve P) (coneIndex v hv k)) = _
  rw [← Category.assoc, liftedBarycentric_naturality, Category.assoc]
  have hc := (RealizationPrism.cocone (nerve P)).w (coneMap v hv f)
  exact congrArg (fun q => liftedBarycentric j.left.len ≫ q) hc

/-- The actual global continuous cone map, with no KQ assumption. -/
noncomputable def realizationCone :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj (nerve P)) ⟶ SSet.toTop.obj (nerve P) :=
  RealizationPrism.assemble (nerve P) _ (piece v hv) (piece_naturality v hv)

end Thomason.Construction.ConePrism

end

section

/-! # Actual cylinder contractions and boundary-lifting weak equivalences

Minimum and maximum on the simplicial interval give explicit simplicial
contractions. Their realized homotopies prove both endpoint maps weak,
without the anodyne characterization or any Kan–Quillen assumption.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Pointwise minimum of two simplices of the ordered interval. -/
def intervalMin {n : SimplexCategoryᵒᵖ} (a b : (Δ[1] : SSet.{0}).obj n) :
    (Δ[1] : SSet.{0}).obj n :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    { toFun := fun i => min ((SSet.stdSimplex.objEquiv a).toOrderHom i)
        ((SSet.stdSimplex.objEquiv b).toOrderHom i)
      monotone' := fun _ _ h => min_le_min
        ((SSet.stdSimplex.objEquiv a).toOrderHom.monotone h)
        ((SSet.stdSimplex.objEquiv b).toOrderHom.monotone h) })

/-- Pointwise maximum of two simplices of the ordered interval. -/
def intervalMax {n : SimplexCategoryᵒᵖ} (a b : (Δ[1] : SSet.{0}).obj n) :
    (Δ[1] : SSet.{0}).obj n :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    { toFun := fun i => max ((SSet.stdSimplex.objEquiv a).toOrderHom i)
        ((SSet.stdSimplex.objEquiv b).toOrderHom i)
      monotone' := fun _ _ h => max_le_max
        ((SSet.stdSimplex.objEquiv a).toOrderHom.monotone h)
        ((SSet.stdSimplex.objEquiv b).toOrderHom.monotone h) })

/-- Contract the simplicial cylinder to its zero endpoint. -/
def cylinderMinHomotopy (X : SSet.{0}) :
    SSet.Homotopy (fst X Δ[1] ≫ SSet.ι₀) (𝟙 (X ⊗ Δ[1])) where
  h := { app n := ↾fun x => (x.1.1, intervalMin x.1.2 x.2)
         naturality m n a := by
           ext x
           apply Prod.ext
           · rfl
           · apply SSet.stdSimplex.objEquiv.injective
             ext k
             rfl }
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      change (min ((SSet.stdSimplex.objEquiv x.2).toOrderHom k) (0 : Fin 2)).val = 0
      rw [min_eq_right (Fin.zero_le _)]
      rfl
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      change (min ((SSet.stdSimplex.objEquiv x.2).toOrderHom k) (1 : Fin 2)).val =
        ((SSet.stdSimplex.objEquiv x.2).toOrderHom k).val
      exact congrArg Fin.val (min_eq_left (show _ ≤ (1 : Fin 2) from Fin.le_last _))
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Contract the simplicial cylinder to its one endpoint. -/
def cylinderMaxHomotopy (X : SSet.{0}) :
    SSet.Homotopy (𝟙 (X ⊗ Δ[1])) (fst X Δ[1] ≫ SSet.ι₁) where
  h := { app n := ↾fun x => (x.1.1, intervalMax x.1.2 x.2)
         naturality m n a := by
           ext x
           apply Prod.ext
           · rfl
           · apply SSet.stdSimplex.objEquiv.injective
             ext k
             rfl }
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      change (max ((SSet.stdSimplex.objEquiv x.2).toOrderHom k) (0 : Fin 2)).val =
        ((SSet.stdSimplex.objEquiv x.2).toOrderHom k).val
      exact congrArg Fin.val (max_eq_left (Fin.zero_le _))
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.objEquiv.injective
      ext k
      change (max ((SSet.stdSimplex.objEquiv x.2).toOrderHom k) (1 : Fin 2)).val = 1
      exact congrArg Fin.val (max_eq_right (show _ ≤ (1 : Fin 2) from Fin.le_last _))
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- The actual simplicial cylinder projection satisfies the semantic weak test. -/
theorem cylinder_projection_weak (X : SSet.{0}) :
    realizationWeakEquivalences (fst X Δ[1]) := by
  have hcomp : realizationWeakEquivalences (fst X Δ[1] ≫ SSet.ι₀) :=
    (RealizedCylinder.weakEquivalence_iff (cylinderMinHomotopy X)).mpr
      (realizationWeakEquivalences.id_mem _)
  let r : RetractArrow (fst X Δ[1]) (fst X Δ[1] ≫ SSet.ι₀) := {
    i := Arrow.homMk (𝟙 _) SSet.ι₀ (by simp)
    r := Arrow.homMk (𝟙 _) (fst X Δ[1]) (by simp)
    retract := by
      apply Arrow.hom_ext <;> simp }
  exact realizationWeakEquivalences.of_retract r hcomp

/-- The zero endpoint is weak in actual geometric realization. -/
theorem cylinder_endpoint_zero_weak (X : SSet.{0}) :
    realizationWeakEquivalences (SSet.ι₀ (X := X)) := by
  apply realizationWeakEquivalences.of_postcomp SSet.ι₀ (fst X Δ[1]) (cylinder_projection_weak X)
  simpa only [SSet.ι₀_fst] using realizationWeakEquivalences.id_mem X

/-- The one endpoint is weak in actual geometric realization. -/
theorem cylinder_endpoint_one_weak (X : SSet.{0}) :
    realizationWeakEquivalences (SSet.ι₁ (X := X)) := by
  apply realizationWeakEquivalences.of_postcomp SSet.ι₁ (fst X Δ[1]) (cylinder_projection_weak X)
  simpa only [SSet.ι₁_fst] using realizationWeakEquivalences.id_mem X

/-- Every boundary-lifting map is an actual realization weak equivalence. -/
theorem boundary_rlp_weak {X Y : SSet.{0}} (f : X ⟶ Y) (hf : I.rlp f) :
    realizationWeakEquivalences f :=
  boundary_rlp_weak_of_endpoints f hf (cylinder_endpoint_zero_weak X)
    (cylinder_endpoint_one_weak X)

end

end Thomason.Construction

end

section

/-! # Both coordinates of the global realization cylinder comparison -/

namespace Thomason.Construction.RealizedCylinder

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

theorem comparison_leg (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K)
    (x : (RealizationPrism.diagram K).obj j) (t : unitInterval) :
    (comparison K).hom ((RealizationPrism.leg K j).hom x, t) =
      (piece K j).hom (x, t) :=
  congrArg (fun f => f.hom (x, t))
    (RealizationPrism.assemble_fac K _ (piece K) (piece_naturality K) j)

/-- The global prism preserves the original realization point. -/
theorem comparison_first (K : SSet.{0}) (x : SSet.toTop.obj K) (t : unitInterval) :
    (SSet.toTop.map (fst K Δ[1])).hom ((comparison K).hom (x, t)) = x := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation K x
  rw [comparison_leg]
  change ((SSet.toTop.map (j.hom ▷ Δ[1]) ≫ SSet.toTop.map (fst K Δ[1])).hom)
    (PrismBarycentric.standardPrism j.left.len (p.down, t)) = _
  rw [← SSet.toTop.map_comp, whiskerRight_fst, SSet.toTop.map_comp]
  change (SSet.toTop.map j.hom).hom
    ((SSet.toTop.map (fst _ Δ[1])).hom
      (PrismBarycentric.standardPrism j.left.len (p.down, t))) = _
  rw [PrismBarycentric.standardPrism_firstProjection]
  exact congrArg (fun f => f.hom p) (show
    (SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map (𝟙 _)) ≫
      SSet.toTop.map j.hom = RealizationPrism.leg K j from by
    rw [SSet.toTop.map_id]
    exact congrArg (fun f => f ≫ SSet.toTop.map j.hom)
      (Category.comp_id (SSet.toTopSimplex.inv.app j.left)))

/-- The global prism preserves the ordinary interval parameter. -/
theorem comparison_time (K : SSet.{0}) (x : SSet.toTop.obj K) (t : unitInterval) :
    PrismBarycentric.realizationTime.hom
      ((SSet.toTop.map (snd K Δ[1])).hom ((comparison K).hom (x, t))) = t := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation K x
  rw [comparison_leg]
  change PrismBarycentric.realizationTime.hom
    ((SSet.toTop.map (j.hom ▷ Δ[1]) ≫ SSet.toTop.map (snd K Δ[1])).hom
      (PrismBarycentric.standardPrism j.left.len (p.down, t))) = _
  rw [← SSet.toTop.map_comp, whiskerRight_snd]
  exact PrismBarycentric.standardPrism_time j.left.len (p.down, t)

/-- The comparison itself satisfies the full, actual weak homotopy test. -/
theorem comparison_weak (K : SSet.{0}) : topologicalWeakEquivalences (comparison K) := by
  apply topologicalWeakEquivalences.of_postcomp (comparison K)
    (SSet.toTop.map (fst K Δ[1])) (cylinder_projection_weak K)
  have he : comparison K ≫ SSet.toTop.map (fst K Δ[1]) =
      TopologicalInterval.projection (SSet.toTop.obj K) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    exact comparison_first K p.1 p.2
  rw [he]
  exact TopologicalInterval.projection_weak _

end

end Thomason.Construction.RealizedCylinder

end

section

/-! # Naturality and exact endpoints of the realization cylinder comparison -/

namespace Thomason.Construction.RealizedCylinder

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- The comparison is natural in every simplicial map. -/
theorem comparison_naturality {K L : SSet.{0}} (f : K ⟶ L) :
    TopologicalInterval.cylinder.map (SSet.toTop.map f) ≫ comparison L =
      comparison K ≫ SSet.toTop.map (f ▷ Δ[1]) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  obtain ⟨j, p, hp⟩ := RealizationPrism.point_representation K q.1
  rcases q with ⟨x, t⟩
  dsimp only at hp
  subst x
  change (comparison L).hom ((SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p), t) = _
  have he := congrArg (fun g => g.hom p) (RealizationPrism.leg_naturality f j)
  change (SSet.toTop.map f).hom ((RealizationPrism.leg K j).hom p) = _ at he
  rw [he, comparison_leg]
  change (piece L ((CostructuredArrow.map f).obj j)).hom (p, t) =
    (SSet.toTop.map (f ▷ Δ[1])).hom
      ((comparison K).hom ((RealizationPrism.leg K j).hom p, t))
  rw [comparison_leg]
  change (PrismBarycentric.liftedStandardPrism j.left.len ≫
      SSet.toTop.map ((j.hom ≫ f) ▷ Δ[1])).hom (p, t) =
    ((PrismBarycentric.liftedStandardPrism j.left.len ≫ SSet.toTop.map (j.hom ▷ Δ[1])) ≫
      SSet.toTop.map (f ▷ Δ[1])).hom (p, t)
  rw [Category.assoc, ← SSet.toTop.map_comp, comp_whiskerRight]

/-- The exact zero endpoint on the global comparison. -/
theorem comparison_zero (K : SSet.{0}) (x : SSet.toTop.obj K) :
    (comparison K).hom (x, 0) = (SSet.toTop.map SSet.ι₀).hom x := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation K x
  rw [comparison_leg]
  exact congrArg (fun f => f.hom p) (piece_zero K j)

/-- The exact one endpoint on the global comparison. -/
theorem comparison_one (K : SSet.{0}) (x : SSet.toTop.obj K) :
    (comparison K).hom (x, 1) = (SSet.toTop.map SSet.ι₁).hom x := by
  obtain ⟨j, p, rfl⟩ := RealizationPrism.point_representation K x
  rw [comparison_leg]
  exact congrArg (fun f => f.hom p) (piece_one K j)

end

end Thomason.Construction.RealizedCylinder

end

section

/-! # The positive universal map from three matching cell tables -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

variable {L : DirectedComplex.{0}}

def value {n k p : ℕ} (x : Fin 3 → Cell L) (b : Basis n k p) : L.group p :=
  (x b.val.1).table b.val.2 p

theorem tables_below {k p : ℕ} (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (i : Fin 3) (a : Bool) (hp : p < k) :
    (x 0).table a p = (x i).table a p := by
  fin_cases i
  · rfl
  · exact Cell.matching_below (hm 0) a hp
  · exact (Cell.matching_below (hm 0) a hp).trans (Cell.matching_below (hm 1) a hp)

theorem value_embed {n k p : ℕ} (hkn : k < n) (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (i : Fin 3) (b : DirectedGlobeComplex.Basis n p) :
    value x (embed hkn i b) = (x i).table b.val p := by
  by_cases hp : p < k
  · simpa only [embed, dite_eq_left hp, value] using tables_below x hm i b.val hp
  · by_cases he : p = k
    · subst p
      by_cases hb : b.val = false
      · fin_cases i
        · simp [embed, value, hb]
        · simpa [embed, value, hb, predecessor] using Cell.matching_top (hm 0)
        · simpa [embed, value, hb, predecessor] using Cell.matching_top (hm 1)
      · simp [embed, value, hb]
    · simp [embed, hp, he, value]

def descApp {n k : ℕ} (x : Fin 3 → Cell L) (p : ℕ) :
    Chains n k p →ₗ[ℤ] L.group p :=
  Finsupp.linearCombination ℤ (value x)

@[simp] theorem descApp_single {n k p : ℕ} (x : Fin 3 → Cell L)
    (b : Basis n k p) (z : ℤ) :
    descApp x p (Finsupp.single b z) = z • value x b := by simp [descApp]

theorem descApp_embedApp {n k : ℕ} (hkn : k < n) (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (i : Fin 3) (p : ℕ) (u : DirectedGlobeComplex.Chains n p) :
    descApp x p (embedApp hkn i p u) = DirectedGlobeComplex.cellApp n (x i) p u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp [value_embed hkn x hm]

theorem descApp_differential {n k : ℕ} (hkn : k < n) (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (p : ℕ) (u : Chains n k (p+1)) :
    descApp x p (differential hkn p u) = L.differential p (descApp x (p+1) u) := by
  have hs (i : Fin 3) (b : DirectedGlobeComplex.Basis n (p+1)) (z : ℤ) :
      descApp x p (differential hkn p (Finsupp.single (embed hkn i b) z)) =
        L.differential p (descApp x (p+1) (Finsupp.single (embed hkn i b) z)) := by
    rw [← embedApp_single hkn i b z, ← embedApp_differential,
      descApp_embedApp hkn x hm, descApp_embedApp hkn x hm]
    exact DirectedGlobeComplex.cellApp_differential n (x i) p _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    simpa only [embed_self] using hs b.val.1 ⟨b.val.2, b.property.1⟩ z

theorem descApp_augmentation {n k : ℕ} (x : Fin 3 → Cell L) (u : Chains n k 0) :
    L.augmentation (descApp x 0 u) = weight n k 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp [value, Cell.augmentation]

theorem descApp_positive {n k p : ℕ} (x : Fin 3 → Cell L) (u : Chains n k p)
    (hu : u ∈ positive n k p) : descApp x p u ∈ L.positive p := by
  classical
  change (u.sum fun b z => z • value x b) ∈ L.positive p
  apply (L.positive p).sum_mem
  intro b hb
  change u b • value x b ∈ L.positive p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  exact (L.positive p).nsmul_mem ((x b.val.1).positive b.val.2 p) _

def desc {n k : ℕ} (hkn : k < n) (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k) :
    Hom (complex n k hkn) L where
  app p := (descApp x p).toAddMonoidHom
  differential := descApp_differential hkn x hm
  augmentation := descApp_augmentation x
  positive _ _ hu := descApp_positive x _ hu

theorem inclusion_desc {n k : ℕ} (hkn : k < n) (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (i : Fin 3) :
    Hom.comp (inclusion hkn i) (desc hkn x hm) = DirectedGlobeComplex.cellMap n (x i) := by
  apply Hom.ext_app
  intro p u
  exact descApp_embedApp hkn x hm i p u

theorem hom_ext {n k : ℕ} (hkn : k < n) {f g : Hom (complex n k hkn) L}
    (h : ∀ i, Hom.comp (inclusion hkn i) f = Hom.comp (inclusion hkn i) g) : f = g := by
  apply Hom.ext_app
  intro p u
  have hs (i : Fin 3) (b : DirectedGlobeComplex.Basis n p) (z : ℤ) :
      f.app p (Finsupp.single (embed hkn i b) z) =
        g.app p (Finsupp.single (embed hkn i b) z) := by
    have he := congrArg (fun q : Hom (DirectedGlobeComplex.complex n) L =>
      q.app p (Finsupp.single b z)) (h i)
    change f.app p (embedApp hkn i p (Finsupp.single b z)) =
      g.app p (embedApp hkn i p (Finsupp.single b z)) at he
    simpa only [embedApp_single] using he
  let fp : Chains n k p →+ L.group p := f.app p
  let gp : Chains n k p →+ L.group p := g.app p
  change fp u = gp u
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    change f.app p (Finsupp.single b z) = g.app p (Finsupp.single b z)
    simpa only [embed_self] using hs b.val.1 ⟨b.val.2, b.property.1⟩ z

end
end Thomason.Construction.TripleGlobeBasis

end

section

/-! # The actual strict parameter for three successive equal-dimensional cells -/

namespace Thomason.Construction.StrictOmegaCategory.TripleGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

abbrev bridge (n k : ℕ) : Globe.category k ⟶ PastingGlobe.category n n k :=
  Globe.faceMap true k n ≫ PastingGlobe.right n n k

abbrev category (n k : ℕ) : StrictOmegaCategory.{0} :=
  pushout (bridge n k) (Globe.faceMap false k n)

abbrev pair (n k : ℕ) : PastingGlobe.category n n k ⟶ category n k :=
  pushout.inl _ _

abbrev inclusion (n k : ℕ) (i : Fin 3) : Globe.category n ⟶ category n k :=
  if i = 0 then PastingGlobe.left n n k ≫ pair n k
  else if i = 1 then PastingGlobe.right n n k ≫ pair n k
  else pushout.inr _ _

def cell (n k : ℕ) (i : Fin 3) : category n k :=
  (inclusion n k i).toFun Globe.Cell.top

theorem adjacent_matching (n k : ℕ) (i : Fin 2) :
    (category n k).target k (cell n k i.castSucc) =
      (category n k).source k (cell n k i.succ) := by
  fin_cases i
  · have h := congrArg (pair n k).toFun (PastingGlobe.matching n n k)
    exact ((pair n k).map_face true k (PastingGlobe.leftCell n n k)).symm.trans
      (h.trans ((pair n k).map_face false k (PastingGlobe.rightCell n n k)))
  · have h := congrArg (fun F : Globe.category k ⟶ category n k => F.toFun Globe.Cell.top)
      (pushout.condition (f := bridge n k) (g := Globe.faceMap false k n))
    change (inclusion n k 1).toFun ((Globe.category n).face true k Globe.Cell.top) =
      (inclusion n k 2).toFun ((Globe.category n).face false k Globe.Cell.top) at h
    exact ((inclusion n k 1).map_face true k Globe.Cell.top).symm.trans
      (h.trans ((inclusion n k 2).map_face false k Globe.Cell.top))

theorem cell_dimension (n k : ℕ) (i : Fin 3) :
    (category n k).DimensionLE n (cell n k i) :=
  (inclusion n k i).dimensionLE (Globe.category_truncated n Globe.Cell.top)

theorem hom_ext {n k : ℕ} {C : StrictOmegaCategory.{0}}
    (f g : category n k ⟶ C)
    (h : ∀ i, f.toFun (cell n k i) = g.toFun (cell n k i)) : f = g := by
  apply pushout.hom_ext
  · apply PastingGlobe.hom_ext
    · exact h 0
    · exact h 1
  · apply Globe.hom_ext
    exact h 2

theorem desc_condition {n k : ℕ} (C : StrictOmegaCategory.{0}) (x : Fin 3 → C)
    (hd : ∀ i, C.DimensionLE n (x i))
    (hm : ∀ i : Fin 2, C.target k (x i.castSucc) = C.source k (x i.succ)) :
    bridge n k ≫ PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0) =
      Globe.faceMap false k n ≫ Globe.lift C (x 2) (hd 2) := by
  rw [Globe.faceMap_lift]
  apply Globe.hom_ext
  change (PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0)).toFun
      ((PastingGlobe.right n n k).toFun ((Globe.category n).face true k Globe.Cell.top)) =
    C.face false k (x 2)
  let F := PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0)
  exact (congrArg F.toFun ((PastingGlobe.right n n k).map_face true k Globe.Cell.top)).trans
    ((F.map_face true k (PastingGlobe.rightCell n n k)).trans
      ((congrArg (C.face true k) (PastingGlobe.desc_right C (x 0) (x 1)
        (hd 0) (hd 1) (hm 0))).trans (hm 1)))

def desc {n k : ℕ} (C : StrictOmegaCategory.{0}) (x : Fin 3 → C)
    (hd : ∀ i, C.DimensionLE n (x i))
    (hm : ∀ i : Fin 2, C.target k (x i.castSucc) = C.source k (x i.succ)) :
    category n k ⟶ C :=
  pushout.desc (PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
    (Globe.lift C (x 2) (hd 2)) (desc_condition C x hd hm)

@[simp] theorem desc_cell {n k : ℕ} (C : StrictOmegaCategory.{0}) (x : Fin 3 → C)
    (hd : ∀ i, C.DimensionLE n (x i))
    (hm : ∀ i : Fin 2, C.target k (x i.castSucc) = C.source k (x i.succ))
    (i : Fin 3) : (desc C x hd hm).toFun (cell n k i) = x i := by
  have hl := congrArg (fun F : PastingGlobe.category n n k ⟶ C =>
      F.toFun (PastingGlobe.leftCell n n k)) (pushout.inl_desc
        (PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
        (Globe.lift C (x 2) (hd 2)) (desc_condition C x hd hm))
  have hr := congrArg (fun F : PastingGlobe.category n n k ⟶ C =>
      F.toFun (PastingGlobe.rightCell n n k)) (pushout.inl_desc
        (PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
        (Globe.lift C (x 2) (hd 2)) (desc_condition C x hd hm))
  have ht := congrArg (fun F : Globe.category n ⟶ C => F.toFun Globe.Cell.top)
    (pushout.inr_desc (PastingGlobe.desc C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
      (Globe.lift C (x 2) (hd 2)) (desc_condition C x hd hm))
  fin_cases i
  · exact hl.trans (PastingGlobe.desc_left C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
  · exact hr.trans (PastingGlobe.desc_right C (x 0) (x 1) (hd 0) (hd 1) (hm 0))
  · exact ht

end
end Thomason.Construction.StrictOmegaCategory.TripleGlobe

end

section

/-! # The strict associativity diagram for three pasted globes

The two bracketings are literal strict functors from a binary pasting
into the actual three-globe parameter. Their universal composites agree
by strict associativity in that parameter.
-/

namespace Thomason.Construction.StrictOmegaCategory.TripleGlobe

open CategoryTheory

noncomputable section

variable (n k : ℕ) (hk : k < n)

def firstComposite : category n k :=
  (category n k).comp k (cell n k 0) (cell n k 1) (adjacent_matching n k 0)

def lastComposite : category n k :=
  (category n k).comp k (cell n k 1) (cell n k 2) (adjacent_matching n k 1)

theorem firstComposite_dimension (hk : k < n) : (category n k).DimensionLE n (firstComposite n k) :=
  (category n k).dimensionLE_comp hk (cell_dimension n k 0) (cell_dimension n k 1) _

theorem lastComposite_dimension (hk : k < n) : (category n k).DimensionLE n (lastComposite n k) :=
  (category n k).dimensionLE_comp hk (cell_dimension n k 1) (cell_dimension n k 2) _

theorem firstComposite_matching :
    (category n k).target k (firstComposite n k) = (category n k).source k (cell n k 2) :=
  ((category n k).target_comp k _ _ _).trans (adjacent_matching n k 1)

theorem lastComposite_matching :
    (category n k).target k (cell n k 0) = (category n k).source k (lastComposite n k) :=
  (adjacent_matching n k 0).trans ((category n k).source_comp k _ _ _).symm

/-- The inclusion of the second and third globe. -/
def rightPair : PastingGlobe.category n n k ⟶ category n k :=
  PastingGlobe.desc _ (cell n k 1) (cell n k 2)
    (cell_dimension n k 1) (cell_dimension n k 2) (adjacent_matching n k 1)

theorem rightPair_left :
    PastingGlobe.left n n k ≫ rightPair n k = inclusion n k 1 := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_left _ _ _ _ _ _

theorem rightPair_right :
    PastingGlobe.right n n k ≫ rightPair n k = inclusion n k 2 := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_right _ _ _ _ _ _

theorem pair_composite :
    (pair n k).toFun (PastingGlobe.composite n n k) = firstComposite n k :=
  (pair n k).map_comp k _ _ _ (adjacent_matching n k 0)

theorem rightPair_composite :
    (rightPair n k).toFun (PastingGlobe.composite n n k) = lastComposite n k :=
  PastingGlobe.desc_composite _ _ _ _ _ _

/-- The outer pair of the left-associated composite. -/
def leftBracket : PastingGlobe.category n n k ⟶ category n k :=
  PastingGlobe.desc _ (firstComposite n k) (cell n k 2)
    (firstComposite_dimension n k hk) (cell_dimension n k 2) (firstComposite_matching n k)

/-- The outer pair of the right-associated composite. -/
def rightBracket : PastingGlobe.category n n k ⟶ category n k :=
  PastingGlobe.desc _ (cell n k 0) (lastComposite n k)
    (cell_dimension n k 0) (lastComposite_dimension n k hk) (lastComposite_matching n k)

theorem leftBracket_left :
    PastingGlobe.left n n k ≫ leftBracket n k hk =
      GrayMapping.compositionGlobe n k hk ≫ pair n k := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_left _ _ _ _ _ _).trans (pair_composite n k).symm

theorem leftBracket_right :
    PastingGlobe.right n n k ≫ leftBracket n k hk = inclusion n k 2 := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_right _ _ _ _ _ _

theorem rightBracket_left :
    PastingGlobe.left n n k ≫ rightBracket n k hk = inclusion n k 0 := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_left _ _ _ _ _ _

theorem rightBracket_right :
    PastingGlobe.right n n k ≫ rightBracket n k hk =
      GrayMapping.compositionGlobe n k hk ≫ rightPair n k := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_right _ _ _ _ _ _).trans (rightPair_composite n k).symm

/-- Equality of the two actual universal composite maps. -/
theorem associativity_diagram :
    GrayMapping.compositionGlobe n k hk ≫ leftBracket n k hk =
      GrayMapping.compositionGlobe n k hk ≫ rightBracket n k hk := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_composite _ _ _ _ _ _).trans
    (((category n k).assoc k (cell n k 0) (cell n k 1) (cell n k 2)
      (adjacent_matching n k 0) (adjacent_matching n k 1)
      (firstComposite_matching n k) (lastComposite_matching n k)).trans
        (PastingGlobe.desc_composite _ _ _ _ _ _).symm)

end
end Thomason.Construction.StrictOmegaCategory.TripleGlobe

end

section

/-! # Associativity evaluated in a three-globe cylinder

This is the compatibility bridge between strict associativity of the
finite parameter and the concrete mapping composition. The only local
data is a map out of that actual parameter cylinder.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {D : StrictOmegaCategory.{0}} {n k : ℕ}

theorem composite_congr (hk : k < n)
    {f g f' g' : model.obj (Globe.category n) ⟶ D} (hf : f = f') (hg : g = g')
    (h : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (h' : model.map (Globe.faceMap true k n) ≫ f' = model.map (Globe.faceMap false k n) ≫ g') :
    composite hk f g h = composite hk f' g' h' := by
  subst f'
  subst g'
  rfl

/-- Evaluate any binary parameter when its two legs have already been identified. -/
theorem composite_evaluation_of_legs {C : StrictOmegaCategory.{0}} (hk : k < n)
    (p : PastingGlobe.category n n k ⟶ C) (u : model.obj C ⟶ D)
    (f g : model.obj (Globe.category n) ⟶ D)
    (hf : model.map (PastingGlobe.left n n k ≫ p) ≫ u = f)
    (hg : model.map (PastingGlobe.right n n k ≫ p) ≫ u = g)
    (h : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ g) :
    composite hk f g h = model.map (compositionGlobe n k hk ≫ p) ≫ u :=
  (composite_congr hk hf hg (evaluation_matching p u) h).symm.trans
    (composite_evaluation hk p u (evaluation_matching p u))

abbrev tripleEvaluation (u : model.obj (TripleGlobe.category n k) ⟶ D) (i : Fin 3) :
    model.obj (Globe.category n) ⟶ D := model.map (TripleGlobe.inclusion n k i) ≫ u

theorem triple_first_composite (hk : k < n)
    (u : model.obj (TripleGlobe.category n k) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 0 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 1) :
    composite hk (tripleEvaluation u 0) (tripleEvaluation u 1) h =
      model.map (compositionGlobe n k hk ≫ TripleGlobe.pair n k) ≫ u :=
  composite_evaluation hk (TripleGlobe.pair n k) u h

theorem triple_last_composite (hk : k < n)
    (u : model.obj (TripleGlobe.category n k) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 1 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 2) :
    composite hk (tripleEvaluation u 1) (tripleEvaluation u 2) h =
      model.map (compositionGlobe n k hk ≫ TripleGlobe.rightPair n k) ≫ u := by
  have hm := evaluation_matching (TripleGlobe.rightPair n k) u
  have he := composite_evaluation hk (TripleGlobe.rightPair n k) u hm
  have hf : model.map (PastingGlobe.left n n k ≫ TripleGlobe.rightPair n k) ≫ u =
      tripleEvaluation u 1 := congrArg (fun p => model.map p ≫ u) (TripleGlobe.rightPair_left n k)
  have hg : model.map (PastingGlobe.right n n k ≫ TripleGlobe.rightPair n k) ≫ u =
      tripleEvaluation u 2 := congrArg (fun p => model.map p ≫ u) (TripleGlobe.rightPair_right n k)
  exact (composite_congr hk hf hg hm h).symm.trans he

theorem triple_associativity (hk : k < n)
    (u : model.obj (TripleGlobe.category n k) ⟶ D)
    (h01 : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 0 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 1)
    (h12 : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 1 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 2)
    (hl : model.map (Globe.faceMap true k n) ≫
        composite hk (tripleEvaluation u 0) (tripleEvaluation u 1) h01 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 2)
    (hr : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 0 =
      model.map (Globe.faceMap false k n) ≫
        composite hk (tripleEvaluation u 1) (tripleEvaluation u 2) h12) :
    composite hk (composite hk (tripleEvaluation u 0) (tripleEvaluation u 1) h01)
        (tripleEvaluation u 2) hl =
      composite hk (tripleEvaluation u 0)
        (composite hk (tripleEvaluation u 1) (tripleEvaluation u 2) h12) hr := by
  have hml := evaluation_matching (TripleGlobe.leftBracket n k hk) u
  have hmr := evaluation_matching (TripleGlobe.rightBracket n k hk) u
  have heL := composite_evaluation hk (TripleGlobe.leftBracket n k hk) u hml
  have heR := composite_evaluation hk (TripleGlobe.rightBracket n k hk) u hmr
  have hL0 : model.map (PastingGlobe.left n n k ≫ TripleGlobe.leftBracket n k hk) ≫ u =
      composite hk (tripleEvaluation u 0) (tripleEvaluation u 1) h01 :=
    (congrArg (fun p => model.map p ≫ u) (TripleGlobe.leftBracket_left n k hk)).trans
      (triple_first_composite hk u h01).symm
  have hL1 : model.map (PastingGlobe.right n n k ≫ TripleGlobe.leftBracket n k hk) ≫ u =
      tripleEvaluation u 2 :=
    congrArg (fun p => model.map p ≫ u) (TripleGlobe.leftBracket_right n k hk)
  have hR0 : model.map (PastingGlobe.left n n k ≫ TripleGlobe.rightBracket n k hk) ≫ u =
      tripleEvaluation u 0 :=
    congrArg (fun p => model.map p ≫ u) (TripleGlobe.rightBracket_left n k hk)
  have hR1 : model.map (PastingGlobe.right n n k ≫ TripleGlobe.rightBracket n k hk) ≫ u =
      composite hk (tripleEvaluation u 1) (tripleEvaluation u 2) h12 :=
    (congrArg (fun p => model.map p ≫ u) (TripleGlobe.rightBracket_right n k hk)).trans
      (triple_last_composite hk u h12).symm
  exact (composite_congr hk hL0 hL1 hml hl).symm.trans
    (heL.trans ((congrArg (fun p => model.map p ≫ u)
      (TripleGlobe.associativity_diagram n k hk)).trans
        (heR.symm.trans (composite_congr hk hR0 hR1 hmr hr))))

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # Evaluation carries the strict grid interchange to mapping composition -/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {D : StrictOmegaCategory.{0}} {n k l : ℕ} {hkl : k < l}

abbrev gridEvaluation (u : model.obj (GridGlobe.category n k l hkl) ⟶ D) (b a : Bool) :
    model.obj (Globe.category n) ⟶ D := model.map (GridGlobe.inclusion n k l hkl b a) ≫ u

theorem grid_row_composite (hln : l < n)
    (u : model.obj (GridGlobe.category n k l hkl) ⟶ D) (b : Bool)
    (h : model.map (Globe.faceMap true k n) ≫ gridEvaluation u b false =
      model.map (Globe.faceMap false k n) ≫ gridEvaluation u b true) :
    composite (hkl.trans hln) (gridEvaluation u b false) (gridEvaluation u b true) h =
      model.map (compositionGlobe n k (hkl.trans hln) ≫ GridGlobe.row n k l hkl b) ≫ u :=
  composite_evaluation (hkl.trans hln) (GridGlobe.row n k l hkl b) u h

theorem grid_column_composite (hln : l < n)
    (u : model.obj (GridGlobe.category n k l hkl) ⟶ D) (a : Bool)
    (h : model.map (Globe.faceMap true l n) ≫ gridEvaluation u false a =
      model.map (Globe.faceMap false l n) ≫ gridEvaluation u true a) :
    composite hln (gridEvaluation u false a) (gridEvaluation u true a) h =
      model.map (compositionGlobe n l hln ≫ GridGlobe.column n k l hkl a) ≫ u :=
  composite_evaluation_of_legs hln (GridGlobe.column n k l hkl a) u _ _
    (congrArg (fun p => model.map p ≫ u) (GridGlobe.column_left n k l hkl a))
    (congrArg (fun p => model.map p ≫ u) (GridGlobe.column_right n k l hkl a)) h

/-- Any actual map from the grid cylinder respects strict interchange. -/
theorem grid_interchange (hln : l < n)
    (u : model.obj (GridGlobe.category n k l hkl) ⟶ D)
    (ht : model.map (Globe.faceMap true k n) ≫ gridEvaluation u false false =
      model.map (Globe.faceMap false k n) ≫ gridEvaluation u false true)
    (hb : model.map (Globe.faceMap true k n) ≫ gridEvaluation u true false =
      model.map (Globe.faceMap false k n) ≫ gridEvaluation u true true)
    (hl : model.map (Globe.faceMap true l n) ≫ gridEvaluation u false false =
      model.map (Globe.faceMap false l n) ≫ gridEvaluation u true false)
    (hr : model.map (Globe.faceMap true l n) ≫ gridEvaluation u false true =
      model.map (Globe.faceMap false l n) ≫ gridEvaluation u true true)
    (hv : model.map (Globe.faceMap true l n) ≫
        composite (hkl.trans hln) (gridEvaluation u false false) (gridEvaluation u false true) ht =
      model.map (Globe.faceMap false l n) ≫
        composite (hkl.trans hln) (gridEvaluation u true false) (gridEvaluation u true true) hb)
    (hh : model.map (Globe.faceMap true k n) ≫
        composite hln (gridEvaluation u false false) (gridEvaluation u true false) hl =
      model.map (Globe.faceMap false k n) ≫
        composite hln (gridEvaluation u false true) (gridEvaluation u true true) hr) :
    composite hln
        (composite (hkl.trans hln) (gridEvaluation u false false) (gridEvaluation u false true) ht)
        (composite (hkl.trans hln) (gridEvaluation u true false) (gridEvaluation u true true) hb) hv =
      composite (hkl.trans hln)
        (composite hln (gridEvaluation u false false) (gridEvaluation u true false) hl)
        (composite hln (gridEvaluation u false true) (gridEvaluation u true true) hr) hh := by
  have hv0 := (congrArg (fun p => model.map p ≫ u)
    (GridGlobe.verticalOuter_left n k l hkl hln)).trans (grid_row_composite hln u false ht).symm
  have hv1 := (congrArg (fun p => model.map p ≫ u)
    (GridGlobe.verticalOuter_right n k l hkl hln)).trans (grid_row_composite hln u true hb).symm
  have hh0 := (congrArg (fun p => model.map p ≫ u)
    (GridGlobe.horizontalOuter_left n k l hkl hln)).trans (grid_column_composite hln u false hl).symm
  have hh1 := (congrArg (fun p => model.map p ≫ u)
    (GridGlobe.horizontalOuter_right n k l hkl hln)).trans (grid_column_composite hln u true hr).symm
  exact (composite_evaluation_of_legs hln (GridGlobe.verticalOuter n k l hkl hln)
    u _ _ hv0 hv1 hv).trans
      ((congrArg (fun p => model.map p ≫ u) (GridGlobe.interchange_diagram n k l hkl hln)).trans
        (composite_evaluation_of_legs (hkl.trans hln) (GridGlobe.horizontalOuter n k l hkl hln)
          u _ _ hh0 hh1 hh).symm)

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

end OAI
