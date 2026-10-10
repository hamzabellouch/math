import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Simplicial.AcyclicKanSimplexLifting
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSupportInclusion
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionImageLattice
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionBaseChange
import OAI.CategoryTheory.Thomason.Simplicial.KanFinitePosetExtension
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialApproximation
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity
import OAI.CategoryTheory.Thomason.Transfer.KanQuillenLiftingReduction

namespace OAI

section

/-! # Detecting finite simplicial homotopies in a Kan realization

A continuous extension over a parameter that embeds in a simplex gives an
exact simplicial extension. Applying this to the two ends of the actual
simplicial cylinder detects homotopies in the original Kan target.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Transport the simplex-subcomplex extension theorem along the actual
range isomorphisms of a pair of monomorphisms. -/
theorem kan_extension_of_realization_extension_of_simplex_mono
    {A B X : SSet.{0}} [SSet.KanComplex X] {n : ℕ}
    (e : B ⟶ (Δ[n] : SSet.{0})) [Mono e] (i : A ⟶ B) [Mono i]
    (a : A ⟶ X) (b : SSet.toTop.obj B ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map i ≫ b = SSet.toTop.map a) :
    ∃ d : B ⟶ X, i ≫ d = a := by
  let R := SSet.Subcomplex.range e
  let S := SSet.Subcomplex.range (i ≫ e)
  have hSR : S ≤ R := by
    intro k x hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨i.app k y, hy⟩
  let qA : A ≅ S.toSSet := asIso (SSet.Subcomplex.toRange (i ≫ e))
  let qB : B ≅ R.toSSet := asIso (SSet.Subcomplex.toRange e)
  let j := SSet.Subcomplex.homOfLE hSR
  have hij : qA.hom ≫ j = i ≫ qB.hom := by
    apply (cancel_mono R.ι).mp
    change (SSet.Subcomplex.toRange (i ≫ e) ≫ j) ≫ R.ι =
      (i ≫ SSet.Subcomplex.toRange e) ≫ R.ι
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι, Category.assoc, SSet.Subcomplex.toRange_ι]
  have hj : j ≫ qB.inv = qA.inv ≫ i := by
    calc
      j ≫ qB.inv = qA.inv ≫ ((qA.hom ≫ j) ≫ qB.inv) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = qA.inv ≫ ((i ≫ qB.hom) ≫ qB.inv) := by rw [hij]
      _ = qA.inv ≫ i := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h' : SSet.toTop.map j ≫ (SSet.toTop.map qB.inv ≫ b) =
      SSet.toTop.map (qA.inv ≫ a) := by
    rw [← Category.assoc, ← SSet.toTop.map_comp, hj, SSet.toTop.map_comp,
      Category.assoc, h, ← SSet.toTop.map_comp]
  obtain ⟨d, hd⟩ := kan_extension_of_subcomplex_realization_extension
    S R hSR (qA.inv ≫ a) (SSet.toTop.map qB.inv ≫ b) h'
  refine ⟨qB.hom ≫ d, ?_⟩
  rw [← Category.assoc, ← hij, Category.assoc, hd, ← Category.assoc,
    qA.hom_inv_id, Category.id_comp]

/-- A finite-poset parameter is an actual simplex subcomplex after a
finite linear extension, so the same exact extension theorem applies. -/
theorem kan_extension_of_finitePoset_realization_extension
    (P : Type) [PartialOrder P] [Finite P] [Nonempty P]
    {A X : SSet.{0}} [SSet.KanComplex X]
    (i : A ⟶ nerve P) [Mono i] (a : A ⟶ X)
    (b : SSet.toTop.obj (nerve P) ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map i ≫ b = SSet.toTop.map a) :
    ∃ d : nerve P ⟶ X, i ≫ d = a := by
  obtain ⟨n, e, he⟩ := finitePoset_nerve_simplex_embedding P
  exact kan_extension_of_realization_extension_of_simplex_mono e i a b h

theorem simplicialCylinder_inclusion_comp {K X : SSet.{0}} (a : K ⊗ Δ[1] ⟶ X) :
    SimplicialCylinder.inclusion K ≫ a =
      SimplicialCylinder.desc (SSet.ι₀ ≫ a) (SSet.ι₁ ≫ a) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  cases x <;> rfl

theorem simplicialCylinder_desc_comp {K X Y : SSet.{0}}
    (f g : K ⟶ X) (a : X ⟶ Y) :
    SimplicialCylinder.desc f g ≫ a = SimplicialCylinder.desc (f ≫ a) (g ≫ a) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  cases x <;> rfl

def realizedHomotopyCylinder {K X : SSet.{0}} {f g : K ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    SSet.toTop.obj (K ⊗ Δ[1]) ⟶ SSet.toTop.obj X :=
  SSet.toTop.map (realizationUnitHomotopy H).h ≫
    sSetTopAdj.counit.app (SSet.toTop.obj X)

/-- The singular homotopy can be evaluated on the actual simplicial
cylinder, with the two original realized endpoint maps exact. -/
theorem realizedHomotopyCylinder_ends {K X : SSet.{0}} {f g : K ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    SSet.toTop.map (SimplicialCylinder.inclusion K) ≫ realizedHomotopyCylinder H =
      SSet.toTop.map (SimplicialCylinder.desc f g) := by
  let h := realizationUnitHomotopy H
  have he : SimplicialCylinder.inclusion K ≫ h.h =
      SimplicialCylinder.desc f g ≫ sSetTopAdj.unit.app X := by
    rw [simplicialCylinder_inclusion_comp, h.h₀, h.h₁, simplicialCylinder_desc_comp]
  change SSet.toTop.map (SimplicialCylinder.inclusion K) ≫
    (SSet.toTop.map h.h ≫ sSetTopAdj.counit.app (SSet.toTop.obj X)) = _
  rw [← Category.assoc, ← SSet.toTop.map_comp, he, SSet.toTop.map_comp,
    Category.assoc, sSetTopAdj.left_triangle_components, Category.comp_id]

theorem realizedHomotopy_cylinder_extension {K X : SSet.{0}} {f g : K ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    ∃ b : SSet.toTop.obj (K ⊗ Δ[1]) ⟶ SSet.toTop.obj X,
      SSet.toTop.map (SimplicialCylinder.inclusion K) ≫ b =
        SSet.toTop.map (SimplicialCylinder.desc f g) :=
  ⟨realizedHomotopyCylinder H, realizedHomotopyCylinder_ends H⟩

/-- The same evaluated cylinder retains stationarity on the whole
realized image of a prescribed simplicial subobject. -/
theorem realizedHomotopyCylinder_stationary {A K X : SSet.{0}} {f g : K ⟶ X}
    (i : A ⟶ K)
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom)
    (hH : ∀ (t : unitInterval) (x : SSet.toTop.obj A),
      H (t, (SSet.toTop.map i).hom x) =
        (SSet.toTop.map f).hom ((SSet.toTop.map i).hom x)) :
    SSet.toTop.map (i ▷ Δ[1]) ≫ realizedHomotopyCylinder H =
      SSet.toTop.map (fst A Δ[1] ≫ i ≫ f) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨⟨x, t⟩, rfl⟩ := RealizedCylinder.comparison_surjective A z
  unfold realizedHomotopyCylinder
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  change evaluateSingularCylinder
      (i ▷ Δ[1] ≫ (realizationUnitHomotopy H).h) (t, x) = _
  rw [← evaluateSingularCylinder_naturality, realizationUnitHomotopy_evaluate, hH]
  simp only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [RealizedCylinder.comparison_first]

theorem cylinder_simplex_embedding {K : SSet.{0}} {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] :
    ∃ (m : ℕ) (j : K ⊗ Δ[1] ⟶ (Δ[m] : SSet.{0})), Mono j := by
  let P := ULift.{0} (Fin (n+1) × Fin 2)
  obtain ⟨m, j, hj⟩ := finitePoset_nerve_simplex_embedding P
  let q : (Δ[n] : SSet.{0}) ⊗ Δ[1] ⟶ nerve P :=
    (SSet.prodStdSimplex.isoNerve n 1).hom
  have : IsIso q := inferInstanceAs (IsIso (SSet.prodStdSimplex.isoNerve n 1).hom)
  have : Mono (e ▷ (Δ[1] : SSet.{0})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro k
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y h
    have hh : (e.app k x.1, x.2) = (e.app k y.1, y.2) := h
    apply Prod.ext
    · exact (CategoryTheory.mono_iff_injective (e.app k)).mp inferInstance
        (congrArg Prod.fst hh)
    · exact congrArg (fun z : (Δ[n] : SSet.{0}).obj k × (Δ[1] : SSet.{0}).obj k =>
        z.2) hh
  exact ⟨m, (e ▷ Δ[1]) ≫ q ≫ j, inferInstance⟩

/-- A continuous homotopy between two simplicial maps into a Kan complex
is detected by a genuine simplicial homotopy for every simplex subcomplex
parameter, including every finite-poset nerve. -/
theorem kan_homotopy_of_realization_homotopy_of_simplex_mono
    {K X : SSet.{0}} [SSet.KanComplex X] {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] {f g : K ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    Nonempty (SSet.Homotopy f g) := by
  obtain ⟨m, j, hj⟩ := cylinder_simplex_embedding e
  obtain ⟨b, hb⟩ := realizedHomotopy_cylinder_extension H
  obtain ⟨a, ha⟩ := kan_extension_of_realization_extension_of_simplex_mono
    j (SimplicialCylinder.inclusion K) (SimplicialCylinder.desc f g) b hb
  refine ⟨{ h := a, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · change SSet.ι₀ ≫ a = f
    have h := congrArg (SimplicialCylinder.zero K ≫ ·) ha
    simpa only [← Category.assoc, SimplicialCylinder.zero_inclusion,
      SimplicialCylinder.zero_desc] using h
  · change SSet.ι₁ ≫ a = g
    have h := congrArg (SimplicialCylinder.one K ≫ ·) ha
    simpa only [← Category.assoc, SimplicialCylinder.one_inclusion,
      SimplicialCylinder.one_desc] using h
  · apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

theorem kan_finitePoset_homotopy_iff (P : Type) [PartialOrder P] [Finite P] [Nonempty P]
    {X : SSet.{0}} [SSet.KanComplex X] (f g : nerve P ⟶ X) :
    Nonempty (SSet.Homotopy f g) ↔
      Nonempty ((SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨RealizedCylinder.homotopy H⟩
  · rintro ⟨H⟩
    obtain ⟨n, e, he⟩ := finitePoset_nerve_simplex_embedding P
    exact kan_homotopy_of_realization_homotopy_of_simplex_mono e H

end

end Thomason.Construction

end

section

/-! # Detecting relative homotopies in a Kan realization

The union of the cylinder's ends and its prescribed side is an actual
subcomplex. Exact extension across that subcomplex retains stationarity
on the whole original side.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

theorem intervalBoundaryFamily_comp {K X Y : SSet.{0}}
    (f g : K ⟶ X) (a : X ⟶ Y) :
    intervalBoundaryFamily f g ≫ a = intervalBoundaryFamily (f ≫ a) (g ≫ a) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro z
  change a.app k (if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0 then
    f.app k z.1 else g.app k z.1) =
    if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0 then
      a.app k (f.app k z.1) else a.app k (g.app k z.1)
  split_ifs <;> rfl

theorem intervalBoundaryFamily_self {K X : SSet.{0}} (f : K ⟶ X) :
    intervalBoundaryFamily f f = fst K (SSet.boundary 1 : SSet.{0}) ≫ f := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro z
  change (if (SSet.stdSimplex.objEquiv z.2.val).toOrderHom 0 = 0 then
    f.app k z.1 else f.app k z.1) = f.app k z.1
  simp only [ite_self]

theorem realizedHomotopyCylinder_intervalBoundary {K X : SSet.{0}} {f g : K ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫ realizedHomotopyCylinder H =
      SSet.toTop.map (intervalBoundaryFamily f g) := by
  let h := realizationUnitHomotopy H
  have he : K ◁ (SSet.boundary 1).ι ≫ h.h =
      intervalBoundaryFamily f g ≫ sSetTopAdj.unit.app X := by
    rw [intervalBoundaryFamily_restriction, h.h₀, h.h₁, intervalBoundaryFamily_comp]
  change SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫
    (SSet.toTop.map h.h ≫ sSetTopAdj.counit.app (SSet.toTop.obj X)) = _
  rw [← Category.assoc, ← SSet.toTop.map_comp, he, SSet.toTop.map_comp,
    Category.assoc, sSetTopAdj.left_triangle_components, Category.comp_id]

/-- Relative continuous homotopy gives a simplicial homotopy which fixes
the prescribed subcomplex exactly. -/
theorem kan_homotopy_of_realization_homotopy_rel
    {K X : SSet.{0}} [SSet.KanComplex X] {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] (A : K.Subcomplex)
    {f g : K ⟶ X} (hfg : A.ι ≫ f = A.ι ≫ g)
    (H : (SSet.toTop.map f).hom.HomotopyRel (SSet.toTop.map g).hom
      (Set.range (SSet.toTop.map A.ι).hom)) :
    ∃ h : SSet.Homotopy f g,
      A.ι ▷ Δ[1] ≫ h.h = fst A.toSSet Δ[1] ≫ A.ι ≫ f := by
  let T : (Δ[1] : SSet.{0}).Subcomplex := SSet.boundary 1
  let U := A.unionProd T
  let side := fst A.toSSet (Δ[1] : SSet.{0}) ≫ A.ι ≫ f
  let ends := intervalBoundaryFamily f g
  let sq := SSet.Subcomplex.unionProd.isPushout A T
  have hc : A.ι ▷ T.toSSet ≫ ends = A.toSSet ◁ T.ι ≫ side := by
    change A.ι ▷ (SSet.boundary 1 : SSet.{0}) ≫ intervalBoundaryFamily f g =
      A.toSSet ◁ (SSet.boundary 1).ι ≫ (fst A.toSSet Δ[1] ≫ A.ι ≫ f)
    rw [intervalBoundaryFamily_naturality, ← hfg, intervalBoundaryFamily_self]
    simp only [← Category.assoc, whiskerLeft_fst]
  let a : U.toSSet ⟶ X := sq.desc ends side hc
  have hleft : SSet.Subcomplex.unionProd.ι₁ A T ≫ a = ends :=
    sq.inl_desc ends side hc
  have hright : SSet.Subcomplex.unionProd.ι₂ A T ≫ a = side :=
    sq.inr_desc ends side hc
  let b := realizedHomotopyCylinder H.toHomotopy
  have hbside : SSet.toTop.map (A.ι ▷ Δ[1]) ≫ b = SSet.toTop.map side := by
    apply realizedHomotopyCylinder_stationary A.ι H.toHomotopy
    intro t x
    exact H.prop t _ ⟨x, rfl⟩
  have hbends : SSet.toTop.map (K ◁ T.ι) ≫ b = SSet.toTop.map ends :=
    realizedHomotopyCylinder_intervalBoundary H.toHomotopy
  have hb : SSet.toTop.map U.ι ≫ b = SSet.toTop.map a := by
    apply (sq.map SSet.toTop).hom_ext
    · rw [← Category.assoc, ← SSet.toTop.map_comp,
        SSet.Subcomplex.unionProd.ι₁_ι, hbends,
        ← SSet.toTop.map_comp, hleft]
    · rw [← Category.assoc, ← SSet.toTop.map_comp,
        SSet.Subcomplex.unionProd.ι₂_ι, hbside,
        ← SSet.toTop.map_comp, hright]
  obtain ⟨m, j, hj⟩ := cylinder_simplex_embedding e
  obtain ⟨d, hd⟩ := kan_extension_of_realization_extension_of_simplex_mono j U.ι a b hb
  have hdends : K ◁ (SSet.boundary 1).ι ≫ d = intervalBoundaryFamily f g := by
    rw [← SSet.Subcomplex.unionProd.ι₁_ι A T, Category.assoc, hd, hleft]
  obtain ⟨h₀, h₁⟩ := intervalBoundaryFamily_endpoints d f g hdends
  have hdside : A.ι ▷ Δ[1] ≫ d = side := by
    rw [← SSet.Subcomplex.unionProd.ι₂_ι A T, Category.assoc, hd, hright]
  let hd' : SSet.Homotopy f g := {
    h := d
    h₀ := h₀
    h₁ := h₁
    rel := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  exact ⟨hd', hdside⟩

end

end Thomason.Construction

end

section

/-! # Realization homotopy classes with a Kan target

Finite subdivision is removed with its actual comparison homotopy.
Consequently every continuous map from a finite-poset realization into
a Kan realization is represented by an original simplicial map.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

noncomputable section

namespace SubdivisionBarycentric

theorem iteratedChainRealization_homotopy (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    Nonempty ((iteratedChainRealization P r).Homotopy
      (SSet.toTop.map (nerveMap (RelativeLabelCarrier.greatestVertex P r).monotone.functor)).hom) := by
  induction r with
  | zero =>
      refine ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id _)).cast rfl ?_⟩
      change ContinuousMap.id _ =
        (SSet.toTop.map (nerveMap (OrderHom.id : P →o P).monotone.functor)).hom
      have hi : nerveMap (OrderHom.id : P →o P).monotone.functor = 𝟙 (nerve P) := rfl
      rw [hi, SSet.toTop.map_id]
      rfl
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      obtain ⟨H⟩ := ih
      have H' := H.comp (chainRealizationMapHomotopy (iteratedChainPoset P r))
      refine ⟨H'.cast rfl ?_⟩
      change (SSet.toTop.map (nerveMap
        (RelativeLabelCarrier.greatestVertex P r).monotone.functor)).hom.comp
        (SSet.toTop.map (nerveMap
          (ChainLabelApproximation.greatestHom (P := iteratedChainPoset P r)).monotone.functor)).hom = _
      rw [← TopCat.hom_comp, ← SSet.toTop.map_comp, ← orderNerveMap_comp]
      rfl

theorem exists_iteratedSubdivision_descent_homotopy (P : PartOrd.{0}) [Finite P]
    (X : SSet.{0}) [SSet.KanComplex X] (r : ℕ)
    (f : (iteratedSubdivision r).obj (nerve P) ⟶ X) :
    ∃ g : nerve P ⟶ X,
      Nonempty ((SSet.toTop.map (iteratedLastVertex (nerve P) r ≫ g)).hom.Homotopy
        (SSet.toTop.map f).hom) := by
  induction r with
  | zero =>
      refine ⟨f, ⟨(ContinuousMap.Homotopy.refl (SSet.toTop.map f).hom).cast ?_ rfl⟩⟩
      change (SSet.toTop.map f).hom = (SSet.toTop.map ((𝟙 _) ≫ f)).hom
      rw [Category.id_comp]
  | succ r ih =>
      obtain ⟨f', ⟨H⟩, _⟩ := exists_iteratedSubdivision_step_descent P r X f
      obtain ⟨g, ⟨G⟩⟩ := ih f'
      let l := lastVertex.app ((iteratedSubdivision r).obj (nerve P))
      have G' := G.comp (ContinuousMap.Homotopy.refl (SSet.toTop.map l).hom)
      have h₀ : (SSet.toTop.map (iteratedLastVertex (nerve P) r ≫ g)).hom.comp
          (SSet.toTop.map l).hom =
          (SSet.toTop.map (iteratedLastVertex (nerve P) (r+1) ≫ g)).hom := by
        rw [← TopCat.hom_comp, ← SSet.toTop.map_comp]
        exact congrArg (fun k => (SSet.toTop.map k).hom)
          (Category.assoc l (iteratedLastVertex (nerve P) r) g).symm
      have h₁ : (SSet.toTop.map f').hom.comp (SSet.toTop.map l).hom =
          (SSet.toTop.map (l ≫ f')).hom := by
        rw [← TopCat.hom_comp, ← SSet.toTop.map_comp]
      exact ⟨g, ⟨(G'.cast h₀ h₁).trans (RealizedCylinder.homotopy H)⟩⟩

end SubdivisionBarycentric

/-- A weak equivalence of actual realizations reflects continuous
homotopies after precomposition. -/
theorem realization_homotopy_of_precomp {A B : SSet.{0}} (u : A ⟶ B)
    (hu : realizationWeakEquivalences u) {T : TopCat.{0}}
    (f g : SSet.toTop.obj B ⟶ T)
    (H : (f.hom.comp (SSet.toTop.map u).hom).Homotopy
      (g.hom.comp (SSet.toTop.map u).hom)) :
    Nonempty (f.hom.Homotopy g.hom) := by
  let e := realizationWhiteheadEquiv (SSet.toTop.map u) hu
  let R := Classical.choice e.right_inv
  have H₀ := (ContinuousMap.Homotopy.refl f.hom).comp R
  have H₁ := H.comp (ContinuousMap.Homotopy.refl e.invFun)
  have H₂ := (ContinuousMap.Homotopy.refl g.hom).comp R
  exact ⟨(H₀.cast (by ext; rfl) (by ext; rfl)).symm.trans
    (H₁.trans (H₂.cast (by ext; rfl) (by ext; rfl)))⟩

/-- No subdivision remains in the source, and the comparison is a
homotopy to the given continuous map in the original Kan realization. -/
theorem exists_kan_realization_approximation (P : PartOrd.{0}) [Fintype P]
    (X : SSet.{0}) [SSet.KanComplex X]
    (F : C(SSet.toTop.obj (nerve P), SSet.toTop.obj X)) :
    ∃ g : nerve P ⟶ X, Nonempty (F.Homotopy (SSet.toTop.map g).hom) := by
  obtain ⟨r, f, ⟨H⟩⟩ := SubdivisionBarycentric.exists_simplicial_approximation P X F
  let e := iteratedSubdivisionNerveIso P (r+1)
  let l := iteratedLastVertex (nerve P) (r+1)
  obtain ⟨g, ⟨G⟩⟩ := SubdivisionBarycentric.exists_iteratedSubdivision_descent_homotopy
    P X (r+1) (e.hom ≫ f)
  obtain ⟨B⟩ := SubdivisionBarycentric.iteratedChainRealization_homotopy P (r+1)
  let a := (SSet.toTop.map e.hom).hom
  have H' := H.comp (ContinuousMap.Homotopy.refl a)
  have B' := ((ContinuousMap.Homotopy.refl F).comp B).comp
    (ContinuousMap.Homotopy.refl a)
  have hlast : (SSet.toTop.map (nerveMap
      (RelativeLabelCarrier.greatestVertex P (r+1)).monotone.functor)).hom.comp a =
      (SSet.toTop.map l).hom := by
    rw [← TopCat.hom_comp, ← SSet.toTop.map_comp,
      RelativeLabelCarrier.greatestVertex_lastVertex]
  have hb : Nonempty ((F.comp (SSet.toTop.map l).hom).Homotopy
      (SSet.toTop.map (e.hom ≫ f)).hom) := by
    refine ⟨(B'.symm.trans H').cast ?_ ?_⟩
    · rw [ContinuousMap.comp_assoc, hlast]
    · exact congrArg TopCat.Hom.hom (SSet.toTop.map_comp e.hom f).symm
  obtain ⟨hb⟩ := hb
  apply Exists.intro g
  apply realization_homotopy_of_precomp l (iteratedLastVertex_weak _ _)
    (TopCat.ofHom F) (SSet.toTop.map g)
  have h := hb.trans G.symm
  refine h.cast rfl ?_
  rw [SSet.toTop.map_comp]
  rfl

end

end Thomason.Construction

end

section

/-! # Exact Kan lifts from relative realization homotopies

A relative continuous homotopy of the projection of a simplicial map can
be made simplicial and then lifted. The new endpoint has the required
projection and retains the original subcomplex exactly.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Exactify a relative lift when the projection comparison is an actual
continuous homotopy fixing the prescribed subcomplex. -/
theorem exactify_realization_relative_lift
    {K E B : SSet.{0}} [SSet.KanComplex B] {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] (A : K.Subcomplex)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (d : K ⟶ E) (b : K ⟶ B)
    (hdb : A.ι ≫ (d ≫ p) = A.ι ≫ b)
    (H : (SSet.toTop.map (d ≫ p)).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map A.ι).hom)) :
    ∃ l : K ⟶ E, A.ι ≫ l = A.ι ≫ d ∧ l ≫ p = b := by
  obtain ⟨s, hs⟩ := kan_homotopy_of_realization_homotopy_rel e A hdb H
  apply exactify_simplicial_relative_lift A.ι p (A.ι ≫ d) b d rfl s
  simpa only [Category.assoc] using hs

/-- The exactification can itself be chosen with a stationary simplicial
homotopy from the initial map. In particular it preserves the actual
realization weak-equivalence test. -/
theorem exists_kan_stationary_lift_of_realization_homotopy
    {K E B : SSet.{0}} [SSet.KanComplex B] {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] (A : K.Subcomplex)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (d : K ⟶ E) (b : K ⟶ B)
    (hdb : A.ι ≫ (d ≫ p) = A.ι ≫ b)
    (H : (SSet.toTop.map (d ≫ p)).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map A.ι).hom)) :
    ∃ (l : K ⟶ E) (s : SSet.Homotopy d l),
      A.ι ≫ l = A.ι ≫ d ∧ l ≫ p = b ∧
      A.ι ▷ Δ[1] ≫ s.h = fst A.toSSet Δ[1] ≫ A.ι ≫ d ∧
      Nonempty ((SSet.toTop.map d).hom.HomotopyRel (SSet.toTop.map l).hom
        (Set.range (SSet.toTop.map A.ι).hom)) ∧
      (realizationWeakEquivalences d ↔ realizationWeakEquivalences l) := by
  obtain ⟨t, ht⟩ := kan_homotopy_of_realization_homotopy_rel e A hdb H
  obtain ⟨l, s, hp, hs, hr, hw⟩ :=
    exists_kan_stationary_lift A.ι p d t (by simpa only [Category.assoc] using ht)
  refine ⟨l, s, ?_, hp, hs, hr, hw⟩
  let sh : K ⊗ (Δ[1] : SSet.{0}) ⟶ E := s.h
  have hs₁ : SSet.ι₁ ≫ sh = l := s.h₁
  calc
    A.ι ≫ l = A.ι ≫ (SSet.ι₁ ≫ sh) := congrArg (A.ι ≫ ·) hs₁.symm
    _ = (A.ι ≫ SSet.ι₁) ≫ sh := (Category.assoc _ _ _).symm
    _ = (SSet.ι₁ ≫ A.ι ▷ Δ[1]) ≫ sh :=
      congrArg (fun q => q ≫ sh) (SSet.ι₁_comp A.ι).symm
    _ = SSet.ι₁ ≫ (A.ι ▷ Δ[1] ≫ sh) := Category.assoc _ _ _
    _ = SSet.ι₁ ≫ (fst A.toSSet Δ[1] ≫ A.ι ≫ d) := congrArg (SSet.ι₁ ≫ ·) hs
    _ = A.ι ≫ d := by rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]

end

end Thomason.Construction

end

section

/-! # Exactification along arbitrary simplicial monomorphisms -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The relative realization exactification theorem applies to any
monomorphism into a simplex subcomplex, using its actual range. -/
theorem exactify_realization_relative_lift_mono
    {A K E B : SSet.{0}} [SSet.KanComplex B] {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{0})) [Mono e] (i : A ⟶ K) [Mono i]
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (d : K ⟶ E) (b : K ⟶ B)
    (hdb : i ≫ (d ≫ p) = i ≫ b)
    (H : (SSet.toTop.map (d ≫ p)).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map i).hom)) :
    ∃ l : K ⟶ E, i ≫ l = i ≫ d ∧ l ≫ p = b := by
  let R := SSet.Subcomplex.range i
  let q : A ⟶ R.toSSet := SSet.Subcomplex.toRange i
  let r : R.toSSet ⟶ A := inv q
  have hq : q ≫ R.ι = i := SSet.Subcomplex.toRange_ι i
  have hr : r ≫ i = R.ι := by
    rw [← hq, ← Category.assoc]
    change (inv q ≫ q) ≫ R.ι = R.ι
    rw [IsIso.inv_hom_id, Category.id_comp]
  have hR : R.ι ≫ (d ≫ p) = R.ι ≫ b := by
    apply (cancel_epi q).mp
    simpa only [← Category.assoc, hq] using hdb
  let HR : (SSet.toTop.map (d ≫ p)).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map R.ι).hom) := {
    toHomotopy := H.toHomotopy
    prop' := by
      intro t x hx
      apply H.prop t
      obtain ⟨z, rfl⟩ := hx
      refine ⟨(SSet.toTop.map r).hom z, ?_⟩
      have hz := congrArg (fun f => (SSet.toTop.map f).hom z) hr
      rw [SSet.toTop.map_comp] at hz
      exact hz }
  obtain ⟨l, hl, hp⟩ := exactify_realization_relative_lift e R p d b hR HR
  refine ⟨l, ?_, hp⟩
  calc
    i ≫ l = q ≫ (R.ι ≫ l) := by rw [← Category.assoc, hq]
    _ = q ≫ (R.ι ≫ d) := congrArg (q ≫ ·) hl
    _ = i ≫ d := by rw [← Category.assoc, hq]

end

end Thomason.Construction

end

section

/-! # Finite tests for weak equivalences between Kan complexes

The actual realization weak test gives surjectivity and injectivity on
finite-poset homotopy classes. For a Kan fibration, the surjectivity
comparison can be lifted to give an exact map over the prescribed base.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open SSet.modelCategoryQuillen

noncomputable section

theorem kan_weak_map_surjective_homotopy
    (P : PartOrd.{0}) [Fintype P] [Nonempty P]
    {E B : SSet.{0}} [SSet.KanComplex E] [SSet.KanComplex B]
    (p : E ⟶ B) (hp : realizationWeakEquivalences p) (b : nerve P ⟶ B) :
    ∃ a : nerve P ⟶ E, Nonempty (SSet.Homotopy (a ≫ p) b) := by
  let e := realizationWhiteheadEquiv (SSet.toTop.map p) hp
  let F := e.invFun.comp (SSet.toTop.map b).hom
  obtain ⟨a, ⟨H⟩⟩ := exists_kan_realization_approximation P E F
  have H₀ := (ContinuousMap.Homotopy.refl (SSet.toTop.map p).hom).comp H.symm
  have H₁ := (Classical.choice e.right_inv).comp
    (ContinuousMap.Homotopy.refl (SSet.toTop.map b).hom)
  have h : (SSet.toTop.map (a ≫ p)).hom.Homotopy (SSet.toTop.map b).hom := by
    refine (H₀.trans (H₁.cast (by ext; rfl) (by ext; rfl))).cast ?_ rfl
    exact congrArg TopCat.Hom.hom (SSet.toTop.map_comp a p).symm
  exact ⟨a, (kan_finitePoset_homotopy_iff P (a ≫ p) b).mpr ⟨h⟩⟩

theorem kan_weak_map_reflects_homotopy
    (P : PartOrd.{0}) [Finite P] [Nonempty P]
    {E B : SSet.{0}} [SSet.KanComplex E]
    (p : E ⟶ B) (hp : realizationWeakEquivalences p)
    (f g : nerve P ⟶ E) (H : SSet.Homotopy (f ≫ p) (g ≫ p)) :
    Nonempty (SSet.Homotopy f g) := by
  let e := realizationWhiteheadEquiv (SSet.toTop.map p) hp
  let R := Classical.choice e.left_inv
  have H₀ := R.comp (ContinuousMap.Homotopy.refl (SSet.toTop.map f).hom)
  have H₁ := (ContinuousMap.Homotopy.refl e.invFun).comp (RealizedCylinder.homotopy H)
  have H₂ := R.comp (ContinuousMap.Homotopy.refl (SSet.toTop.map g).hom)
  have h : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom := by
    have hf : e.invFun.comp (SSet.toTop.map (f ≫ p)).hom =
        (e.invFun.comp e.toFun).comp (SSet.toTop.map f).hom := by
      rw [SSet.toTop.map_comp]
      rfl
    have hg : e.invFun.comp (SSet.toTop.map (g ≫ p)).hom =
        (e.invFun.comp e.toFun).comp (SSet.toTop.map g).hom := by
      rw [SSet.toTop.map_comp]
      rfl
    exact (H₀.cast rfl (by ext; rfl)).symm.trans
      ((H₁.cast hf hg).trans (H₂.cast rfl (by ext; rfl)))
  exact (kan_finitePoset_homotopy_iff P f g).mpr ⟨h⟩

/-- This lifts the base map exactly; no boundary condition is asserted
by this intermediate theorem. -/
theorem kan_weak_fibration_lift_finitePoset
    (P : PartOrd.{0}) [Fintype P] [Nonempty P]
    {E B : SSet.{0}} [SSet.KanComplex E] [SSet.KanComplex B]
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : nerve P ⟶ B) :
    ∃ a : nerve P ⟶ E, a ≫ p = b := by
  obtain ⟨a, ⟨H⟩⟩ := kan_weak_map_surjective_homotopy P p hp b
  let : HasLiftingProperty (SSet.ι₀ (X := nerve P)) p :=
    anodyne_iota_zero (nerve P) p
      ((SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance)
  let sq : CommSq a (SSet.ι₀ (X := nerve P)) p H.h := ⟨H.h₀.symm⟩
  exact ⟨SSet.ι₁ ≫ sq.lift, by rw [Category.assoc, sq.fac_right, H.h₁]⟩

end

end Thomason.Construction

end

section

/-! # Weakly contractible Kan fibres give exact boundary lifting

The only semantic property used here is actual weak contractibility of
each original vertex fibre. Pullback to the specified base simplex and
the continuous-to-simplicial extension theorem give exact lifts.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem weaklyContractible_kan_boundary_extension (X : SSet.{0}) [SSet.KanComplex X]
    (hX : IsWeakHomotopyEquivalence (ContinuousMap.const (SSet.toTop.obj X) ()))
    (n : ℕ) (a : (SSet.boundary n : SSet.{0}) ⟶ X) :
    ∃ d : (Δ[n] : SSet.{0}) ⟶ X, (SSet.boundary n).ι ≫ d = a := by
  obtain ⟨c, hc⟩ := weaklyContractible_realized_extension (SSet.toTop.obj X) hX
    (SSet.boundary n).ι (SSet.toTop.map a)
  exact kan_extension_of_realization_boundary_extension n a c hc

theorem kan_boundary_lifting_of_weak_fibers {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p]
    (hF : ∀ v : B _⦋0⦌, IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p v).toSSet) ()))
    (n : ℕ) : HasLiftingProperty (SSet.boundary n).ι p := by
  refine ⟨fun {a b} sq => ?_⟩
  let q := pullback.snd p b
  let : HomotopicalAlgebra.Fibration q := kan_pullback_snd_fibration p b
  have hq : HasLiftingProperty (SSet.boundary n).ι q := by
    apply simplex_boundary_lifting_of_initial_fiber n n q
    intro aF
    let v := initialSimplexVertex n
    let F := simplicialPointFiber q v
    let : SSet.KanComplex F.toSSet := simplicialPointFiber_kan q v
    let e := simplicialPointFiberBaseChangeIso p b v
    have hi : IsWeakHomotopyEquivalence (SSet.toTop.map e.inv).hom :=
      realizationWeakEquivalences.of_isIso e.inv
    have hF' : IsWeakHomotopyEquivalence (ContinuousMap.const (SSet.toTop.obj F.toSSet) ()) := by
      exact hi.comp (hF (b.app _ v))
    exact weaklyContractible_kan_boundary_extension F.toSSet hF' n aF
  let a' : (SSet.boundary n : SSet.{0}) ⟶ pullback p b :=
    pullback.lift a (SSet.boundary n).ι sq.w
  have ha' : a' ≫ q = (SSet.boundary n).ι := pullback.lift_snd _ _ _
  let sq' : CommSq a' (SSet.boundary n).ι q (𝟙 _) :=
    ⟨ha'.trans (Category.comp_id _).symm⟩
  let : HasLiftingProperty (SSet.boundary n).ι q := hq
  refine ⟨⟨{ l := sq'.lift ≫ pullback.fst p b, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, sq'.fac_left, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sq'.fac_right,
      Category.id_comp]

theorem kan_boundary_rlp_of_weak_fibers {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p]
    (hF : ∀ v : B _⦋0⦌, IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p v).toSSet) ())) :
    I.rlp p := by
  intro A C i hi
  obtain ⟨n⟩ := hi
  exact kan_boundary_lifting_of_weak_fibers p hF n

/-- Boundary lifting also forces actual weak contractibility of every
original vertex fibre. Thus the preceding sufficient condition captures
the precise fibre obstruction, independently of any model structure. -/
theorem weak_fibers_of_boundary_rlp {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (hp : I.rlp p) (v : B _⦋0⦌) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p v).toSSet) ()) := by
  let c : (Δ[0] : SSet.{0}) ⟶ B := SSet.const v
  let q := pullback.snd p c
  have hq : I.rlp q := MorphismProperty.of_isPullback (IsPullback.of_hasPullback p c) hp
  have hqw : realizationWeakEquivalences q := boundary_rlp_weak q hq
  have hf := kan_simplex_baseChange_fiber_weak p 0 c
  have hcomp := realizationWeakEquivalences.comp_mem _ _ hf hqw
  let e : SSet.toTop.obj (Δ[0] : SSet.{0}) ≅ TopCat.of Unit := TopCat.isoOfHomeo
    (Homeomorph.homeomorphOfUnique (SSet.toTop.obj (Δ[0] : SSet.{0})) Unit)
  have he : topologicalWeakEquivalences e.hom := topologicalWeakEquivalences.of_isIso _
  have ht := topologicalWeakEquivalences.comp_mem _ e.hom hcomp he
  have hc : c.app _ (finalSimplexVertex 0) = v := by
    change B.map ((SimplexCategory.mk 0).const (.mk 0) 0).op v = v
    rw [show (SimplexCategory.mk 0).const (.mk 0) 0 = 𝟙 _ from Subsingleton.elim _ _]
    simp
  have heq : SSet.toTop.map (pointFiberToPullback p c (finalSimplexVertex 0) ≫ q) ≫ e.hom =
      TopCat.ofHom (ContinuousMap.const
        (SSet.toTop.obj (simplicialPointFiber p (c.app _ (finalSimplexVertex 0))).toSSet) ()) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  rw [heq] at ht
  change IsWeakHomotopyEquivalence (ContinuousMap.const
    (SSet.toTop.obj (simplicialPointFiber p (c.app _ (finalSimplexVertex 0))).toSSet) ()) at ht
  convert ht using 1
  rw [hc]

theorem kan_boundary_rlp_iff_weak_fibers {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] :
    I.rlp p ↔ ∀ v : B _⦋0⦌, IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p v).toSSet) ()) :=
  ⟨fun h => weak_fibers_of_boundary_rlp p h, kan_boundary_rlp_of_weak_fibers p⟩

end

end Thomason.Construction

end

section

/-! # Reduction of acyclic Kan lifting to Kan sources and bases

The actual infinite-extension functor reflects the boundary lifting
property for every Kan fibration. To prove this, reflect weak equivalences
of its pullbacks over points and use the original vertex-fibre criterion.
The reduction isolates the case where both source and base are Kan.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Weakness of the actual pullback over a vertex makes the original
simplicial vertex fibre weakly contractible. -/
theorem weak_fiber_of_point_pullback_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (v : B _⦋0⦌)
    (h : realizationWeakEquivalences
      (pullback.snd p (SSet.const (X := (Δ[0] : SSet.{0})) v))) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p v).toSSet) ()) := by
  let c : (Δ[0] : SSet.{0}) ⟶ B := SSet.const v
  let q := pullback.snd p c
  have hf := kan_simplex_baseChange_fiber_weak p 0 c
  have hcomp := realizationWeakEquivalences.comp_mem _ _ hf h
  let e : SSet.toTop.obj (Δ[0] : SSet.{0}) ≅ TopCat.of Unit := TopCat.isoOfHomeo
    (Homeomorph.homeomorphOfUnique (SSet.toTop.obj (Δ[0] : SSet.{0})) Unit)
  have he : topologicalWeakEquivalences e.hom := topologicalWeakEquivalences.of_isIso _
  have ht := topologicalWeakEquivalences.comp_mem _ e.hom hcomp he
  have hc : c.app _ (finalSimplexVertex 0) = v := by
    change B.map ((SimplexCategory.mk 0).const (.mk 0) 0).op v = v
    rw [show (SimplexCategory.mk 0).const (.mk 0) 0 = 𝟙 _ from Subsingleton.elim _ _]
    simp
  have heq : SSet.toTop.map (pointFiberToPullback p c (finalSimplexVertex 0) ≫ q) ≫ e.hom =
      TopCat.ofHom (ContinuousMap.const
        (SSet.toTop.obj (simplicialPointFiber p (c.app _ (finalSimplexVertex 0))).toSSet) ()) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  rw [heq] at ht
  change IsWeakHomotopyEquivalence
    (ContinuousMap.const
      (SSet.toTop.obj (simplicialPointFiber p (c.app _ (finalSimplexVertex 0))).toSSet) ()) at ht
  convert ht using 1
  rw [hc]

/-- The infinite extension reflects boundary lifting without any Kan
assumption on the original base. -/
theorem boundary_rlp_of_map_arbitrary_base {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (hp : I.rlp (map p)) : I.rlp p := by
  apply kan_boundary_rlp_of_weak_fibers p
  intro v
  let c : (Δ[0] : SSet.{0}) ⟶ B := SSet.const v
  have hq : I.rlp (pullback.snd (map p) (map c)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (map p) (map c)) hp
  have hqw : realizationWeakEquivalences (pullback.snd p c) :=
    (pullback_snd_weak_iff p c).mpr (boundary_rlp_weak _ hq)
  exact weak_fiber_of_point_pullback_weak p v hqw

theorem map_boundary_rlp_iff_arbitrary_base {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] : I.rlp (map p) ↔ I.rlp p :=
  ⟨boundary_rlp_of_map_arbitrary_base p, map_boundary_rlp p⟩

/-- Only weak Kan fibrations between Kan complexes remain in the general
acyclic lifting problem. This is a reduction, not an assumption in the main
theorem or a proof of that restricted case. -/
theorem acyclicKanLifting_of_fibrant_case
    (h : ∀ {E B : SSet.{0}} [SSet.KanComplex E] [SSet.KanComplex B]
      (p : E ⟶ B) [HomotopicalAlgebra.Fibration p],
        realizationWeakEquivalences p → I.rlp p) : PublishedAcyclicKanLifting := by
  intro E B p hp
  let : HomotopicalAlgebra.Fibration p := (fibration_iff p).mpr hp.1
  let : HomotopicalAlgebra.Fibration (map p) := map_fibration p
  apply boundary_rlp_of_map_arbitrary_base p
  exact h (map p) ((map_weak_iff p).mpr hp.2)

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Returning an exact face-poset lift to the original simplex

The actual first-subdivision comparison commutes with last vertices and
with subcomplex inclusions. Relative Kan descent therefore takes an exact
face-poset lift back to the original simplex subcomplex.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem simplexSubcomplex_lift_of_facePoset_lift {n : ℕ}
    (A B : (Δ[n] : SSet.{0}).Subcomplex) (hAB : A ≤ B)
    {E Z : SSet.{0}} [SSet.KanComplex Z]
    (p : E ⟶ Z) [HomotopicalAlgebra.Fibration p]
    (a : A.toSSet ⟶ E) (b : B.toSSet ⟶ Z)
    (ha : a ≫ p = SSet.Subcomplex.homOfLE hAB ≫ b)
    (d : nerve B.toSSet.N ⟶ E)
    (hd : nerveMap (NonsingularLastVertex.faceMap (SSet.Subcomplex.homOfLE hAB)
        (NonsingularLastVertex.preservesNondegenerate_of_mono _)).monotone.functor ≫ d =
      NonsingularLastVertex.map A.toSSet ≫ a)
    (hp : d ≫ p = NonsingularLastVertex.map B.toSSet ≫ b) :
    ∃ g : B.toSSet ⟶ E,
      SSet.Subcomplex.homOfLE hAB ≫ g = a ∧ g ≫ p = b := by
  let i := SSet.Subcomplex.homOfLE hAB
  let f := SubcomplexFaceComparison.map B ≫ d
  have hi : SSet.sd.map i ≫ f = lastVertex.app A.toSSet ≫ a := by
    change SSet.sd.map i ≫ (SubcomplexFaceComparison.map B ≫ d) = _
    rw [← Category.assoc, SubcomplexFaceComparison.map_naturality hAB,
      Category.assoc, hd, ← Category.assoc, SubcomplexFaceComparison.map_lastVertex]
  have hf : f ≫ p = lastVertex.app B.toSSet ≫ b := by
    change (SubcomplexFaceComparison.map B ≫ d) ≫ p = _
    rw [Category.assoc, hp, ← Category.assoc, SubcomplexFaceComparison.map_lastVertex]
  obtain ⟨g, _, hg, hgp, _, _⟩ :=
    exists_simplexSubcomplex_subdivision_relative_base_descent A B i p a f b ha hf hi
  exact ⟨g, hg, hgp⟩

end

end Thomason.Construction

end

end OAI
