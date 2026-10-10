import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanContractedFamilyLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanRealizedEdgeComposition
import OAI.CategoryTheory.Thomason.Simplicial.KanSimplexContinuousFibers
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.TripleGlobeCylinderPushout
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts

namespace OAI

section

/-! # Exact finite approximation inside fibres over contracted parameters -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The explicit stationary simplicial contraction makes the actual
realization weakly contractible, via its original chosen vertex. -/
theorem contracted_realization_to_point_weak (B : SSet.{0}) (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v) :
    IsWeakHomotopyEquivalence (ContinuousMap.const (SSet.toTop.obj B) ()) := by
  let q : B ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from B
  have hi := anodyne_realization_weak (contractedVertexInclusion v)
    (contractedVertexInclusion_anodyne v C hC)
  have hq : realizationWeakEquivalences q := by
    apply realizationWeakEquivalences.of_precomp (contractedVertexInclusion v) q hi
    rw [show contractedVertexInclusion v ≫ q = 𝟙 _ from
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
    exact realizationWeakEquivalences.id_mem _
  let e : SSet.toTop.obj (Δ[0] : SSet.{0}) ≅ TopCat.of Unit := TopCat.isoOfHomeo
    (Homeomorph.homeomorphOfUnique (SSet.toTop.obj (Δ[0] : SSet.{0})) Unit)
  have he : topologicalWeakEquivalences e.hom := topologicalWeakEquivalences.of_isIso _
  have hh := topologicalWeakEquivalences.comp_mem (SSet.toTop.map q) e.hom hq he
  have hc : SSet.toTop.map q ≫ e.hom =
      (TopCat.ofHom (ContinuousMap.const (SSet.toTop.obj B) ()) : _ ⟶ TopCat.of Unit) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  rwa [hc] at hh

/-- Every real-point fibre of an acyclic Kan map over the finite
contracted base is weakly contractible. No choice of vertex for that point
or singular replacement of the original total space is used. -/
theorem kan_acyclic_finite_contracted_continuousFiber_weak
    {E B : SSet.{0}} [B.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : SSet.toTop.obj B) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (continuousFiber (SSet.toTop.map p) b) ()) := by
  have hf := kan_finite_contracted_continuousFiberInclusion_weak v C hC p b
  exact (hf.comp hp).comp (contracted_realization_to_point_weak B v C hC)

/-- The original simplicial vertex fibre has the same weak-contractibility
test. This is the fibre in which the higher boundary must eventually be
filled simplicially. -/
theorem kan_acyclic_finite_contracted_simplicialFiber_weak
    {E B : SSet.{0}} [B.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : B _⦋0⦌) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p b).toSSet) ()) := by
  have hf := kan_finite_contracted_simplicialFiberInclusion_weak v C hC p b
  exact (hf.comp hp).comp (contracted_realization_to_point_weak B v C hC)

/-- A finite higher extension problem admits an exact continuous extension
in one finite subcomplex of the ORIGINAL simplicial fibre. The entire
prescribed boundary map is retained, before applying any singular unit. -/
theorem finite_relative_contracted_fiber_extension
    {E B A K : SSet.{0}} [B.Finite] [K.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : B _⦋0⦌)
    (i : A ⟶ K) [Mono i] (a : A ⟶ (simplicialPointFiber p b).toSSet) :
    ∃ (S : (simplicialPointFiber p b).toSSet.Subcomplex)
      (_ : SSet.Finite S.toSSet) (aS : A ⟶ S.toSSet)
      (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
      aS ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map aS := by
  let F := (simplicialPointFiber p b).toSSet
  let f : SSet.toTop.obj F ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const _ ())
  let d : SSet.toTop.obj K ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const _ ())
  have h : SSet.toTop.map a ≫ f = SSet.toTop.map i ≫ d := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  obtain ⟨S, hS, aS, c, ha, hc, _⟩ := finite_relative_realization_lift i f
    (kan_acyclic_finite_contracted_simplicialFiber_weak v C hC p hp b) a d h
  exact ⟨S, hS, aS, c, ha, hc⟩

end

end Thomason.Construction

end

section

/-! # Finite relative approximation and extensions in cubical Kan fibres -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A continuous relative family in the total realization of a cubical Kan
fibration can be moved into any vertex fibre, in finite support. The boundary
is kept simplicial and exact, and the resulting total-space homotopy is
stationary there. No acyclicity of the original fibration is needed. -/
theorem finite_relative_fiber_approximation {E A K : SSet.{0}} [K.Finite]
    (n : ℕ) (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (b : (obj n) _⦋0⦌)
    (i : A ⟶ K) [Mono i] (a : A ⟶ (simplicialPointFiber p b).toSSet)
    (d : SSet.toTop.obj K ⟶ SSet.toTop.obj E)
    (h : SSet.toTop.map a ≫ SSet.toTop.map (simplicialPointFiber p b).ι =
      SSet.toTop.map i ≫ d) :
    ∃ S : (simplicialPointFiber p b).toSSet.Subcomplex,
      SSet.Finite S.toSSet ∧ ∃ (a' : A ⟶ S.toSSet)
        (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
        a' ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        Nonempty ((c ≫ SSet.toTop.map S.ι ≫
          SSet.toTop.map (simplicialPointFiber p b).ι).hom.HomotopyRel d.hom
            (Set.range (SSet.toTop.map i).hom)) :=
  finite_relative_realization_lift i (SSet.toTop.map (simplicialPointFiber p b).ι)
    (kan_any_fiber_weak n p b) a d h

/-- Every vertex fibre of an actual weak Kan fibration over a finite cube
has weakly contractible realization. -/
theorem acyclic_fiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : (obj n) _⦋0⦌) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p b).toSSet) ()) := by
  have hc := kan_realizedPointFiberComparison_weak n p b
  have hf := continuousHomotopyFiber_weak (SSet.toTop.map p) hp
    (RealizationPrism.vertexPoint _ b)
  exact hc.comp hf

/-- Higher finite relative extension in an acyclic cubical fibre has an
exact continuous solution in one finite subcomplex of the literal fibre. -/
theorem finite_relative_acyclic_fiber_extension {E A K : SSet.{0}} [K.Finite]
    (n : ℕ) (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : (obj n) _⦋0⦌)
    (i : A ⟶ K) [Mono i] (a : A ⟶ (simplicialPointFiber p b).toSSet) :
    ∃ S : (simplicialPointFiber p b).toSSet.Subcomplex,
      SSet.Finite S.toSSet ∧ ∃ (a' : A ⟶ S.toSSet)
        (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
        a' ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map a' := by
  let f : SSet.toTop.obj (simplicialPointFiber p b).toSSet ⟶ TopCat.of Unit :=
    TopCat.ofHom (ContinuousMap.const _ ())
  let d : SSet.toTop.obj K ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const _ ())
  have h : SSet.toTop.map a ≫ f = SSet.toTop.map i ≫ d := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  obtain ⟨S, hS, a', c, ha, hi, _⟩ := finite_relative_realization_lift i f
    (acyclic_fiber_weak n p hp b) a d h
  exact ⟨S, hS, a', c, ha, hi⟩

end

end Thomason.Construction.RealizedCube

end

section

/-! # Exact acyclic edge lifting over finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- An actual weak Kan fibration over a finite cube lifts every edge with
both endpoints prescribed. The endpoint correction is performed by an
actual edge in the weakly contractible vertex fibre. -/
theorem acyclic_edge_lifting {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (x y : E _⦋0⦌)
    (b : SSet.Edge (p.app _ x) (p.app _ y)) :
    ∃ e : SSet.Edge x y, e.map p = b :=
  kan_lift_edge_of_fiber_components p x y b (acyclic_fiber_weak n p hp _).1.1

/-- The full one-dimensional acyclic boundary lifting theorem for arbitrary
Kan fibrations whose base is a finite simplicial cube. -/
theorem acyclic_boundary_one {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) :
    HasLiftingProperty (SSet.boundary 1).ι p :=
  boundary_one_lifting_of_edges p (acyclic_edge_lifting n p hp)

end

end Thomason.Construction.RealizedCube

end

section

/-! # Finite geometric approximation of every higher cubical boundary problem -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A weak Kan map over a finite cube gives every cubical boundary square
an exact continuous extension in one finite subcomplex of its ORIGINAL
initial simplicial fibre. The original square has a simplicial lift exactly
when the retained boundary is simplicially nullhomotopic in that fibre.
No Kan or acyclicity property is asserted for the finite carrier itself. -/
theorem finite_boundary_lifting_reduction {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ obj m) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p)
    (a : (boundary n : SSet.{0}) ⟶ E) (b : obj (n+1) ⟶ obj m)
    (hab : a ≫ p = (boundary n).ι ≫ b) :
    ∃ (r : E ⟶ (simplicialPointFiber p (initialVertex m)).toSSet)
      (S : (simplicialPointFiber p (initialVertex m)).toSSet.Subcomplex)
      (_ : SSet.Finite S.toSSet)
      (aS : (boundary n : SSet.{0}) ⟶ S.toSSet)
      (c : SSet.toTop.obj (obj (n+1)) ⟶ SSet.toTop.obj S.toSSet),
      (simplicialPointFiber p (initialVertex m)).ι ≫ r = 𝟙 _ ∧
      aS ≫ S.ι = a ≫ r ∧
      SSet.toTop.map (boundary n).ι ≫ c = SSet.toTop.map aS ∧
      ((∃ d : obj (n+1) ⟶ E, (boundary n).ι ≫ d = a ∧ d ≫ p = b) ↔
        ∃ x, Nonempty (SSet.Homotopy (SSet.const x) (aS ≫ S.ι))) := by
  obtain ⟨r, hr, he⟩ := boundary_lift_iff_fiber_nullhomotopy m n p a b hab
  have : (obj (n+1)).Finite := realizedCube_finite (n+1)
  obtain ⟨S, hS, aS, c, haS, hc⟩ := finite_relative_acyclic_fiber_extension m p hp
    (initialVertex m) (boundary n).ι (a ≫ r)
  refine ⟨r, S, hS, aS, c, hr, haS, hc, ?_⟩
  rw [haS]
  exact he

end

end Thomason.Construction.RealizedCube

end

section

/-! # Finite support for the entire relative weak-lifting homotopy -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A relative weak lift between realizations can be confined to a map of
finite subcomplexes, including the entire homotopy in the target. The
original simplicial boundary is retained exactly. -/
theorem finite_relative_lift_with_homotopy_support {A B L Y : SSet.{0}} [B.Finite]
    (i : A ⟶ B) [Mono i] (f : L ⟶ Y) (hf : realizationWeakEquivalences f)
    (a : A ⟶ L) (b : SSet.toTop.obj B ⟶ SSet.toTop.obj Y)
    (h : SSet.toTop.map a ≫ SSet.toTop.map f = SSet.toTop.map i ≫ b) :
    ∃ (S : L.Subcomplex) (T : Y.Subcomplex),
      SSet.Finite S.toSSet ∧ SSet.Finite T.toSSet ∧
      ∃ (g : S.toSSet ⟶ T.toSSet) (a' : A ⟶ S.toSSet)
        (c : SSet.toTop.obj B ⟶ SSet.toTop.obj S.toSSet)
        (b' : SSet.toTop.obj B ⟶ SSet.toTop.obj T.toSSet),
        g ≫ T.ι = S.ι ≫ f ∧ a' ≫ S.ι = a ∧
        SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        b' ≫ SSet.toTop.map T.ι = b ∧
        Nonempty ((c ≫ SSet.toTop.map g).hom.HomotopyRel b'.hom
          (Set.range (SSet.toTop.map i).hom)) := by
  obtain ⟨S, hS, a', c, ha, hc, ⟨H⟩⟩ :=
    finite_relative_realization_lift i (SSet.toTop.map f) hf a b h
  have : SSet.Finite S.toSSet := hS
  let : CompactSpace (SSet.toTop.obj B) := RealizationPrism.compactSpace_of_finite B
  obtain ⟨V, hV, hVmap, heV⟩ := RealizationPrism.compact_map_factors Y H.toContinuousMap
  let : SSet.Finite V.toSSet := hV
  let T : Y.Subcomplex := V ⊔ SSet.Subcomplex.range (S.ι ≫ f)
  have hT : SSet.Finite T.toSSet := by
    let U : Bool → Y.Subcomplex := fun v => if v then V else SSet.Subcomplex.range (S.ι ≫ f)
    have he : T = iSup U := by
      apply le_antisymm
      · exact sup_le (le_iSup U true) (le_iSup U false)
      · apply iSup_le
        intro v
        cases v
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff U).mpr
    intro v
    cases v <;> dsimp [U] <;> infer_instance
  let j : V.toSSet ⟶ T.toSSet := SSet.Subcomplex.homOfLE le_sup_left
  let HT : C(unitInterval × SSet.toTop.obj B, SSet.toTop.obj T.toSSet) :=
    (SSet.toTop.map j).hom.comp hVmap
  have hHT (z : unitInterval × SSet.toTop.obj B) :
      (SSet.toTop.map T.ι).hom (HT z) = H z := by
    have hj : j ≫ T.ι = V.ι := rfl
    have hz := congrArg (fun k => k.hom (hVmap z)) (SSet.toTop.congr_map hj)
    rw [SSet.toTop.map_comp] at hz
    exact hz.trans (congrArg (fun k : C(_, _) => k z) heV)
  let g : S.toSSet ⟶ T.toSSet := T.lift (S.ι ≫ f) le_sup_right
  have hg : g ≫ T.ι = S.ι ≫ f := rfl
  let b' : SSet.toTop.obj B ⟶ SSet.toTop.obj T.toSSet :=
    TopCat.ofHom ⟨fun x => HT (1, x), by fun_prop⟩
  have hb : b' ≫ SSet.toTop.map T.ι = b := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact (hHT (1, x)).trans (H.apply_one x)
  have hzero (x : SSet.toTop.obj B) : HT (0, x) = (c ≫ SSet.toTop.map g).hom x := by
    apply RealizationPrism.inclusion_injective Y T
    have he := congrArg (fun k => k.hom (c.hom x)) (SSet.toTop.congr_map hg)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
    exact (hHT (0, x)).trans ((H.apply_zero x).trans he.symm)
  refine ⟨S, T, hS, hT, g, a', c, b', hg, ha, hc, hb, ⟨?_⟩⟩
  refine {
    toFun := HT
    continuous_toFun := HT.continuous
    map_zero_left := hzero
    map_one_left := fun _ => rfl
    prop' := ?_ }
  intro t x hx
  apply RealizationPrism.inclusion_injective Y T
  have he := congrArg (fun k => k.hom (c.hom x)) (SSet.toTop.congr_map hg)
  rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
  exact (hHT (t, x)).trans ((H.prop t x hx).trans he.symm)

end

end Thomason.Construction

end

section

/-! # Finite higher-dimensional extension inside acyclic simplex fibres -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Every vertex fibre of an actual weak Kan fibration over a standard
simplex has weakly contractible realization. -/
theorem kan_acyclic_simplex_fiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : (Δ[n] : SSet.{0}) _⦋0⦌) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p b).toSSet) ()) := by
  have hc := kan_simplex_realizedPointFiberComparison_weak n p b
  have hf := continuousHomotopyFiber_weak (SSet.toTop.map p) hp
    (RealizationPrism.vertexPoint _ b)
  exact hc.comp hf

/-- A finite relative extension problem in such a fibre has an exact
continuous solution in one finite subcomplex of the same literal fibre.
The boundary map stays simplicial and is preserved exactly. This theorem
asserts the geometric finite approximation stage, not a simplicial filler. -/
theorem finite_relative_simplex_fiber_extension {E A K : SSet.{0}} [K.Finite]
    (n : ℕ) (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (b : (Δ[n] : SSet.{0}) _⦋0⦌)
    (i : A ⟶ K) [Mono i] (a : A ⟶ (simplicialPointFiber p b).toSSet) :
    ∃ S : (simplicialPointFiber p b).toSSet.Subcomplex,
      SSet.Finite S.toSSet ∧ ∃ (a' : A ⟶ S.toSSet)
        (c : SSet.toTop.obj K ⟶ SSet.toTop.obj S.toSSet),
        a' ≫ S.ι = a ∧ SSet.toTop.map i ≫ c = SSet.toTop.map a' := by
  let f : SSet.toTop.obj (simplicialPointFiber p b).toSSet ⟶ TopCat.of Unit :=
    TopCat.ofHom (ContinuousMap.const _ ())
  let d : SSet.toTop.obj K ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const _ ())
  have h : SSet.toTop.map a ≫ f = SSet.toTop.map i ≫ d := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  obtain ⟨S, hS, a', c, ha, hi, _⟩ := finite_relative_realization_lift i f
    (kan_acyclic_simplex_fiber_weak n p hp b) a d h
  exact ⟨S, hS, a', c, ha, hi⟩

end

end Thomason.Construction

end

section

/-! # Finite singular approximation retaining a full relative lifting square -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- A continuous relative weak lift has an exact simplicial adjoint and a
stationary simplicial projection homotopy. The target remains the singular
realization; no descent to the original simplicial set is asserted. -/
theorem singular_relative_lift_of_continuous {A K E B : SSet.{0}}
    (i : A ⟶ K) (p : E ⟶ B) (a : A ⟶ E) (b : K ⟶ B)
    (c : SSet.toTop.obj K ⟶ SSet.toTop.obj E)
    (hc : SSet.toTop.map i ≫ c = SSet.toTop.map a)
    (H : (c ≫ SSet.toTop.map p).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map i).hom)) :
    ∃ (d : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj E))
      (G : SSet.Homotopy (d ≫ TopCat.toSSet.map (SSet.toTop.map p))
        (b ≫ sSetTopAdj.unit.app B)),
      i ≫ d = a ≫ sSetTopAdj.unit.app E ∧
      i ▷ Δ[1] ≫ G.h =
        fst A Δ[1] ≫ a ≫ sSetTopAdj.unit.app E ≫ TopCat.toSSet.map (SSet.toTop.map p) := by
  let d := sSetTopAdj.homEquiv K (SSet.toTop.obj E) c
  have hd : i ≫ d = a ≫ sSetTopAdj.unit.app E := adjoint_relative_extension i a c hc
  have he : sSetTopAdj.homEquiv K (SSet.toTop.obj B) (c ≫ SSet.toTop.map p) =
      d ≫ TopCat.toSSet.map (SSet.toTop.map p) :=
    sSetTopAdj.homEquiv_naturality_right c (SSet.toTop.map p)
  let F := adjointRealizationHomotopy H.toHomotopy
  let G : SSet.Homotopy (d ≫ TopCat.toSSet.map (SSet.toTop.map p))
      (b ≫ sSetTopAdj.unit.app B) := {
    h := F.h
    h₀ := by
      rw [F.h₀, he]
      rfl
    h₁ := by
      rw [F.h₁, adjoint_realized_map]
      rfl
    rel := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨d, G, hd, ?_⟩
  have hG := adjointRealizationHomotopy_stationary i H
  change i ▷ Δ[1] ≫ (adjointRealizationHomotopy H.toHomotopy).h = _
  rw [hG, he, ← Category.assoc i d, hd]
  simp only [Category.assoc]

/-- The complete singular relative lift lies in two finite subcomplexes,
including every simplex of its stationary projection homotopy. -/
theorem finite_singular_relative_lift_of_continuous {A K E B : SSet.{0}} [K.Finite]
    (i : A ⟶ K) (p : E ⟶ B) (a : A ⟶ E) (b : K ⟶ B)
    (c : SSet.toTop.obj K ⟶ SSet.toTop.obj E)
    (hc : SSet.toTop.map i ≫ c = SSet.toTop.map a)
    (H : (c ≫ SSet.toTop.map p).hom.HomotopyRel (SSet.toTop.map b).hom
      (Set.range (SSet.toTop.map i).hom)) :
    ∃ (S : (TopCat.toSSet.obj (SSet.toTop.obj E)).Subcomplex)
      (T : (TopCat.toSSet.obj (SSet.toTop.obj B)).Subcomplex),
      SSet.Finite S.toSSet ∧ SSet.Finite T.toSSet ∧
      ∃ (q : S.toSSet ⟶ T.toSSet) (aS : A ⟶ S.toSSet)
        (bT : K ⟶ T.toSSet) (dS : K ⟶ S.toSSet)
        (G : SSet.Homotopy (dS ≫ q) bT),
        q ≫ T.ι = S.ι ≫ TopCat.toSSet.map (SSet.toTop.map p) ∧
        aS ≫ S.ι = a ≫ sSetTopAdj.unit.app E ∧
        bT ≫ T.ι = b ≫ sSetTopAdj.unit.app B ∧ i ≫ dS = aS ∧
        i ▷ Δ[1] ≫ G.h = fst A Δ[1] ≫ aS ≫ q := by
  obtain ⟨d, G, hd, hG⟩ := singular_relative_lift_of_continuous i p a b c hc H
  let S := SSet.Subcomplex.range d
  let T := SSet.Subcomplex.range G.h
  let dS : K ⟶ S.toSSet := SSet.Subcomplex.toRange d
  have hST : S ≤ T.preimage (TopCat.toSSet.map (SSet.toTop.map p)) := by
    intro j x hx
    obtain ⟨y, rfl⟩ := hx
    change (d ≫ TopCat.toSSet.map (SSet.toTop.map p)).app j y ∈ T.obj j
    rw [← G.h₀]
    exact ⟨SSet.ι₀.app j y, rfl⟩
  let q : S.toSSet ⟶ T.toSSet := SSet.Subcomplex.homOfLE hST ≫
    T.fromPreimage (TopCat.toSSet.map (SSet.toTop.map p))
  let aS : A ⟶ S.toSSet := i ≫ dS
  let bT : K ⟶ T.toSSet := SSet.ι₁ ≫ SSet.Subcomplex.toRange G.h
  have hq : q ≫ T.ι = S.ι ≫ TopCat.toSSet.map (SSet.toTop.map p) := by
    dsimp only [q]
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι]
    rfl
  have hds : dS ≫ S.ι = d := rfl
  have ha : aS ≫ S.ι = a ≫ sSetTopAdj.unit.app E := by
    dsimp only [aS]
    rw [Category.assoc, hds, hd]
  have hb : bT ≫ T.ι = b ≫ sSetTopAdj.unit.app B := by
    dsimp only [bT]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, G.h₁]
  let GT : SSet.Homotopy (dS ≫ q) bT := {
    h := SSet.Subcomplex.toRange G.h
    h₀ := by
      change SSet.ι₀ ≫ SSet.Subcomplex.toRange G.h = dS ≫ q
      apply (cancel_mono T.ι).mp
      rw [Category.assoc, SSet.Subcomplex.toRange_ι, G.h₀,
        Category.assoc, hq, ← Category.assoc, hds]
    h₁ := rfl
    rel := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨S, T, inferInstance, inferInstance, q, aS, bT, dS, GT, hq, ha, hb, rfl, ?_⟩
  apply (cancel_mono T.ι).mp
  change (i ▷ Δ[1] ≫ SSet.Subcomplex.toRange G.h) ≫ T.ι = _
  rw [Category.assoc, SSet.Subcomplex.toRange_ι, hG,
    Category.assoc, Category.assoc, hq, ← Category.assoc aS, ha]
  simp only [Category.assoc]

/-- Every actual weak simplicial map admits this finite, stationary
singular approximation to each finite relative lifting problem. A Kan
hypothesis is not needed until descent and exactification in the original
simplicial set. -/
theorem finite_singular_weak_relative_lift {A K E B : SSet.{0}} [K.Finite]
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) (hp : realizationWeakEquivalences p)
    (a : A ⟶ E) (b : K ⟶ B) (h : a ≫ p = i ≫ b) :
    ∃ (S : (TopCat.toSSet.obj (SSet.toTop.obj E)).Subcomplex)
      (T : (TopCat.toSSet.obj (SSet.toTop.obj B)).Subcomplex),
      SSet.Finite S.toSSet ∧ SSet.Finite T.toSSet ∧
      ∃ (q : S.toSSet ⟶ T.toSSet) (aS : A ⟶ S.toSSet)
        (bT : K ⟶ T.toSSet) (dS : K ⟶ S.toSSet)
        (G : SSet.Homotopy (dS ≫ q) bT),
        q ≫ T.ι = S.ι ≫ TopCat.toSSet.map (SSet.toTop.map p) ∧
        aS ≫ S.ι = a ≫ sSetTopAdj.unit.app E ∧
        bT ≫ T.ι = b ≫ sSetTopAdj.unit.app B ∧ i ≫ dS = aS ∧
        i ▷ Δ[1] ≫ G.h = fst A Δ[1] ≫ aS ≫ q := by
  have ht : SSet.toTop.map a ≫ SSet.toTop.map p = SSet.toTop.map i ≫ SSet.toTop.map b := by
    rw [← SSet.toTop.map_comp, h, SSet.toTop.map_comp]
  obtain ⟨c, hc, ⟨H⟩⟩ := weak_relative_realization_lift
    (SSet.toTop.map p) hp i (SSet.toTop.map a) (SSet.toTop.map b) ht
  exact finite_singular_relative_lift_of_continuous i p a b c hc H

end

end Thomason.Construction

end

section

/-! # Weak simplicial monos realize to strong deformation retractions -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A monomorphic actual realization weak equivalence has a continuous
retraction and a homotopy fixing its entire realized image. -/
theorem weak_mono_realization_deformation {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (hi : realizationWeakEquivalences i) :
    ∃ r : SSet.toTop.obj B ⟶ SSet.toTop.obj A,
      SSet.toTop.map i ≫ r = 𝟙 _ ∧
      Nonempty ((r ≫ SSet.toTop.map i).hom.HomotopyRel (ContinuousMap.id _)
        (Set.range (SSet.toTop.map i).hom)) := by
  exact weak_relative_realization_lift (SSet.toTop.map i) hi i (𝟙 _) (𝟙 _) (by simp)

/-- The strong deformation condition is exactly the realization weak test
on a simplicial monomorphism. No anodyne-class identification is assumed. -/
theorem weak_mono_iff_realization_deformation {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    realizationWeakEquivalences i ↔
      ∃ r : SSet.toTop.obj B ⟶ SSet.toTop.obj A,
        SSet.toTop.map i ≫ r = 𝟙 _ ∧
        Nonempty ((r ≫ SSet.toTop.map i).hom.HomotopyRel (ContinuousMap.id _)
          (Set.range (SSet.toTop.map i).hom)) := by
  constructor
  · exact weak_mono_realization_deformation i
  · rintro ⟨r, hr, ⟨H⟩⟩
    let e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj A) (SSet.toTop.obj B) := {
      toFun := (SSet.toTop.map i).hom
      invFun := r.hom
      left_inv := by
        have he := congrArg (fun t => t.hom) hr
        change r.hom.comp (SSet.toTop.map i).hom = ContinuousMap.id _ at he
        rw [he]
      right_inv := ⟨H.toHomotopy⟩ }
    exact homotopyEquiv_isWeakHomotopyEquivalence e

end

end Thomason.Construction

end

section

/-! # Arbitrary small coproducts of actual realization weak equivalences

The proof factors each map algebraically, uses the realized deformation on
its weak monic factor and on a section of its boundary-lifting factor, and
then applies two-out-of-three. It requires no Kan–Quillen model structure.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

theorem weak_mono_coproduct {α : Type} {A B : α → SSet.{0}}
    (f : ∀ a, A a ⟶ B a) (hm : ∀ a, Mono (f a))
    (hf : ∀ a, realizationWeakEquivalences (f a)) :
    realizationWeakEquivalences (CategoryTheory.Limits.Sigma.map f) := by
  have hd : ∀ a, Nonempty (TopologicalDeformation.Data (SSet.toTop.map (f a))) := by
    intro a
    have := hm a
    obtain ⟨r, hr, H⟩ := weak_mono_realization_deformation (f a) (hf a)
    exact ⟨⟨r, hr, Classical.choice H⟩⟩
  let d := realizedCoproductData f (fun a => Classical.choice (hd a))
  exact weakEquivalence_of_strongDeformationRetract _ _
    (congrArg TopCat.Hom.hom d.left_inv) d.homotopy

/-- The original coproduct map satisfies the actual realization weak test. -/
theorem realization_coproduct_weak {α : Type} {A B : α → SSet.{0}}
    (f : ∀ a, A a ⟶ B a) (hf : ∀ a, realizationWeakEquivalences (f a)) :
    realizationWeakEquivalences (CategoryTheory.Limits.Sigma.map f) := by
  have := boundary_weakFactorizationSystem
  let d := fun a => MorphismProperty.factorizationData
    (MorphismProperty.monomorphisms SSet.{0}) I.rlp (f a)
  have hp : ∀ a, realizationWeakEquivalences (d a).p :=
    fun a => boundary_rlp_weak _ (d a).hp
  have hi : ∀ a, realizationWeakEquivalences (d a).i := by
    intro a
    apply realizationWeakEquivalences.of_postcomp _ (d a).p (hp a)
    rw [(d a).fac]
    exact hf a
  have hsi := weak_mono_coproduct (fun a => (d a).i) (fun a => (d a).hi) hi
  let r := fun a => boundaryRetraction (d a).p (d a).hp
  have hrm : ∀ a, Mono (r a).section_ := by
    intro a
    have : Mono ((r a).section_ ≫ (d a).p) := by rw [(r a).section_comp]; infer_instance
    exact mono_of_mono _ (d a).p
  have hrw : ∀ a, realizationWeakEquivalences (r a).section_ := by
    intro a
    apply realizationWeakEquivalences.of_postcomp _ (d a).p (hp a)
    rw [(r a).section_comp]
    exact realizationWeakEquivalences.id_mem _
  have hsr := weak_mono_coproduct (fun a => (r a).section_) hrm hrw
  have he : CategoryTheory.Limits.Sigma.map (fun a => (r a).section_) ≫ CategoryTheory.Limits.Sigma.map (fun a => (d a).p) = 𝟙 _ := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, (r a).section_comp, Category.id_comp, Category.comp_id]
  have hsp : realizationWeakEquivalences (CategoryTheory.Limits.Sigma.map (fun a => (d a).p)) := by
    apply realizationWeakEquivalences.of_precomp _ _ hsr
    rw [he]
    exact realizationWeakEquivalences.id_mem _
  have hfac : CategoryTheory.Limits.Sigma.map (fun a => (d a).i) ≫ CategoryTheory.Limits.Sigma.map (fun a => (d a).p) = CategoryTheory.Limits.Sigma.map f := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, (d a).fac, Sigma.ι_map]
  rw [← hfac]
  exact realizationWeakEquivalences.comp_mem _ _ hsi hsp

end

end Thomason.Construction

end

section

/-! # Arbitrary simplicial coproducts and their actual pullbacks -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- An arbitrary coproduct of simplicial sets remains a coproduct after
pullback. The proof uses the literal disjoint partition in each degree. -/
def simplicialCofan_pullback_isColimit {α : Type} {A D : α → SSet.{0}}
    (c : Cofan A) (hc : IsColimit c)
    (d : Cofan D) (p : d.pt ⟶ c.pt) (q : ∀ a, D a ⟶ A a)
    (h : ∀ a, IsPullback (d.inj a) (q a) p (c.inj a)) : IsColimit d := by
  let ec : c ≅ Cofan.mk c.pt c.inj := Cofan.ext (Iso.refl _) (fun a => by simp)
  let ed : d ≅ Cofan.mk d.pt d.inj := Cofan.ext (Iso.refl _) (fun a => by simp)
  refine IsColimit.ofIsoColimit ?_ ed.symm
  apply evaluationJointlyReflectsColimits
  intro m
  refine (isColimitMapCoconeCofanMkEquiv (SSet.evaluation.obj m) D d.inj).symm ?_
  let c' := Cofan.mk (c.pt.obj m) (fun a => (c.inj a).app m)
  have hc' : IsColimit c' :=
    (isColimitMapCoconeCofanMkEquiv (SSet.evaluation.obj m) _ _) (isColimitOfPreserves _ (IsColimit.ofIsoColimit hc ec))
  let d' := Cofan.mk (d.pt.obj m) (fun a => (d.inj a).app m)
  change IsColimit d'
  apply Classical.choice
  apply (Cofan.isColimit_cofanTypes_iff d').mp
  apply CofanTypes.isColimit_mk
  · intro x
    obtain ⟨a, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hc' (p.app m x)
    obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback ((h a).app m) x y hy.symm
    exact ⟨a, z, hz⟩
  · intro a x y hxy
    apply Types.ext_of_isPullback ((h a).app m) hxy
    apply Cofan.inj_injective_of_isColimit hc' a
    have hw := NatTrans.congr_app (h a).w m
    have h₁ := congrArg (fun k => k x) hw
    have h₂ := congrArg (fun k => k y) hw
    exact h₁.symm.trans ((congrArg (p.app m) hxy).trans h₂)
  · intro a b x y hxy
    apply Cofan.eq_of_inj_apply_eq_of_isColimit hc' ((q a).app m x) ((q b).app m y)
    have h₁ := congrArg (fun k => k x) (NatTrans.congr_app (h a).w m)
    have h₂ := congrArg (fun k => k y) (NatTrans.congr_app (h b).w m)
    exact h₁.symm.trans ((congrArg (p.app m) hxy).trans h₂)

/-- Canonical pullback pieces above an arbitrary coproduct form a coproduct
of the original total space. -/
def simplicialCofan_pullback (α : Type) (A : α → SSet.{0}) (c : Cofan A)
    (hc : IsColimit c) {E : SSet.{0}} (p : E ⟶ c.pt) :
    IsColimit (Cofan.mk E (fun a => pullback.fst p (c.inj a))) :=
  simplicialCofan_pullback_isColimit c hc _ p (fun a => pullback.snd p (c.inj a))
    (fun _ => IsPullback.of_hasPullback _ _)

/-- Objectwise actual weak equivalences between arbitrary coproduct
presentations induce a weak equivalence of the original total objects. -/
theorem simplicialCofan_map_weak {α : Type} {A B : α → SSet.{0}}
    (c : Cofan A) (hc : IsColimit c) (d : Cofan B) (hd : IsColimit d)
    (f : c.pt ⟶ d.pt) (u : ∀ a, A a ⟶ B a)
    (hu : ∀ a, c.inj a ≫ f = u a ≫ d.inj a)
    (hw : ∀ a, realizationWeakEquivalences (u a)) : realizationWeakEquivalences f := by
  let e := discreteCoproductIso (Discrete.functor A) hc
  let e' := discreteCoproductIso (Discrete.functor B) hd
  have he : e.hom ≫ f = CategoryTheory.Limits.Sigma.map u ≫ e'.hom := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, discreteCoproductIso_fac]
    change c.inj a ≫ f = _
    rw [hu, ← Category.assoc, Sigma.ι_map, Category.assoc]
    have hleg := discreteCoproductIso_fac (Discrete.functor B) hd a
    change Sigma.ι B a ≫ e'.hom = d.inj a at hleg
    rw [hleg]
  apply realizationWeakEquivalences.of_precomp e.hom f
    (realizationWeakEquivalences.of_isIso _)
  rw [he]
  exact realizationWeakEquivalences.comp_mem _ _ (realization_coproduct_weak u hw)
    (realizationWeakEquivalences.of_isIso _)

end

end Thomason.Construction

end

section

/-! # Cobase change of actual weak simplicial monomorphisms -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Cobase change preserves actual realization weak equivalences when the
changed map is monomorphic. The realized deformation is glued explicitly. -/
theorem realization_weak_mono_pushout {A B X P : SSet.{0}}
    {i : A ⟶ B} {f : A ⟶ X} {b : B ⟶ P} {j : X ⟶ P}
    (sq : IsPushout i f b j) [Mono i] (hi : realizationWeakEquivalences i) :
    realizationWeakEquivalences j := by
  obtain ⟨r, hr, ⟨H⟩⟩ := weak_mono_realization_deformation i hi
  exact TopologicalDeformation.pushout_weak (SSet.toTop.map_isPushout sq)
    ⟨r, hr, H⟩

/-- This stability is proved directly from geometric realization, without
identifying acyclic monomorphisms with anodyne extensions. -/
instance weakMonos_stableUnderCobaseChange :
    (MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences).IsStableUnderCobaseChange where
  of_isPushout sq hi := by
    have : Mono _ := hi.1
    exact ⟨(MorphismProperty.monomorphisms SSet).of_isPushout sq hi.1,
      realization_weak_mono_pushout sq.flip hi.2⟩

end

end Thomason.Construction

end

section

/-! # Cobase-change closure of weak equivalences tested along Kan fibrations -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Weak equivalence after every base change along an actual Kan fibration.
This is a property to be proved for cells, not an extra main-theorem input. -/
def kanBaseChangeWeak : MorphismProperty SSet.{0} := fun _ B i =>
  ∀ (E : SSet.{0}) (p : E ⟶ B), HomotopicalAlgebra.Fibration p →
    realizationWeakEquivalences (pullback.fst p i)

/-- The canonical pullback formulation also applies to any specified
cartesian square, retaining its original upper map. -/
theorem kanBaseChangeWeak.of_isPullback {A B A' B' : SSet.{0}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {a : A' ⟶ A} {p : B' ⟶ B}
    (hi : kanBaseChangeWeak i) [HomotopicalAlgebra.Fibration p]
    (h : IsPullback i' a p i) : realizationWeakEquivalences i' := by
  rw [← h.isoPullback_hom_fst]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (hi B' p inferInstance)

/-- Every generating horn satisfies the Kan base-change test. -/
theorem horn_kanBaseChangeWeak (n : ℕ) (i : Fin (n+2)) :
    kanBaseChangeWeak (Λ[n+1, i] : SSet.Subcomplex (Δ[n+1] : SSet.{0})).ι := by
  intro E p hp
  have := hp
  exact kan_horn_baseChange_weak n i p

/-- Pulling back a monic pushout gives a pushout. The weak upper attaching
map is obtained by testing the original cell along the restricted Kan
fibration, then the proved geometric gluing theorem applies. -/
theorem kanBaseChangeWeak_pushout {A B C D : SSet.{0}}
    {i : A ⟶ B} {f : A ⟶ C} {b : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f b j) [Mono i] (hi : kanBaseChangeWeak i) :
    kanBaseChangeWeak j := by
  intro E p hp
  have := hp
  obtain ⟨A', i', f', a, hleft, hright, htop⟩ :=
    (Adhesive.van_kampen sq).exists_cube_filling
      (IsPullback.of_hasPullback p b) (IsPullback.of_hasPullback p j)
  have : HomotopicalAlgebra.Fibration (pullback.snd p b) := kan_pullback_snd_fibration p b
  have hw : realizationWeakEquivalences i' := hi.of_isPullback hleft
  have : Mono i' := (MorphismProperty.monomorphisms SSet).of_isPullback hleft.flip inferInstance
  exact realization_weak_mono_pushout htop hw

/-- In particular, any single horn attachment remains a weak equivalence
under arbitrary Kan base change. -/
theorem horn_attachment_kanBaseChangeWeak {C D : SSet.{0}} (n : ℕ) (k : Fin (n+2))
    {f : (Λ[n+1, k] : SSet.{0}) ⟶ C} {b : (Δ[n+1] : SSet.{0}) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (Λ[n+1, k] : SSet.Subcomplex _).ι f b j) :
    kanBaseChangeWeak j := kanBaseChangeWeak_pushout sq (horn_kanBaseChangeWeak n k)

/-- The cell property composes, using the exact iterated-pullback isomorphism. -/
theorem kanBaseChangeWeak_comp {A B C : SSet.{0}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : kanBaseChangeWeak i) (hj : kanBaseChangeWeak j) : kanBaseChangeWeak (i ≫ j) := by
  intro E p hp
  have := hp
  have : HomotopicalAlgebra.Fibration (pullback.snd p j) := kan_pullback_snd_fibration p j
  rw [← pullbackLeftPullbackSndIso_inv_fst p j i]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _)
    (realizationWeakEquivalences.comp_mem _ _ (hi _ _ inferInstance) (hj _ _ inferInstance))

end

end Thomason.Construction

end

section

/-! # Simultaneous horn attachments and Kan base change -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- Arbitrary coproducts preserve the actual Kan base-change weak test.
Each restricted upper map is the base change of its original component. -/
theorem kanBaseChangeWeak_sigma {α : Type} {A B : α → SSet.{0}}
    (i : ∀ a, A a ⟶ B a) (hi : ∀ a, kanBaseChangeWeak (i a)) :
    kanBaseChangeWeak (CategoryTheory.Limits.Sigma.map i) := by
  intro E p hp
  have := hp
  let f := CategoryTheory.Limits.Sigma.map i
  let P := pullback p f
  let r : P ⟶ E := pullback.fst p f
  let q : P ⟶ ∐ A := pullback.snd p f
  let DA (a : α) := pullback q (Sigma.ι A a)
  let DB (a : α) := pullback p (Sigma.ι B a)
  let cA : Cofan DA := Cofan.mk P (fun a => pullback.fst q (Sigma.ι A a))
  let cB : Cofan DB := Cofan.mk E (fun a => pullback.fst p (Sigma.ι B a))
  have hcA : IsColimit cA := simplicialCofan_pullback α A _ (coproductIsCoproduct A) q
  have hcB : IsColimit cB := simplicialCofan_pullback α B _ (coproductIsCoproduct B) p
  have hout (a : α) : IsPullback
      (pullback.fst q (Sigma.ι A a) ≫ r) (pullback.snd q (Sigma.ι A a))
      p (i a ≫ Sigma.ι B a) := by
    have h := (IsPullback.of_hasPullback q (Sigma.ι A a)).paste_horiz
      (IsPullback.of_hasPullback p f)
    simpa only [f, r, Sigma.ι_map] using h
  let u (a : α) : DA a ⟶ DB a :=
    (IsPullback.of_hasPullback p (Sigma.ι B a)).lift
      (pullback.fst q (Sigma.ι A a) ≫ r)
      (pullback.snd q (Sigma.ι A a) ≫ i a) (by
        rw [Category.assoc]
        exact (hout a).w)
  have hu (a : α) : cA.inj a ≫ r = u a ≫ cB.inj a := by
    exact (IsPullback.lift_fst _ _ _ _).symm
  apply simplicialCofan_map_weak cA hcA cB hcB r u hu
  intro a
  have : HomotopicalAlgebra.Fibration (pullback.snd p (Sigma.ι B a)) :=
    kan_pullback_snd_fibration p (Sigma.ι B a)
  exact (hi a).of_isPullback
    (IsPullback.of_right' (hout a) (IsPullback.of_hasPullback p (Sigma.ι B a)))

end

end Thomason.Construction

end

section

/-! # Passing the Kan base-change test through a subcomplex exhaustion -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- Inverse image of a subcomplex is the actual categorical pullback. -/
theorem subcomplex_preimage_isPullback {X E : SSet.{0}} (A : X.Subcomplex) (p : E ⟶ X) :
    IsPullback (A.preimage p).ι (A.fromPreimage p) p A.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.1
  · intro x y h
    refine ⟨⟨x, ?_⟩, rfl, ?_⟩
    · change p.app d x ∈ A.obj d
      rw [h]
      exact y.property
    · exact Subtype.ext h

/-- Restricting a Kan fibration to an actual subcomplex is still Kan. -/
theorem subcomplex_fromPreimage_fibration {X E : SSet.{0}}
    (A : X.Subcomplex) (p : E ⟶ X) [HomotopicalAlgebra.Fibration p] :
    HomotopicalAlgebra.Fibration (A.fromPreimage p) := by
  rw [fibration_iff]
  exact MorphismProperty.of_isPullback (subcomplex_preimage_isPullback A p)
    ((fibration_iff p).mp inferInstance)

/-- Preimages of an inclusion form the required comparison pullback. -/
theorem subcomplex_preimage_inclusion_isPullback {X E : SSet.{0}}
    {A B : X.Subcomplex} (h : A ≤ B) (p : E ⟶ X) :
    IsPullback (SSet.Subcomplex.homOfLE (SSet.Subcomplex.preimage_monotone p h))
      (A.fromPreimage p) (B.fromPreimage p) (SSet.Subcomplex.homOfLE h) := by
  exact IsPullback.of_right (subcomplex_preimage_isPullback A p) rfl
    (subcomplex_preimage_isPullback B p)

/-- An increasing union of subcomplexes passes the actual Kan base-change
weak-equivalence test once the initial-to-stage comparisons do. Compact
cubes and relative homotopies justify the passage to the union. -/
theorem kanBaseChangeWeak_exhaustion {X : SSet.{0}} (A : ℕ → X.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤)
    (hW : ∀ n, kanBaseChangeWeak (SSet.Subcomplex.homOfLE (hA (Nat.zero_le n)))) :
    kanBaseChangeWeak (A 0).ι := by
  intro E p hp
  have := hp
  let R : ℕ → E.Subcomplex := fun n => (A n).preimage p
  have hR : Monotone R := fun n m h => SSet.Subcomplex.preimage_monotone p (hA h)
  have hc : iSup R = ⊤ := by
    ext d x
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ, iff_true]
    have hx : p.app d x ∈ (iSup A).obj d := by rw [hcover]; trivial
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, hn⟩
  have hr : realizationWeakEquivalences (R 0).ι := by
    apply RealizationPrism.exhaustion_initial_weak E R hR hc
    intro n
    have : HomotopicalAlgebra.Fibration ((A n).fromPreimage p) :=
      subcomplex_fromPreimage_fibration (A n) p
    exact (hW n).of_isPullback (subcomplex_preimage_inclusion_isPullback (hA (Nat.zero_le n)) p)
  let h := subcomplex_preimage_isPullback (A 0) p
  rw [← h.isoPullback_inv_fst]
  exact realizationWeakEquivalences.comp_mem _ _ (realizationWeakEquivalences.of_isIso _) hr

end

end Thomason.Construction

end

end OAI
