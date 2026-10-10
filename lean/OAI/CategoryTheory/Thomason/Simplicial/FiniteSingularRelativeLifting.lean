import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.FiniteKanBaseChangeApproximation
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

namespace OAI

section

/-! # The subdivision-homotopy reduction for the canonical extension

An explicit homotopy between the two last-vertex maps on double subdivision
implies the full canonical-extension weak-equivalence theorem through the
adjunction identities and the two-out-of-six argument.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- The mates of a simplicial homotopy are simplicially homotopic. -/
def subdivisionAdjunctHomotopy {A B : SSet.{0}} {f g : SSet.sd.obj A ⟶ B}
    (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.sdExAdjunction.homEquiv A B f)
      (SSet.sdExAdjunction.homEquiv A B g) where
  h := (SSet.sdExAdjunction.unit.app A ▷ Δ[1]) ≫ (extensionHomotopy H).h
  h₀ := by
    change SSet.ι₀ ≫ ((SSet.sdExAdjunction.unit.app A ▷ Δ[1]) ≫
      (extensionHomotopy H).h) = SSet.sdExAdjunction.homEquiv A B f
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, (extensionHomotopy H).h₀]
    exact (SSet.sdExAdjunction.homEquiv_unit A B f).symm
  h₁ := by
    change SSet.ι₁ ≫ ((SSet.sdExAdjunction.unit.app A ▷ Δ[1]) ≫
      (extensionHomotopy H).h) = SSet.sdExAdjunction.homEquiv A B g
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, (extensionHomotopy H).h₁]
    exact (SSet.sdExAdjunction.homEquiv_unit A B g).symm
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

def postcomposeSimplicialHomotopy {A B C : SSet.{0}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (k : B ⟶ C) : SSet.Homotopy (f ≫ k) (g ≫ k) where
  h := H.h ≫ k
  h₀ := by
    change SSet.ι₀ ≫ (H.h ≫ k) = f ≫ k
    rw [← Category.assoc, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (H.h ≫ k) = g ≫ k
    rw [← Category.assoc, H.h₁]
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

theorem canonicalExtension_adjunct {A B : SSet.{0}} (f : A ⟶ B) :
    SSet.sdExAdjunction.homEquiv A B (lastVertex.app A ≫ f) =
      f ≫ canonicalExtension.app B := by
  have he : SSet.sd.map f ≫ lastVertex.app B = lastVertex.app A ≫ f :=
    lastVertex.naturality f
  calc
    _ = SSet.sdExAdjunction.homEquiv A B (SSet.sd.map f ≫ lastVertex.app B) :=
      congrArg (SSet.sdExAdjunction.homEquiv A B) he.symm
    _ = _ := SSet.sdExAdjunction.homEquiv_naturality_left f (lastVertex.app B)

theorem canonicalExtension_counit (X : SSet.{0}) :
    SSet.sd.map (canonicalExtension.app X) ≫ SSet.sdExAdjunction.counit.app X =
      lastVertex.app X := by
  have h := SSet.sdExAdjunction.homEquiv_counit X X (canonicalExtension.app X)
  exact h.symm.trans ((SSet.sdExAdjunction.homEquiv X X).symm_apply_apply (lastVertex.app X))

/-- A double-subdivision homotopy gives the precise counit composite needed
by the weak-equivalence argument. -/
def canonicalExtensionCounitHomotopy (X : SSet.{0})
    (H : SSet.Homotopy (SSet.sd.map (lastVertex.app (SSet.ex.obj X)))
      (lastVertex.app (SSet.sd.obj (SSet.ex.obj X)))) :
    SSet.Homotopy (lastVertex.app (SSet.ex.obj X))
      (SSet.sdExAdjunction.counit.app X ≫ canonicalExtension.app X) := by
  let c := SSet.sdExAdjunction.counit.app X
  have h₀ : SSet.sdExAdjunction.homEquiv _ _
      (SSet.sd.map (lastVertex.app (SSet.ex.obj X)) ≫ c) =
      lastVertex.app (SSet.ex.obj X) := by
    rw [SSet.sdExAdjunction.homEquiv_naturality_left]
    have hc : SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X
        (c : SSet.sd.obj (SSet.ex.obj X) ⟶ X) = 𝟙 _ := by
      calc
        _ = SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X
            ((SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X).symm (𝟙 _)) :=
          congrArg (SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X)
            (SSet.sdExAdjunction.homEquiv_symm_id X).symm
        _ = _ := (SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X).apply_symm_apply _
    change lastVertex.app (SSet.ex.obj X) ≫
      SSet.sdExAdjunction.homEquiv (SSet.ex.obj X) X
        (c : SSet.sd.obj (SSet.ex.obj X) ⟶ X) = _
    exact (congrArg (fun g => lastVertex.app (SSet.ex.obj X) ≫ g) hc).trans
      (Category.comp_id _)
  have h₁ : SSet.sdExAdjunction.homEquiv _ _
      (lastVertex.app (SSet.sd.obj (SSet.ex.obj X)) ≫ c) =
      c ≫ canonicalExtension.app X := canonicalExtension_adjunct c
  exact h₀ ▸ h₁ ▸ subdivisionAdjunctHomotopy (postcomposeSimplicialHomotopy H c)

/-- Once the explicit subdivision homotopy has been constructed, the
general canonical-extension theorem follows without an approximation
assumption or a Kan--Quillen model structure. -/
theorem canonicalExtension_weak_of_subdivision_homotopy
    (H : ∀ K : SSet.{0}, SSet.Homotopy (SSet.sd.map (lastVertex.app K))
      (lastVertex.app (SSet.sd.obj K))) (X : SSet.{0}) :
    realizationWeakEquivalences (canonicalExtension.app X) := by
  have hab : realizationWeakEquivalences
      (SSet.sd.map (canonicalExtension.app X) ≫ SSet.sdExAdjunction.counit.app X) := by
    rw [canonicalExtension_counit]
    exact lastVertex_weak X
  have hbc : realizationWeakEquivalences
      (SSet.sdExAdjunction.counit.app X ≫ canonicalExtension.app X) :=
    (RealizedCylinder.weakEquivalence_iff
      (canonicalExtensionCounitHomotopy X (H (SSet.ex.obj X)))).mp
        (lastVertex_weak (SSet.ex.obj X))
  exact (realizationWeakEquivalences_two_out_of_six _ _ _ hab hbc).2.2.1

end

end Thomason.Construction

end

section

/-! # Finite carriers remain finite under actual subdivision -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

noncomputable section

theorem finite_nonemptyFiniteChains (P : Type) [PartialOrder P] [Finite P] :
    Finite (NonemptyFiniteChains P) :=
  Finite.of_injective NonemptyFiniteChains.finset
    (fun _ _ h => NonemptyFiniteChains.ext h)

/-- Subdividing a standard simplex still has only finitely many
nondegenerate simplices, not merely finite sets in each degree. -/
theorem subdivision_standard_finite (n : SimplexCategory) :
    (SSet.sd.obj (SSet.stdSimplex.{0}.obj n)).Finite := by
  let := finite_nonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))
  have : (SimplexCategory.sd.{0}.obj n).Finite :=
    PosetGeometry.nerve_finite (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1))))
  exact SSet.finite_of_iso (SSet.stdSimplex.sdIso.symm.app n)

def nondegenerateSimplexFamily (K : SSet.{0}) (s : K.N) : SSet.{0} := Δ[s.dim]

def nondegenerateSimplexCover (K : SSet.{0}) :
    (∐ nondegenerateSimplexFamily K) ⟶ K :=
  Sigma.desc (fun s : K.N => (SSet.yonedaEquiv.symm s.simplex : nondegenerateSimplexFamily K s ⟶ K))

/-- The finite-dimensional generators cover every simplex, including the
original degenerate simplices. -/
theorem nondegenerateSimplexCover_epi (K : SSet.{0}) : Epi (nondegenerateSimplexCover K) := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  apply (CategoryTheory.epi_iff_surjective _).mpr
  intro x
  obtain ⟨m, f, _, s, hs⟩ := K.exists_nonDegenerate x
  let t := SSet.N.mk s.val s.property
  refine ⟨(Sigma.ι (nondegenerateSimplexFamily K) t).app d
    (SSet.stdSimplex.objEquiv.symm f), ?_⟩
  have he := congrArg (fun u => u.app d (SSet.stdSimplex.objEquiv.symm f))
    (Sigma.ι_comp_desc (fun s : K.N => (SSet.yonedaEquiv.symm s.simplex : nondegenerateSimplexFamily K s ⟶ K)) t)
  apply he.trans
  change (SSet.yonedaEquiv.symm s.val).app d
    (SSet.stdSimplex.objEquiv.symm f) = x
  simpa only [SSet.yonedaEquiv_symm_app_objEquiv_symm] using hs.symm

/-- Actual subdivision preserves finite simplicial sets. -/
theorem subdivision_finite (K : SSet.{0}) [K.Finite] : (SSet.sd.obj K).Finite := by
  let Q := ∐ nondegenerateSimplexFamily K
  have : ∀ s : K.N, (SSet.sd.obj (nondegenerateSimplexFamily K s)).Finite :=
    fun s => subdivision_standard_finite ⦋s.dim⦌
  have : (SSet.sd.obj Q).Finite :=
    SSet.finite_of_iso (PreservesCoproduct.iso SSet.sd (nondegenerateSimplexFamily K)).symm
  have := nondegenerateSimplexCover_epi K
  exact SSet.finite_of_epi (SSet.sd.map (nondegenerateSimplexCover K))

/-- The double subdivision used in the Thomason left adjoint also preserves
finite carrier data. -/
theorem subdivision_twice_finite (K : SSet.{0}) [K.Finite] :
    ((SSet.sd ⋙ SSet.sd).obj K).Finite := by
  let := subdivision_finite K
  exact subdivision_finite (SSet.sd.obj K)

end

end Thomason.Construction

end

section

/-! # Finite carriers for the actual extension functor

Adjunction and finiteness of subdivision show that every finite family of
extended simplices comes from a finite subcomplex of the original simplicial
set. Compact realized families consequently have the same finite support.
-/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A finite simplicial family in `Ex K` comes from `Ex A` for an actual
finite subcomplex `A` of `K`. The factorization is an equality of maps. -/
theorem finite_map_extension_factors {T K : SSet.{0}} [T.Finite]
    (f : T ⟶ SSet.ex.obj K) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : T ⟶ SSet.ex.obj A.toSSet, g ≫ SSet.ex.map A.ι = f := by
  let a := (SSet.sdExAdjunction.homEquiv T K).symm f
  let A := SSet.Subcomplex.range a
  have := subdivision_finite T
  have hA : SSet.Finite A.toSSet := inferInstance
  let g := SSet.sdExAdjunction.homEquiv T A.toSSet (SSet.Subcomplex.toRange a)
  refine ⟨A, hA, g, ?_⟩
  calc
    _ = SSet.sdExAdjunction.homEquiv T K (SSet.Subcomplex.toRange a ≫ A.ι) :=
      (SSet.sdExAdjunction.homEquiv_naturality_right (SSet.Subcomplex.toRange a) A.ι).symm
    _ = f := (SSet.sdExAdjunction.homEquiv T K).apply_symm_apply f

/-- Every compact family of points of `|Ex K|` is supported over the
extension of one finite subcomplex of `K`. -/
theorem compact_map_extension_factors {Z : Type} [TopologicalSpace Z] [CompactSpace Z]
    (K : SSet.{0}) (f : C(Z, SSet.toTop.obj (SSet.ex.obj K))) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : C(Z, SSet.toTop.obj (SSet.ex.obj A.toSSet)),
        (SSet.toTop.map (SSet.ex.map A.ι)).hom.comp g = f := by
  obtain ⟨T, hT, u, hu⟩ := RealizationPrism.compact_map_factors _ f
  let := hT
  obtain ⟨A, hA, b, hb⟩ := finite_map_extension_factors T.ι
  refine ⟨A, hA, (SSet.toTop.map b).hom.comp u, ?_⟩
  calc
    _ = (SSet.toTop.map (b ≫ SSet.ex.map A.ι)).hom.comp u := by
      rw [SSet.toTop.map_comp]
      rfl
    _ = f := by rw [hb]; exact hu

end

end Thomason.Construction

end

section

/-! # Finite supports of maps into a subdivision -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

attribute [local instance] subdivision_map_mono

def subdividedSimplexCover (K : SSet.{0}) :
    (∐ fun s : K.N => SSet.sd.obj (nondegenerateSimplexFamily K s)) ⟶ SSet.sd.obj K :=
  sigmaComparison SSet.sd (nondegenerateSimplexFamily K) ≫
    SSet.sd.map (nondegenerateSimplexCover K)

theorem subdividedSimplexCover_epi (K : SSet.{0}) : Epi (subdividedSimplexCover K) := by
  have := nondegenerateSimplexCover_epi K
  unfold subdividedSimplexCover
  infer_instance

theorem subdividedSimplexCover_ι (K : SSet.{0}) (s : K.N) :
    Sigma.ι (fun s : K.N => SSet.sd.obj (nondegenerateSimplexFamily K s)) s ≫
      subdividedSimplexCover K = SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) := by
  rw [subdividedSimplexCover, ← Category.assoc, ι_comp_sigmaComparison,
    ← Functor.map_comp]
  exact congrArg SSet.sd.map (Sigma.ι_comp_desc
    (fun t : K.N => (SSet.yonedaEquiv.symm t.simplex :
      nondegenerateSimplexFamily K t ⟶ K)) s)

/-- Every simplex of a subdivision is already in the subdivided image of a
single finite simplex carrier of the original simplicial set. -/
theorem subdivision_simplex_finite_support (K : SSet.{0})
    (d : SimplexCategoryᵒᵖ) (x : (SSet.sd.obj K).obj d) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      x ∈ (SSet.Subcomplex.range (SSet.sd.map A.ι)).obj d := by
  have := subdividedSimplexCover_epi K
  have hcover : (⨆ s : K.N,
      SSet.Subcomplex.range (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex))) = ⊤ := by
    rw [← SSet.Subcomplex.range_eq_top (subdividedSimplexCover K),
      SSet.range_eq_iSup_sigma_ι]
    simp only [subdividedSimplexCover_ι]
    rfl
  have hx : x ∈ (⨆ s : K.N,
      SSet.Subcomplex.range (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex))).obj d := by
    rw [hcover]
    trivial
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range] at hx
  obtain ⟨s, y, rfl⟩ := hx
  let A := SSet.Subcomplex.ofSimplex s.simplex
  let f : nondegenerateSimplexFamily K s ⟶ A.toSSet :=
    SSet.Subcomplex.toOfSimplex s.simplex
  have hf : f ≫ A.ι = SSet.yonedaEquiv.symm s.simplex := rfl
  refine ⟨A, inferInstance, (SSet.sd.map f).app d y, ?_⟩
  change (SSet.sd.map f ≫ SSet.sd.map A.ι).app d y = _
  rw [← SSet.sd.map_comp, hf]
  rfl

/-- A map with finite source into `Sd K` factors through `Sd A` for an
actual finite subcomplex `A` of `K`. The factorization is exactly simplicial. -/
theorem finite_map_subdivision_factors {T K : SSet.{0}} [T.Finite]
    (f : T ⟶ SSet.sd.obj K) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : T ⟶ SSet.sd.obj A.toSSet, g ≫ SSet.sd.map A.ι = f := by
  classical
  choose A hA hx using fun s : T.N =>
    subdivision_simplex_finite_support K _ (f.app _ s.simplex)
  let B : K.Subcomplex := ⨆ s : T.N, A s
  have hB : SSet.Finite B.toSSet := (SSet.finite_iSup_iff A).mpr hA
  have hr : SSet.Subcomplex.range f ≤ SSet.Subcomplex.range (SSet.sd.map B.ι) := by
    intro d x hx'
    obtain ⟨y, rfl⟩ := hx'
    obtain ⟨m, a, _, s, hs⟩ := T.exists_nonDegenerate y
    let t := SSet.N.mk s.val s.property
    have ht := hx t
    have hle : SSet.Subcomplex.range (SSet.sd.map (A t).ι) ≤
        SSet.Subcomplex.range (SSet.sd.map B.ι) := by
      have he : SSet.sd.map (SSet.Subcomplex.homOfLE (le_iSup A t)) ≫
          SSet.sd.map B.ι = SSet.sd.map (A t).ι := by
        rw [← SSet.sd.map_comp]
        rfl
      rw [← he]
      exact Subfunctor.range_comp_le _ _
    have ht' := hle _ ht
    rw [hs, NatTrans.naturality_apply]
    exact (SSet.Subcomplex.range (SSet.sd.map B.ι)).map a.op ht'
  let q := SSet.Subcomplex.toRange (SSet.sd.map B.ι)
  have hq : IsIso q := inferInstance
  refine ⟨B, hB, SSet.Subcomplex.lift f hr ≫ inv q, ?_⟩
  have he : q ≫ (SSet.Subcomplex.range (SSet.sd.map B.ι)).ι = SSet.sd.map B.ι := rfl
  calc
    _ = (SSet.Subcomplex.lift f hr ≫ inv q) ≫
        (q ≫ (SSet.Subcomplex.range (SSet.sd.map B.ι)).ι) := congrArg _ he.symm
    _ = SSet.Subcomplex.lift f hr ≫
        (SSet.Subcomplex.range (SSet.sd.map B.ι)).ι := by simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = f := rfl

end

end Thomason.Construction

end

section

/-! # Finiteness of maps between the finite simplicial supports in lifting -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A simplicial map is determined by its values on the finitely many
nondegenerate source simplices. -/
theorem finite_simplicial_maps (X Y : SSet.{0}) [X.Finite] [Y.Finite] : Finite (X ⟶ Y) := by
  let e : (X ⟶ Y) → ((s : X.N) → Y.obj (.op (.mk s.dim))) :=
    fun f s => f.app _ s.simplex
  apply Finite.of_injective e
  intro f g h
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨⟨n⟩⟩ := d
  obtain ⟨m, a, _, s, hs⟩ := X.exists_nonDegenerate x
  rw [hs, NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact congrArg (Y.map a.op) (congrFun h (SSet.N.mk s.val s.property))

end

end Thomason.Construction

end

section

/-! # Finite simultaneous stages for actual higher boundary fillers -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- When boundary lifting has been proved for a map, all lifting problems
of bounded dimension between two finite supports have solutions inside
one finite enlargement of the source. All simplices remain in the original
map. The hypothesis is used for the already proved singular cases. -/
theorem finite_boundary_lifting_stage {E B : SSet.{0}} (p : E ⟶ B) (hp : I.rlp p)
    (S : E.Subcomplex) [S.toSSet.Finite] (T : B.Subcomplex) [T.toSSet.Finite] (d : ℕ) :
    ∃ (U : E.Subcomplex) (_ : SSet.Finite U.toSSet) (hSU : S ≤ U),
      U ≤ S ⊔ T.preimage p ∧ ∀ (n : ℕ) (_ : n ≤ d)
        (a : (SSet.boundary n : SSet.{0}) ⟶ S.toSSet)
        (b : (Δ[n] : SSet.{0}) ⟶ T.toSSet)
        (_ : a ≫ S.ι ≫ p = (SSet.boundary n).ι ≫ b ≫ T.ι),
        ∃ l : (Δ[n] : SSet.{0}) ⟶ U.toSSet,
          (SSet.boundary n).ι ≫ l = a ≫ SSet.Subcomplex.homOfLE hSU ∧
          l ≫ U.ι ≫ p = b ≫ T.ι := by
  let Problem := Σ n : Fin (d+1),
    {ab : ((SSet.boundary n.val : SSet.{0}) ⟶ S.toSSet) ×
        ((Δ[n.val] : SSet.{0}) ⟶ T.toSSet) //
      ab.1 ≫ S.ι ≫ p = (SSet.boundary n.val).ι ≫ ab.2 ≫ T.ι}
  have : Finite Problem := by
    have (n : Fin (d+1)) : Finite ((SSet.boundary n.val : SSet.{0}) ⟶ S.toSSet) :=
      finite_simplicial_maps _ _
    have (n : Fin (d+1)) : Finite ((Δ[n.val] : SSet.{0}) ⟶ T.toSSet) :=
      finite_simplicial_maps _ _
    infer_instance
  have (n : ℕ) : HasLiftingProperty (SSet.boundary n).ι p := hp _ (boundary_ι_mem_I n)
  let filler (z : Problem) : (Δ[z.1.val] : SSet.{0}) ⟶ E :=
    (show CommSq (z.2.val.1 ≫ S.ι) (SSet.boundary z.1.val).ι
      p (z.2.val.2 ≫ T.ι) from ⟨by simpa only [Category.assoc] using z.2.property⟩).lift
  have filler_left (z : Problem) :
      (SSet.boundary z.1.val).ι ≫ filler z = z.2.val.1 ≫ S.ι := CommSq.fac_left _
  have filler_right (z : Problem) : filler z ≫ p = z.2.val.2 ≫ T.ι := CommSq.fac_right _
  let V : Problem → E.Subcomplex := fun z => SSet.Subcomplex.range (filler z)
  let U : E.Subcomplex := S ⊔ iSup V
  have hU : SSet.Finite U.toSSet := by
    have : SSet.Finite (iSup V).toSSet := (SSet.finite_iSup_iff V).mpr (fun _ => inferInstance)
    let W : Bool → E.Subcomplex := fun t => if t then S else iSup V
    have he : U = iSup W := by
      apply le_antisymm
      · exact sup_le (le_iSup W true) (le_iSup W false)
      · apply iSup_le
        intro t
        cases t
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff W).mpr
    intro t
    cases t <;> dsimp [W] <;> infer_instance
  have hbound : U ≤ S ⊔ T.preimage p := by
    apply sup_le le_sup_left
    apply iSup_le
    intro z
    apply le_trans (b := T.preimage p) _ le_sup_right
    intro j x hx
    obtain ⟨y, rfl⟩ := hx
    change (filler z ≫ p).app j y ∈ T.obj j
    rw [filler_right]
    exact (z.2.val.2.app j y).property
  refine ⟨U, hU, le_sup_left, hbound, ?_⟩
  intro n hn a b h
  let z : Problem := ⟨⟨n, Nat.lt_succ_of_le hn⟩, ⟨(a, b), h⟩⟩
  let l : (Δ[n] : SSet.{0}) ⟶ U.toSSet :=
    U.lift (filler z) (le_sup_of_le_right (le_iSup V z))
  have hl : l ≫ U.ι = filler z := rfl
  refine ⟨l, ?_, ?_⟩
  · apply (cancel_mono U.ι).mp
    rw [Category.assoc, hl]
    exact filler_left z
  · rw [← Category.assoc, hl, filler_right]

end

end Thomason.Construction

end

section

/-! # Exact finite support in an increasing simplicial exhaustion -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Every map from a finite simplicial set into an increasing union is
already an exact simplicial map into one stage. -/
theorem finite_map_iSup_factors {A E : SSet.{0}} [A.Finite]
    (U : ℕ → E.Subcomplex) (hU : Monotone U) (f : A ⟶ (iSup U).toSSet) :
    ∃ (n : ℕ) (g : A ⟶ (U n).toSSet),
      g ≫ (U n).ι = f ≫ (iSup U).ι := by
  classical
  let F := f ≫ (iSup U).ι
  have hs (s : A.N) : ∃ n, F.app _ s.simplex ∈ (U n).obj _ := by
    have h := (f.app _ s.simplex).property
    change F.app _ s.simplex ∈ (iSup U).obj _ at h
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using h
  choose n hn using hs
  let : Fintype A.N := Fintype.ofFinite _
  let N := Finset.univ.sup n
  have hN (s : A.N) : n s ≤ N := Finset.le_sup (Finset.mem_univ s)
  have hr : SSet.Subcomplex.range F ≤ U N := by
    intro d y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨⟨k⟩⟩ := d
    obtain ⟨m, a, _, s, hs⟩ := A.exists_nonDegenerate x
    let t := SSet.N.mk s.val s.property
    have ht : F.app _ s.val ∈ (U N).obj _ := hU (hN t) _ (hn t)
    rw [hs, NatTrans.naturality_apply]
    exact (U N).map a.op ht
  exact ⟨N, (U N).lift F hr, rfl⟩

end

end Thomason.Construction

end

section

/-! # A boundary-lifting subfibration exhausted by finite supports -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

private structure BoundarySupport {E B : SSet.{0}} (p : E ⟶ B) (T : B.Subcomplex) where
  carrier : E.Subcomplex
  finite : SSet.Finite carrier.toSSet
  liesOver : carrier ≤ T.preimage p

private instance {E B : SSet.{0}} {p : E ⟶ B} {T : B.Subcomplex}
    (S : BoundarySupport p T) : SSet.Finite S.carrier.toSSet := S.finite

private structure BoundaryEnlargement {E B : SSet.{0}} {p : E ⟶ B} {T : B.Subcomplex}
    (S : BoundarySupport p T) (d : ℕ) where
  large : BoundarySupport p T
  le : S.carrier ≤ large.carrier
  lift (n : ℕ) (hn : n ≤ d)
      (a : ((SSet.boundary n) : SSet.{0}) ⟶ S.carrier.toSSet)
      (b : (Δ[n] : SSet.{0}) ⟶ T.toSSet)
      (h : a ≫ S.carrier.ι ≫ p = (SSet.boundary n).ι ≫ b ≫ T.ι) :
      ∃ l : (Δ[n] : SSet.{0}) ⟶ large.carrier.toSSet,
        (SSet.boundary n).ι ≫ l = a ≫ SSet.Subcomplex.homOfLE le ∧
        l ≫ large.carrier.ι ≫ p = b ≫ T.ι

private def boundaryEnlarge {E B : SSet.{0}} {p : E ⟶ B} (hp : I.rlp p)
    {T : B.Subcomplex} [T.toSSet.Finite] (S : BoundarySupport p T) (d : ℕ) :
    BoundaryEnlargement S d := by
  apply Classical.choice
  obtain ⟨U, hU, hSU, hbound, hfill⟩ := finite_boundary_lifting_stage p hp S.carrier T d
  exact ⟨⟨⟨U, hU, hbound.trans (sup_le S.liesOver le_rfl)⟩, hSU, hfill⟩⟩

private def boundarySupportChain {E B : SSet.{0}} {p : E ⟶ B} (hp : I.rlp p)
    {T : B.Subcomplex} [T.toSSet.Finite] (S : BoundarySupport p T) : ℕ → BoundarySupport p T :=
  Nat.rec S (fun n a => (boundaryEnlarge hp a n).large)

private theorem boundarySupportChain_mono {E B : SSet.{0}} {p : E ⟶ B}
    (hp : I.rlp p) {T : B.Subcomplex} [T.toSSet.Finite]
    (S : BoundarySupport p T) : Monotone (fun n => (boundarySupportChain hp S n).carrier) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (boundaryEnlarge hp (boundarySupportChain hp S n) n).le

/-- Every finite subcomplex over a finite base support lies in a genuine
boundary-lifting subfibration of the original map, exhausted by an increasing sequence
of finite subcomplexes. No new simplices outside the original map are added. -/
theorem exists_finite_exhausted_boundary_subfibration {E B : SSet.{0}} (p : E ⟶ B)
    (hp : I.rlp p) (T : B.Subcomplex) [T.toSSet.Finite]
    (S : E.Subcomplex) [S.toSSet.Finite] (hS : S ≤ T.preimage p) :
    ∃ (U : E.Subcomplex) (q : U.toSSet ⟶ T.toSSet),
      S ≤ U ∧ U ≤ T.preimage p ∧ q ≫ T.ι = U.ι ≫ p ∧
      I.rlp q ∧ realizationWeakEquivalences q ∧
      ∃ c : ℕ → E.Subcomplex, Monotone c ∧
        (∀ n, SSet.Finite (c n).toSSet) ∧ c 0 = S ∧ iSup c = U := by
  let S₀ : BoundarySupport p T := ⟨S, inferInstance, hS⟩
  let c : ℕ → E.Subcomplex := fun n => (boundarySupportChain hp S₀ n).carrier
  have hmono : Monotone c := boundarySupportChain_mono hp S₀
  let U : E.Subcomplex := iSup c
  have hU : U ≤ T.preimage p := iSup_le (fun n => (boundarySupportChain hp S₀ n).liesOver)
  let q : U.toSSet ⟶ T.toSSet :=
    SSet.Subcomplex.homOfLE hU ≫ T.fromPreimage p
  have hq : q ≫ T.ι = U.ι ≫ p := by
    dsimp only [q]
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι]
    rfl
  have hqRlp : I.rlp q := by
    intro A D i hi
    obtain ⟨n⟩ := hi
    refine ⟨fun {a b} sq => ?_⟩
    obtain ⟨N, aN, haN⟩ := finite_map_iSup_factors c hmono a
    let M := max N n
    let aM : ((SSet.boundary n) : SSet.{0}) ⟶ (c M).toSSet :=
      aN ≫ SSet.Subcomplex.homOfLE (hmono (le_max_left N n))
    have haM : aM ≫ (c M).ι = a ≫ U.ι := by
      dsimp only [aM]
      rw [Category.assoc]
      exact haN
    have hc : aM ≫ (c M).ι ≫ p = (SSet.boundary n).ι ≫ b ≫ T.ι := by
      rw [← Category.assoc, haM, Category.assoc, ← hq, ← Category.assoc, sq.w,
        Category.assoc]
    obtain ⟨l, hl, hp⟩ := (boundaryEnlarge hp (boundarySupportChain hp S₀ M) M).lift
      n (le_max_right N n) aM b hc
    let d : (Δ[n] : SSet.{0}) ⟶ U.toSSet :=
      l ≫ SSet.Subcomplex.homOfLE (le_iSup c (M+1))
    have hd : d ≫ U.ι = l ≫ (c (M+1)).ι := by
      dsimp only [d]
      rw [Category.assoc]
      rfl
    refine ⟨⟨{ l := d, fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply (cancel_mono U.ι).mp
      rw [Category.assoc, hd]
      change ((SSet.boundary n).ι ≫ l) ≫ (c (M+1)).ι = _
      have he := congrArg (fun z => z ≫ (c (M+1)).ι) hl
      refine he.trans ?_
      rw [Category.assoc]
      exact haM
    · apply (cancel_mono T.ι).mp
      rw [Category.assoc, hq, ← Category.assoc, hd]
      exact hp
  refine ⟨U, q, ?_, hU, hq, hqRlp, boundary_rlp_weak q hqRlp, c, hmono, ?_, rfl, rfl⟩
  · exact le_iSup c 0
  · intro n
    exact (boundarySupportChain hp S₀ n).finite

end

end Thomason.Construction

end

section

/-! # Finite stages containing all prescribed bounded-dimensional Kan fillers -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- From finite source and base supports, a single finite enlargement
contains every Kan horn filler needed up to the specified dimension.
The new simplices are actual simplices of the original total space. -/
theorem finite_kan_horn_stage {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (S : E.Subcomplex) [S.toSSet.Finite]
    (T : B.Subcomplex) [T.toSSet.Finite] (d : ℕ) :
    ∃ (U : E.Subcomplex) (_ : SSet.Finite U.toSSet) (hSU : S ≤ U),
      U ≤ S ⊔ T.preimage p ∧ ∀ (n : ℕ) (_ : n ≤ d) (i : Fin (n+2))
        (a : (Λ[n+1, i] : SSet.{0}) ⟶ S.toSSet)
        (b : (Δ[n+1] : SSet.{0}) ⟶ T.toSSet)
        (_ : a ≫ S.ι ≫ p = Λ[n+1, i].ι ≫ b ≫ T.ι),
        ∃ l : (Δ[n+1] : SSet.{0}) ⟶ U.toSSet,
          Λ[n+1, i].ι ≫ l = a ≫ SSet.Subcomplex.homOfLE hSU ∧
          l ≫ U.ι ≫ p = b ≫ T.ι := by
  let Problem := Σ n : Fin (d+1), Σ i : Fin (n.val+2),
    {ab : ((Λ[n.val+1, i] : SSet.{0}) ⟶ S.toSSet) ×
        ((Δ[n.val+1] : SSet.{0}) ⟶ T.toSSet) //
      ab.1 ≫ S.ι ≫ p = Λ[n.val+1, i].ι ≫ ab.2 ≫ T.ι}
  have hfin : Finite Problem := by
    have (n : Fin (d+1)) (i : Fin (n.val+2)) :
        Finite ((Λ[n.val+1, i] : SSet.{0}) ⟶ S.toSSet) :=
      finite_simplicial_maps _ _
    have (n : Fin (d+1)) : Finite ((Δ[n.val+1] : SSet.{0}) ⟶ T.toSSet) :=
      finite_simplicial_maps _ _
    infer_instance
  have : Finite Problem := hfin
  let filler (z : Problem) : (Δ[z.1.val+1] : SSet.{0}) ⟶ E :=
    (show CommSq (z.2.2.val.1 ≫ S.ι) (Λ[z.1.val+1, z.2.1].ι)
      p (z.2.2.val.2 ≫ T.ι) from ⟨by simpa only [Category.assoc] using z.2.2.property⟩).lift
  have filler_left (z : Problem) :
      Λ[z.1.val+1, z.2.1].ι ≫ filler z = z.2.2.val.1 ≫ S.ι := CommSq.fac_left _
  have filler_right (z : Problem) : filler z ≫ p = z.2.2.val.2 ≫ T.ι := CommSq.fac_right _
  let V : Problem → E.Subcomplex := fun z => SSet.Subcomplex.range (filler z)
  let U : E.Subcomplex := S ⊔ iSup V
  have hU : SSet.Finite U.toSSet := by
    have : SSet.Finite (iSup V).toSSet := (SSet.finite_iSup_iff V).mpr (fun _ => inferInstance)
    let W : Bool → E.Subcomplex := fun t => if t then S else iSup V
    have he : U = iSup W := by
      apply le_antisymm
      · exact sup_le (le_iSup W true) (le_iSup W false)
      · apply iSup_le
        intro t
        cases t
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff W).mpr
    intro t
    cases t <;> dsimp [W] <;> infer_instance
  have hbound : U ≤ S ⊔ T.preimage p := by
    apply sup_le le_sup_left
    apply iSup_le
    intro z
    apply le_trans (b := T.preimage p) _ le_sup_right
    intro j x hx
    obtain ⟨y, rfl⟩ := hx
    change (filler z ≫ p).app j y ∈ T.obj j
    rw [filler_right]
    exact (z.2.2.val.2.app j y).property
  refine ⟨U, hU, le_sup_left, hbound, ?_⟩
  intro n hn i a b h
  let z : Problem := ⟨⟨n, Nat.lt_succ_of_le hn⟩, i, ⟨(a, b), h⟩⟩
  let l : (Δ[n+1] : SSet.{0}) ⟶ U.toSSet :=
    U.lift (filler z) (le_sup_of_le_right (le_iSup V z))
  have hl : l ≫ U.ι = filler z := rfl
  refine ⟨l, ?_, ?_⟩
  · apply (cancel_mono U.ι).mp
    rw [Category.assoc, hl]
    exact filler_left z
  · rw [← Category.assoc, hl, filler_right]

end

end Thomason.Construction

end

section

/-! # A Kan subfibration exhausted by finite supports -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

private structure KanSupport {E B : SSet.{0}} (p : E ⟶ B) (T : B.Subcomplex) where
  carrier : E.Subcomplex
  finite : SSet.Finite carrier.toSSet
  liesOver : carrier ≤ T.preimage p

private instance {E B : SSet.{0}} {p : E ⟶ B} {T : B.Subcomplex}
    (S : KanSupport p T) : SSet.Finite S.carrier.toSSet := S.finite

private structure KanEnlargement {E B : SSet.{0}} {p : E ⟶ B} {T : B.Subcomplex}
    (S : KanSupport p T) (d : ℕ) where
  large : KanSupport p T
  le : S.carrier ≤ large.carrier
  lift (n : ℕ) (hn : n ≤ d) (i : Fin (n+2))
      (a : (Λ[n+1, i] : SSet.{0}) ⟶ S.carrier.toSSet)
      (b : (Δ[n+1] : SSet.{0}) ⟶ T.toSSet)
      (h : a ≫ S.carrier.ι ≫ p = Λ[n+1, i].ι ≫ b ≫ T.ι) :
      ∃ l : (Δ[n+1] : SSet.{0}) ⟶ large.carrier.toSSet,
        Λ[n+1, i].ι ≫ l = a ≫ SSet.Subcomplex.homOfLE le ∧
        l ≫ large.carrier.ι ≫ p = b ≫ T.ι

private def kanEnlarge {E B : SSet.{0}} {p : E ⟶ B} [HomotopicalAlgebra.Fibration p]
    {T : B.Subcomplex} [T.toSSet.Finite] (S : KanSupport p T) (d : ℕ) :
    KanEnlargement S d := by
  apply Classical.choice
  obtain ⟨U, hU, hSU, hbound, hfill⟩ := finite_kan_horn_stage p S.carrier T d
  exact ⟨⟨⟨U, hU, hbound.trans (sup_le S.liesOver le_rfl)⟩, hSU, hfill⟩⟩

private def kanSupportChain {E B : SSet.{0}} {p : E ⟶ B} [HomotopicalAlgebra.Fibration p]
    {T : B.Subcomplex} [T.toSSet.Finite] (S : KanSupport p T) : ℕ → KanSupport p T :=
  Nat.rec S (fun n a => (kanEnlarge a n).large)

private theorem kanSupportChain_mono {E B : SSet.{0}} {p : E ⟶ B}
    [HomotopicalAlgebra.Fibration p] {T : B.Subcomplex} [T.toSSet.Finite]
    (S : KanSupport p T) : Monotone (fun n => (kanSupportChain S n).carrier) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (kanEnlarge (kanSupportChain S n) n).le

/-- Every finite subcomplex over a finite base support lies in a genuine
Kan subfibration of the original map, exhausted by an increasing sequence
of finite subcomplexes. No new simplices outside the original map are added. -/
theorem exists_finite_exhausted_kan_subfibration {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (T : B.Subcomplex) [T.toSSet.Finite]
    (S : E.Subcomplex) [S.toSSet.Finite] (hS : S ≤ T.preimage p) :
    ∃ (U : E.Subcomplex) (q : U.toSSet ⟶ T.toSSet),
      S ≤ U ∧ U ≤ T.preimage p ∧ q ≫ T.ι = U.ι ≫ p ∧
      HomotopicalAlgebra.Fibration q ∧
      ∃ c : ℕ → E.Subcomplex, Monotone c ∧
        (∀ n, SSet.Finite (c n).toSSet) ∧ c 0 = S ∧ iSup c = U := by
  let S₀ : KanSupport p T := ⟨S, inferInstance, hS⟩
  let c : ℕ → E.Subcomplex := fun n => (kanSupportChain S₀ n).carrier
  have hmono : Monotone c := kanSupportChain_mono S₀
  let U : E.Subcomplex := iSup c
  have hU : U ≤ T.preimage p := iSup_le (fun n => (kanSupportChain S₀ n).liesOver)
  let q : U.toSSet ⟶ T.toSSet :=
    SSet.Subcomplex.homOfLE hU ≫ T.fromPreimage p
  have hq : q ≫ T.ι = U.ι ≫ p := by
    dsimp only [q]
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι]
    rfl
  have hqKan : HomotopicalAlgebra.Fibration q := by
    rw [fibration_iff]
    intro A D i hi
    simp only [J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    refine ⟨fun {a b} sq => ?_⟩
    obtain ⟨N, aN, haN⟩ := finite_map_iSup_factors c hmono a
    let M := max N n
    let aM : (Λ[n+1, j] : SSet.{0}) ⟶ (c M).toSSet :=
      aN ≫ SSet.Subcomplex.homOfLE (hmono (le_max_left N n))
    have haM : aM ≫ (c M).ι = a ≫ U.ι := by
      dsimp only [aM]
      rw [Category.assoc]
      exact haN
    have hc : aM ≫ (c M).ι ≫ p = Λ[n+1, j].ι ≫ b ≫ T.ι := by
      rw [← Category.assoc, haM, Category.assoc, ← hq, ← Category.assoc, sq.w,
        Category.assoc]
    obtain ⟨l, hl, hp⟩ := (kanEnlarge (kanSupportChain S₀ M) M).lift
      n (le_max_right N n) j aM b hc
    let d : (Δ[n+1] : SSet.{0}) ⟶ U.toSSet :=
      l ≫ SSet.Subcomplex.homOfLE (le_iSup c (M+1))
    have hd : d ≫ U.ι = l ≫ (c (M+1)).ι := by
      dsimp only [d]
      rw [Category.assoc]
      rfl
    refine ⟨⟨{ l := d, fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply (cancel_mono U.ι).mp
      rw [Category.assoc, hd]
      change (Λ[n+1, j].ι ≫ l) ≫ (c (M+1)).ι = _
      have he := congrArg (fun z => z ≫ (c (M+1)).ι) hl
      refine he.trans ?_
      rw [Category.assoc]
      exact haM
    · apply (cancel_mono T.ι).mp
      rw [Category.assoc, hq, ← Category.assoc, hd]
      exact hp
  refine ⟨U, q, ?_, hU, hq, hqKan, c, hmono, ?_, rfl, rfl⟩
  · exact le_iSup c 0
  · intro n
    exact (kanSupportChain S₀ n).finite

end

end Thomason.Construction

end

section

/-! # Compact homotopy-fibre families lie in finitely exhausted Kan subfibrations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- Compact homotopy-fibre data for a Kan fibration lie in an actual Kan
subfibration over a finite base. Its total space is an increasing union of
finite subcomplexes of the original total space. The entire family retains
its original point and path coordinates. -/
theorem compact_homotopyFiber_kan_support {K : Type} [TopologicalSpace K] [CompactSpace K]
    {E B : SSet.{0}} (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (b : B.obj (.op (.mk 0)))
    (f : C(K, continuousHomotopyFiber (SSet.toTop.map p) (RealizationPrism.vertexPoint B b))) :
    ∃ (A : B.Subcomplex) (_ : SSet.Finite A.toSSet) (U : E.Subcomplex)
      (u : U.toSSet ⟶ A.toSSet) (_ : HomotopicalAlgebra.Fibration u)
      (bA : A.toSSet.obj (.op (.mk 0))),
      u ≫ A.ι = U.ι ≫ p ∧ bA.val = b ∧
      (∃ c : ℕ → E.Subcomplex, Monotone c ∧
        (∀ n, SSet.Finite (c n).toSSet) ∧ iSup c = U) ∧
      ∃ g : C(K, continuousHomotopyFiber (SSet.toTop.map u)
          (RealizationPrism.vertexPoint A.toSSet bA)),
        (∀ k, (SSet.toTop.map U.ι).hom (g k).val.val.1 = (f k).val.val.1) ∧
        (∀ k t, (SSet.toTop.map A.ι).hom ((g k).val.val.2 t) = (f k).val.val.2 t) := by
  obtain ⟨A, hA, L, hL, j, hj, q, bA, hq, hbA, g, hx, ht⟩ :=
    compact_homotopyFiber_finite_arrow p b f
  have : SSet.Finite A.toSSet := hA
  have : SSet.Finite L := hL
  let S : E.Subcomplex := SSet.Subcomplex.range j
  have hS : S ≤ A.preimage p := by
    intro d x hx
    obtain ⟨y, rfl⟩ := hx
    change (j ≫ p).app d y ∈ A.obj d
    rw [← hq]
    exact (q.app d y).property
  obtain ⟨U, u, hSU, _, hu, huKan, c, hc, hfin, _, hcov⟩ :=
    exists_finite_exhausted_kan_subfibration p A S hS
  let k : L ⟶ U.toSSet := U.lift j hSU
  have hk : k ≫ U.ι = j := rfl
  have hku : k ≫ u = q := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hu, ← Category.assoc, hk, hq]
  let v := continuousHomotopyFiberMap (SSet.toTop.map q) (SSet.toTop.map u)
    (SSet.toTop.map k) (𝟙 (SSet.toTop.obj A.toSSet))
    (by rw [← SSet.toTop.map_comp, hku, Category.comp_id])
    (RealizationPrism.vertexPoint A.toSSet bA)
  let gU : C(K, continuousHomotopyFiber (SSet.toTop.map u)
      (RealizationPrism.vertexPoint A.toSSet bA)) := v.hom.comp g
  refine ⟨A, hA, U, u, huKan, bA, hu, hbA, ⟨c, hc, hfin, hcov⟩, gU, ?_, ht⟩
  intro z
  change (SSet.toTop.map U.ι).hom ((SSet.toTop.map k).hom (g z).val.val.1) = _
  have he := congrArg (fun m => m.hom (g z).val.val.1) (SSet.toTop.congr_map hk)
  rw [SSet.toTop.map_comp] at he
  exact he.trans (hx z)

end

end Thomason.Construction

end

section

/-! # Finite-exhausted acyclic carriers for actual singular fibrations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- Finite singular data over a finite base support is contained in an
actual boundary-lifting subfibration, exhausted by finite subcomplexes.
The boundary-lifting hypothesis is discharged here by the proved singular
acyclic theorem; no general simplicial acyclic implication is assumed. -/
theorem finite_singular_boundary_hull {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom)
    (T : (TopCat.toSSet.obj Y).Subcomplex) [T.toSSet.Finite]
    (S : (TopCat.toSSet.obj X).Subcomplex) [S.toSSet.Finite]
    (hS : S ≤ T.preimage (TopCat.toSSet.map p)) :
    ∃ (U : (TopCat.toSSet.obj X).Subcomplex) (q : U.toSSet ⟶ T.toSSet),
      S ≤ U ∧ U ≤ T.preimage (TopCat.toSSet.map p) ∧
      q ≫ T.ι = U.ι ≫ TopCat.toSSet.map p ∧
      I.rlp q ∧ realizationWeakEquivalences q ∧
      ∃ c : ℕ → (TopCat.toSSet.obj X).Subcomplex, Monotone c ∧
        (∀ n, SSet.Finite (c n).toSSet) ∧ c 0 = S ∧ iSup c = U :=
  exists_finite_exhausted_boundary_subfibration (TopCat.toSSet.map p)
    (singular_fibration_boundary_rlp p hp) T S hS

end

end Thomason.Construction

end

section

/-! # Exact finite-base singular weak lifts inside acyclic subfibrations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- A finite relative problem for an actual acyclic singular fibration has
an exact simplicial solution inside a finite-exhausted acyclic subfibration
over one finite base. Both original maps and the entire lifting square
are retained exactly. -/
theorem finite_singular_acyclic_relative_lift {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom)
    {A K : SSet.{0}} [K.Finite] (i : A ⟶ K) [Mono i]
    (a : A ⟶ TopCat.toSSet.obj X) (b : K ⟶ TopCat.toSSet.obj Y)
    (h : a ≫ TopCat.toSSet.map p = i ≫ b) :
    ∃ (T : (TopCat.toSSet.obj Y).Subcomplex) (_ : SSet.Finite T.toSSet)
      (U : (TopCat.toSSet.obj X).Subcomplex) (q : U.toSSet ⟶ T.toSSet),
      I.rlp q ∧ realizationWeakEquivalences q ∧
      ∃ (aU : A ⟶ U.toSSet) (bT : K ⟶ T.toSSet) (l : K ⟶ U.toSSet),
        q ≫ T.ι = U.ι ≫ TopCat.toSSet.map p ∧ aU ≫ U.ι = a ∧ bT ≫ T.ι = b ∧
        i ≫ l = aU ∧ l ≫ q = bT ∧
        ∃ c : ℕ → (TopCat.toSSet.obj X).Subcomplex, Monotone c ∧
          (∀ n, SSet.Finite (c n).toSSet) ∧ iSup c = U := by
  have : A.Finite := SSet.finite_of_mono i
  let S := SSet.Subcomplex.range a
  let T := SSet.Subcomplex.range b
  have hS : S ≤ T.preimage (TopCat.toSSet.map p) := by
    intro d x hx
    obtain ⟨u, rfl⟩ := hx
    change (a ≫ TopCat.toSSet.map p).app d u ∈ T.obj d
    rw [h]
    exact ⟨i.app d u, rfl⟩
  obtain ⟨U, q, hSU, _, hq, hqI, hqW, c, hc, hcf, _, hcu⟩ :=
    finite_singular_boundary_hull p hp T S hS
  let aU : A ⟶ U.toSSet := U.lift a hSU
  let bT : K ⟶ T.toSSet := SSet.Subcomplex.toRange b
  have ha : aU ≫ U.ι = a := rfl
  have hb : bT ≫ T.ι = b := rfl
  have hsquare : aU ≫ q = i ≫ bT := by
    apply (cancel_mono T.ι).mp
    rw [Category.assoc, hq, ← Category.assoc, ha, Category.assoc, hb, h]
  have hqm : (CategoryTheory.MorphismProperty.monomorphisms SSet.{0}).rlp q := by
    rwa [SSet.rlp_monomorphisms]
  have : HasLiftingProperty i q := hqm _ inferInstance
  let sq : CommSq aU i q bT := ⟨hsquare⟩
  exact ⟨T, inferInstance, U, q, hqI, hqW, aU, bT, sq.lift,
    hq, ha, hb, sq.fac_left, sq.fac_right, c, hc, hcf, hcu⟩

end

end Thomason.Construction

end

end OAI
