import OAI.CategoryTheory.Thomason.Chains.SimplexChainHeight
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Data.Finsupp.Order

namespace OAI

section

/-! # Natural barycentric coordinates on the vertices of a simplicial set -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

def vertexOperator {n : ℕ} (i : Fin (n+1)) : SimplexCategory.mk 0 ⟶ .mk n :=
  SimplexCategory.Hom.mk (OrderHom.const _ i)

theorem vertexOperator_comp {m n : ℕ} (f : SimplexCategory.mk m ⟶ .mk n)
    (i : Fin (m+1)) : vertexOperator i ≫ f = vertexOperator (f.toOrderHom i) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  rfl

def simplexVertex (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (i : Fin (n+1)) : K.obj (.op (.mk 0)) :=
  K.map (vertexOperator i).op s

theorem simplexVertex_map (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n))) (i : Fin (m+1)) :
    simplexVertex K (K.map f.op s) i = simplexVertex K s (f.toOrderHom i) := by
  change (K.map f.op ≫ K.map (vertexOperator i).op) s = _
  rw [← K.map_comp, ← op_comp, vertexOperator_comp]
  rfl

theorem simplexVertex_naturality {K L : SSet.{0}} (f : K ⟶ L) {n : ℕ}
    (s : K.obj (.op (.mk n))) (i : Fin (n+1)) :
    simplexVertex L (f.app _ s) i = f.app _ (simplexVertex K s i) :=
  (ConcreteCategory.congr_hom (f.naturality (vertexOperator i).op) s).symm

/-- Repeated vertices receive the sum of their barycentric coordinates. -/
def simplexVertexCoordinates (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n))) :
    C(StdSimplex ℝ (Fin (n+1)), StdSimplex ℝ (K.obj (.op (.mk 0)))) :=
  ⟨StdSimplex.map (simplexVertex K s), StdSimplex.continuous_map ℝ _⟩

theorem simplexVertexCoordinates_map (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1))) :
    simplexVertexCoordinates K (K.map f.op s) x =
      simplexVertexCoordinates K s (StdSimplex.map f.toOrderHom x) := by
  change StdSimplex.map (simplexVertex K (K.map f.op s)) x =
    StdSimplex.map (simplexVertex K s) (StdSimplex.map f.toOrderHom x)
  rw [← StdSimplex.map_comp]
  congr 1
  funext i
  exact simplexVertex_map K f s i

theorem simplexVertexCoordinates_naturality {K L : SSet.{0}} (f : K ⟶ L) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexVertexCoordinates L (f.app _ s) x =
      StdSimplex.map (f.app (.op (.mk 0))) (simplexVertexCoordinates K s x) := by
  change StdSimplex.map (simplexVertex L (f.app _ s)) x =
    StdSimplex.map (f.app (.op (.mk 0))) (StdSimplex.map (simplexVertex K s) x)
  rw [← StdSimplex.map_comp]
  congr 1
  funext i
  exact simplexVertex_naturality f s i

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Continuous vertex coordinates on actual simplicial realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

noncomputable section

def vertexCoordinateCocone (K : SSet.{0}) : Cocone (diagram K) where
  pt := TopCat.of (StdSimplex ℝ (K.obj (.op (.mk 0))))
  ι := {
    app j := TopCat.ofHom ((simplexVertexCoordinates K (SSet.yonedaEquiv j.hom)).comp
      ⟨ULift.down, continuous_uliftDown⟩)
    naturality j k f := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      have hs : K.map f.left.op (SSet.yonedaEquiv k.hom) = SSet.yonedaEquiv j.hom := by
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
      change simplexVertexCoordinates K (SSet.yonedaEquiv k.hom)
          (StdSimplex.map f.left.toOrderHom p.down) =
        simplexVertexCoordinates K (SSet.yonedaEquiv j.hom) p.down
      rw [← simplexVertexCoordinates_map, hs] }

/-- The barycentric mass at each vertex, with repeated vertices combined.
    The target has finite support even when `K` has infinitely many vertices. -/
def vertexCoordinates (K : SSet.{0}) :
    C(SSet.toTop.obj K, StdSimplex ℝ (K.obj (.op (.mk 0)))) :=
  ((isColimit K).desc (vertexCoordinateCocone K)).hom

theorem vertexCoordinates_leg (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K)
    (p : (diagram K).obj j) :
    vertexCoordinates K ((leg K j).hom p) =
      simplexVertexCoordinates K (SSet.yonedaEquiv j.hom) p.down :=
  ConcreteCategory.congr_hom ((isColimit K).fac (vertexCoordinateCocone K) j) p

theorem vertexCoordinates_simplexPoint (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (p : StdSimplex ℝ (Fin (n+1))) :
    vertexCoordinates K (simplexPoint K s p) = simplexVertexCoordinates K s p := by
  have h := vertexCoordinates_leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm s)) (ULift.up p)
  change vertexCoordinates K (simplexPoint K s p) =
    simplexVertexCoordinates K (SSet.yonedaEquiv (SSet.yonedaEquiv.symm s)) p at h
  rwa [SSet.yonedaEquiv.apply_symm_apply] at h

/-- Vertex coordinates commute with every actual simplicial map. -/
theorem vertexCoordinates_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (x : SSet.toTop.obj K) :
    vertexCoordinates L ((SSet.toTop.map f).hom x) =
      StdSimplex.map (f.app (.op (.mk 0))) (vertexCoordinates K x) := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [simplexPoint_naturality, vertexCoordinates_simplexPoint, vertexCoordinates_simplexPoint]
  exact simplexVertexCoordinates_naturality f s p

end

end Thomason.Construction.RealizationPrism

end

section

/-! # The canonical open vertex cover of actual realization

Only openness and the explicit support criterion are asserted. A vertex
star of a general simplicial set need not be contractible.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

def vertexStar (K : SSet.{0}) (v : K.obj (.op (.mk 0))) : Set (SSet.toTop.obj K) :=
  Set.ofPred (fun x => 0 < (vertexCoordinates K x).weights v)

theorem vertexStar_isOpen (K : SSet.{0}) (v : K.obj (.op (.mk 0))) :
    IsOpen (vertexStar K v) :=
  isOpen_lt continuous_const ((StdSimplex.continuous_weights_apply ℝ v).comp
    (vertexCoordinates K).continuous)

/-- Every point lies in the star of one of its positive-mass vertices. -/
theorem vertexStar_cover (K : SSet.{0}) : ⋃ v, vertexStar K v = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  let u := vertexCoordinates K x
  have hn : u.weights.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro he
    have ht := u.total
    rw [he] at ht
    simp at ht
  obtain ⟨v, hv⟩ := hn
  refine Set.mem_iUnion.mpr ⟨v, ?_⟩
  exact lt_of_le_of_ne (u.nonneg v) (Ne.symm (Finsupp.mem_support_iff.mp hv))

/-- On each characteristic simplex, the star criterion is exactly that
    some positive coordinate is assigned to the indicated vertex. -/
theorem simplexPoint_mem_vertexStar_iff (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (p : StdSimplex ℝ (Fin (n+1)))
    (v : K.obj (.op (.mk 0))) :
    simplexPoint K s p ∈ vertexStar K v ↔
      ∃ i, 0 < p.weights i ∧ simplexVertex K s i = v := by
  classical
  change 0 < (vertexCoordinates K (simplexPoint K s p)).weights v ↔ _
  rw [vertexCoordinates_simplexPoint]
  have hs : (simplexVertexCoordinates K s p).weights.support =
      p.weights.support.image (simplexVertex K s) :=
    Finsupp.support_mapDomain_of_nonneg p.nonneg _
  constructor
  · intro hv
    have hm := Finsupp.mem_support_iff.mpr (ne_of_gt hv)
    rw [hs] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact ⟨i, lt_of_le_of_ne (p.nonneg i) (Ne.symm (Finsupp.mem_support_iff.mp hi)), he⟩
  · rintro ⟨i, hi, he⟩
    have hm : v ∈ (simplexVertexCoordinates K s p).weights.support := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr (ne_of_gt hi), he⟩
    exact lt_of_le_of_ne ((simplexVertexCoordinates K s p).nonneg v)
      (Ne.symm (Finsupp.mem_support_iff.mp hm))

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Actual weak equivalences from explicit simplicial homotopy inverses -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The specified simplicial homotopy inverses realize to actual continuous
homotopy inverses, with those same forward and inverse maps. -/
def realizedHomotopyEquivOfSimplicial {X Y : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H : SSet.Homotopy (𝟙 X) (f ≫ g)) (K : SSet.Homotopy (𝟙 Y) (g ≫ f)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map f).hom
  invFun := (SSet.toTop.map g).hom
  left_inv := ⟨(RealizedCylinder.homotopy H).symm.cast
    (by rw [SSet.toTop.map_comp]; rfl) (by rw [SSet.toTop.map_id]; rfl)⟩
  right_inv := ⟨(RealizedCylinder.homotopy K).symm.cast
    (by rw [SSet.toTop.map_comp]; rfl) (by rw [SSet.toTop.map_id]; rfl)⟩

/-- A constructed simplicial homotopy inverse gives the full actual weak
homotopy-equivalence test, independently of the Kan–Quillen model input. -/
theorem simplicial_homotopy_inverse_weak_pair {X Y : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H : SSet.Homotopy (𝟙 X) (f ≫ g)) (K : SSet.Homotopy (𝟙 Y) (g ≫ f)) :
    realizationWeakEquivalences f ∧ realizationWeakEquivalences g :=
  ⟨homotopyEquiv_isWeakHomotopyEquivalence (realizedHomotopyEquivOfSimplicial f g H K),
    homotopyEquiv_isWeakHomotopyEquivalence (realizedHomotopyEquivOfSimplicial g f K H)⟩

end

end Thomason.Construction

end

section

/-! # Base change preserves simplicial homotopies over the fixed base -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- The actual pullback map of a morphism over a fixed base. -/
def overBaseChangeMap {E F A B : SSet.{0}} (p : E ⟶ B) (q : F ⟶ B) (g : A ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) : pullback p g ⟶ pullback q g :=
  pullback.lift (pullback.fst p g ≫ f) (pullback.snd p g) (by
    rw [Category.assoc, hf, pullback.condition])

@[reassoc] theorem overBaseChangeMap_fst {E F A B : SSet.{0}}
    (p : E ⟶ B) (q : F ⟶ B) (g : A ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    overBaseChangeMap p q g f hf ≫ pullback.fst q g = pullback.fst p g ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc] theorem overBaseChangeMap_snd {E F A B : SSet.{0}}
    (p : E ⟶ B) (q : F ⟶ B) (g : A ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    overBaseChangeMap p q g f hf ≫ pullback.snd q g = pullback.snd p g :=
  pullback.lift_snd _ _ _

theorem overBaseChangeMap_id {E A B : SSet.{0}} (p : E ⟶ B) (g : A ⟶ B) :
    overBaseChangeMap p p g (𝟙 E) (Category.id_comp p) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [overBaseChangeMap_fst, overBaseChangeMap_snd, Category.comp_id, Category.id_comp]

theorem overBaseChangeMap_comp {E F G A B : SSet.{0}}
    (p : E ⟶ B) (q : F ⟶ B) (r : G ⟶ B) (g : A ⟶ B)
    (f : E ⟶ F) (k : F ⟶ G) (hf : f ≫ q = p) (hk : k ≫ r = q) :
    overBaseChangeMap p r g (f ≫ k) (by rw [Category.assoc, hk, hf]) =
      overBaseChangeMap p q g f hf ≫ overBaseChangeMap q r g k hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, overBaseChangeMap_fst, overBaseChangeMap_fst_assoc]
  · simp only [Category.assoc, overBaseChangeMap_snd]

/-- A homotopy over the base pulls back to an actual simplicial homotopy.
It does not require a fibration or preservation of pullbacks by realization. -/
def overBaseChangeHomotopy {E F A B : SSet.{0}}
    (p : E ⟶ B) (q : F ⟶ B) (g : A ⟶ B) {f₀ f₁ : E ⟶ F}
    (h₀ : f₀ ≫ q = p) (h₁ : f₁ ≫ q = p) (H : SSet.Homotopy f₀ f₁)
    (hH : H.h ≫ q = fst E Δ[1] ≫ p) :
    SSet.Homotopy (overBaseChangeMap p q g f₀ h₀) (overBaseChangeMap p q g f₁ h₁) := by
  let P := pullback p g
  let a : P ⊗ Δ[1] ⟶ F := (pullback.fst p g) ▷ Δ[1] ≫ H.h
  let b : P ⊗ Δ[1] ⟶ A := fst P Δ[1] ≫ pullback.snd p g
  have hab : a ≫ q = b ≫ g := by
    dsimp only [a, b]
    rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst,
      Category.assoc, pullback.condition, ← Category.assoc]
  let l : P ⊗ Δ[1] ⟶ pullback q g := pullback.lift a b hab
  have hn₀ : SSet.ι₀ ≫ (pullback.fst p g) ▷ (Δ[1] : SSet.{0}) =
      pullback.fst p g ≫ SSet.ι₀ := by
    apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hn₁ : SSet.ι₁ ≫ (pullback.fst p g) ▷ (Δ[1] : SSet.{0}) =
      pullback.fst p g ≫ SSet.ι₁ := by
    apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  refine { h := l, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ l = overBaseChangeMap p q g f₀ h₀
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, overBaseChangeMap_fst]
      dsimp only [a]
      rw [← Category.assoc, hn₀, Category.assoc, H.h₀]
    · rw [Category.assoc, pullback.lift_snd, overBaseChangeMap_snd]
      dsimp only [b]
      rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  · change SSet.ι₁ ≫ l = overBaseChangeMap p q g f₁ h₁
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, overBaseChangeMap_fst]
      dsimp only [a]
      rw [← Category.assoc, hn₁, Category.assoc, H.h₁]
    · rw [Category.assoc, pullback.lift_snd, overBaseChangeMap_snd]
      dsimp only [b]
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  · apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Fibrewise simplicial homotopy inverses stay inverse after arbitrary
base change, hence their actual base-change maps are weak equivalences. -/
theorem overBaseChange_homotopy_inverse_weak {E F A B : SSet.{0}}
    (p : E ⟶ B) (q : F ⟶ B) (g : A ⟶ B)
    (f : E ⟶ F) (r : F ⟶ E) (hf : f ≫ q = p) (hr : r ≫ p = q)
    (H : SSet.Homotopy (𝟙 E) (f ≫ r)) (K : SSet.Homotopy (𝟙 F) (r ≫ f))
    (hH : H.h ≫ p = fst E Δ[1] ≫ p) (hK : K.h ≫ q = fst F Δ[1] ≫ q) :
    realizationWeakEquivalences (overBaseChangeMap p q g f hf) ∧
      realizationWeakEquivalences (overBaseChangeMap q p g r hr) := by
  have H' := overBaseChangeHomotopy p p g (Category.id_comp p)
    (by rw [Category.assoc, hr, hf]) H hH
  have K' := overBaseChangeHomotopy q q g (Category.id_comp q)
    (by rw [Category.assoc, hf, hr]) K hK
  rw [overBaseChangeMap_id, overBaseChangeMap_comp p q p g f r hf hr] at H'
  rw [overBaseChangeMap_id, overBaseChangeMap_comp q p q g r f hr hf] at K'
  exact simplicial_homotopy_inverse_weak_pair _ _ H' K'

end

end Thomason.Construction

end

section

/-! # Natural transformations induce homotopies of ordinary nerves

The prism is the uncurried functor associated to a natural
transformation regarded as a one-arrow diagram of functors.
-/

namespace Thomason.Construction

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

variable {C D : Type} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D}

def naturalTransformationPrism (α : F ⟶ G) : Fin 2 × C ⥤ D :=
  Functor.uncurry.obj (ComposableArrows.mk₁ α)

theorem naturalTransformationPrism_zero (α : F ⟶ G) :
    (((Functor.const C).obj (0 : Fin 2)).prod' (𝟭 C)) ⋙ naturalTransformationPrism α = F := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  intro X Y f
  change ((ComposableArrows.mk₁ α).map (𝟙 (0 : Fin 2))).app X ≫ F.map f =
    𝟙 _ ≫ F.map f ≫ 𝟙 _
  simp

theorem naturalTransformationPrism_one (α : F ⟶ G) :
    (((Functor.const C).obj (1 : Fin 2)).prod' (𝟭 C)) ⋙ naturalTransformationPrism α = G := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  intro X Y f
  change ((ComposableArrows.mk₁ α).map (𝟙 (1 : Fin 2))).app X ≫ G.map f =
    𝟙 _ ≫ G.map f ≫ 𝟙 _
  simp

/-- A natural transformation gives an actual simplicial interval homotopy. -/
def nerveNaturalHomotopy (α : F ⟶ G) :
    SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := {
    app d := ↾fun x =>
      ((SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone.functor.prod' x.1) ⋙
        naturalTransformationPrism α
    naturality _ _ _ := by
      apply ConcreteCategory.hom_ext
      intro x
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    change (((Functor.const _).obj (0 : Fin 2)).prod' s) ⋙
      naturalTransformationPrism α = s ⋙ F
    exact congrArg (s ⋙ ·) (naturalTransformationPrism_zero α)
  h₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    change (((Functor.const _).obj (1 : Fin 2)).prod' s) ⋙
      naturalTransformationPrism α = s ⋙ G
    exact congrArg (s ⋙ ·) (naturalTransformationPrism_one α)
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Natural transformations preserve the actual realization weak test. -/
theorem nerveNaturalHomotopy_weak_iff (α : F ⟶ G) :
    realizationWeakEquivalences (nerveMap F) ↔ realizationWeakEquivalences (nerveMap G) :=
  RealizedCylinder.weakEquivalence_iff (nerveNaturalHomotopy α)

end

end Thomason.Construction

end

section

/-! # Contracting the face-simplex resolution of a standard simplex

Append the final vertex to every simplex. Prefix inclusions give
`id → append`, and the new final vertex gives `constant → append`.
The resulting actual nerve homotopies prove the augmentation weak.
-/

namespace Thomason.Construction.FaceSimplexResolution.Append

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section


def semiMap {a b : SemiSimplexCategory} (f : a ⟶ b) :
    SemiSimplexCategory.mk (a.len+1) ⟶ SemiSimplexCategory.mk (b.len+1) :=
  SemiSimplexCategory.homEquiv.symm
    (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv f))

@[simp]
theorem semiMap_castSucc {a b : SemiSimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len+1)) :
    (SemiSimplexCategory.toSimplexCategory.map (semiMap f)).toOrderHom i.castSucc =
      ((SemiSimplexCategory.toSimplexCategory.map f).toOrderHom i).castSucc :=
  SimplexComplex.coneBasis_castSucc _ _

@[simp]
theorem semiMap_last {a b : SemiSimplexCategory} (f : a ⟶ b) :
    (SemiSimplexCategory.toSimplexCategory.map (semiMap f)).toOrderHom (Fin.last (a.len+1)) =
      Fin.last (b.len+1) := SimplexComplex.coneBasis_last _

@[simp]
theorem semiMap_id (a : SemiSimplexCategory) : semiMap (𝟙 a) = 𝟙 _ := by
  apply SemiSimplexCategory.homEquiv.injective
  apply DFunLike.ext
  intro i
  change (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv (𝟙 a))) i = i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

@[simp]
theorem semiMap_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    semiMap (f ≫ g) = semiMap f ≫ semiMap g := by
  apply SemiSimplexCategory.homEquiv.injective
  apply DFunLike.ext
  intro i
  change (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv (f ≫ g))) i =
    (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv g))
      ((SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv f)) i)
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

abbrev object {n : SimplexCategory} {m : ℕ} (f : SimplexCategory.mk m ⟶ n) :
    Face (SSet.stdSimplex.obj n) :=
  op { obj := op (SemiSimplexCategory.mk m)
       val := SSet.stdSimplex.objEquiv.symm f }

def operator {n : SimplexCategory} (a : Face (SSet.stdSimplex.obj n)) :
    (projection (SSet.stdSimplex.obj n)).obj a ⟶ n := SSet.stdSimplex.objEquiv (cell a)

theorem operator_naturality {n : SimplexCategory} {a b : Face (SSet.stdSimplex.obj n)}
    (f : a ⟶ b) : (projection (SSet.stdSimplex.obj n)).map f ≫ operator b = operator a :=
  congrArg SSet.stdSimplex.objEquiv (cell_map f)

def appendedOperator {n : SimplexCategory} (a : Face (SSet.stdSimplex.obj n)) :
    SimplexCategory.mk (((projection (SSet.stdSimplex.obj n)).obj a).len+1) ⟶ n :=
  SimplexCategory.Hom.mk (SimplexComplex.append (operator a).toOrderHom
    (Fin.last n.len) (Fin.le_last _))

abbrev appendedObject {n : SimplexCategory} (a : Face (SSet.stdSimplex.obj n)) :
    Face (SSet.stdSimplex.obj n) := object (appendedOperator a)

def homOfSemi {n : SimplexCategory} {a b : Face (SSet.stdSimplex.obj n)}
    (u : a.unop.obj.unop ⟶ b.unop.obj.unop)
    (hu : SemiSimplexCategory.toSimplexCategory.map u ≫ operator b = operator a) : a ⟶ b :=
  Quiver.Hom.op {
    hom := u.op
    map_val := by
      apply SSet.stdSimplex.objEquiv.injective
      exact hu }

@[simp]
theorem homOfSemi_projection {n : SimplexCategory} {a b : Face (SSet.stdSimplex.obj n)}
    (u : a.unop.obj.unop ⟶ b.unop.obj.unop)
    (hu : SemiSimplexCategory.toSimplexCategory.map u ≫ operator b = operator a) :
    (projection (SSet.stdSimplex.obj n)).map (homOfSemi u hu) =
      SemiSimplexCategory.toSimplexCategory.map u := rfl

theorem hom_ext {X : SSet.{0}} {a b : Face X} {f g : a ⟶ b}
    (h : (projection X).map f = (projection X).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  apply Quiver.Hom.unop_inj
  exact SemiSimplexCategory.toSimplexCategory.map_injective h

theorem appendedOperator_naturality {n : SimplexCategory}
    {a b : Face (SSet.stdSimplex.obj n)} (f : a ⟶ b) :
    SemiSimplexCategory.toSimplexCategory.map (semiMap f.unop.hom.unop) ≫
      appendedOperator b = appendedOperator a := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (SimplexComplex.append (operator b).toOrderHom (Fin.last n.len) (Fin.le_last _))
    ((SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv f.unop.hom.unop)) i) =
      (SimplexComplex.append (operator a).toOrderHom (Fin.last n.len) (Fin.le_last _)) i
  change Fin (a.unop.obj.unop.len + 1 + 1) at i
  induction i using Fin.lastCases with
  | last =>
      rw [SimplexComplex.coneBasis_last]
      exact (SimplexComplex.append_last (n := n.len) (p := b.unop.obj.unop.len)
        (operator b).toOrderHom (Fin.last n.len) (Fin.le_last _)).trans
        (SimplexComplex.append_last (n := n.len) (p := a.unop.obj.unop.len)
          (operator a).toOrderHom (Fin.last n.len) (Fin.le_last _)).symm
  | cast i =>
      rw [SimplexComplex.coneBasis_castSucc]
      exact (SimplexComplex.append_castSucc (n := n.len) (p := b.unop.obj.unop.len)
        (operator b).toOrderHom (Fin.last n.len) (Fin.le_last _)
        ((SemiSimplexCategory.homEquiv f.unop.hom.unop) i)).trans
        ((congrArg (fun g => g.toOrderHom i) (operator_naturality f)).trans
          (SimplexComplex.append_castSucc (n := n.len) (p := a.unop.obj.unop.len)
            (operator a).toOrderHom (Fin.last n.len) (Fin.le_last _) i).symm)

def appendedMap {n : SimplexCategory} {a b : Face (SSet.stdSimplex.obj n)} (f : a ⟶ b) :
    appendedObject a ⟶ appendedObject b :=
  homOfSemi (semiMap f.unop.hom.unop) (appendedOperator_naturality f)

def functor (n : SimplexCategory) : Face (SSet.stdSimplex.obj n) ⥤ Face (SSet.stdSimplex.obj n) where
  obj := appendedObject
  map := appendedMap
  map_id a := by
    apply hom_ext
    change SemiSimplexCategory.toSimplexCategory.map (semiMap (𝟙 a.unop.obj.unop)) = 𝟙 _
    rw [semiMap_id]
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    apply hom_ext
    change SemiSimplexCategory.toSimplexCategory.map (semiMap (f.unop.hom.unop ≫ g.unop.hom.unop)) =
      SemiSimplexCategory.toSimplexCategory.map (semiMap f.unop.hom.unop) ≫
        SemiSimplexCategory.toSimplexCategory.map (semiMap g.unop.hom.unop)
    rw [semiMap_comp, Functor.map_comp]

def prefixSemi (m : ℕ) : SemiSimplexCategory.mk m ⟶ SemiSimplexCategory.mk (m+1) :=
  SemiSimplexCategory.homEquiv.symm Fin.castSuccOrderEmb

def prefixMap {n : SimplexCategory} (a : Face (SSet.stdSimplex.obj n)) : a ⟶ appendedObject a :=
  homOfSemi (prefixSemi a.unop.obj.unop.len) (by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change (SimplexComplex.append (operator a).toOrderHom (Fin.last n.len) (Fin.le_last _)) i.castSucc =
      (operator a).toOrderHom i
    exact SimplexComplex.append_castSucc _ _ _ _)

theorem prefixSemi_naturality {a b : SemiSimplexCategory} (f : a ⟶ b) :
    f ≫ prefixSemi b.len = prefixSemi a.len ≫ semiMap f := by
  apply SemiSimplexCategory.homEquiv.injective
  apply DFunLike.ext
  intro i
  change ((SemiSimplexCategory.homEquiv f) i).castSucc =
    (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv f)) i.castSucc
  exact (SimplexComplex.coneBasis_castSucc _ _).symm

def prefixTransformation (n : SimplexCategory) : 𝟭 (Face (SSet.stdSimplex.obj n)) ⟶ functor n where
  app := prefixMap
  naturality a b f := by
    apply hom_ext
    change SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop ≫
        SemiSimplexCategory.toSimplexCategory.map (prefixSemi b.unop.obj.unop.len) =
      SemiSimplexCategory.toSimplexCategory.map (prefixSemi a.unop.obj.unop.len) ≫
        SemiSimplexCategory.toSimplexCategory.map (semiMap f.unop.hom.unop)
    rw [← Functor.map_comp, ← Functor.map_comp, prefixSemi_naturality]

def finalObject (n : SimplexCategory) : Face (SSet.stdSimplex.obj n) :=
  object (SimplexCategory.const (.mk 0) n (Fin.last n.len))

def finalSemi (m : ℕ) : SemiSimplexCategory.mk 0 ⟶ SemiSimplexCategory.mk (m+1) :=
  SemiSimplexCategory.homEquiv.symm (OrderEmbedding.ofStrictMono
    (fun _ : Fin 1 => Fin.last (m+1)) (by
      intro i j h
      change Fin 1 at i j
      have he : i = j := Subsingleton.elim _ _
      exact (ne_of_lt h he).elim))

def finalMap {n : SimplexCategory} (a : Face (SSet.stdSimplex.obj n)) :
    finalObject n ⟶ appendedObject a :=
  homOfSemi (finalSemi a.unop.obj.unop.len) (by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change (SimplexComplex.append (operator a).toOrderHom (Fin.last n.len) (Fin.le_last _))
      (Fin.last (a.unop.obj.unop.len+1)) = Fin.last n.len
    exact SimplexComplex.append_last _ _ _)

theorem finalSemi_naturality {a b : SemiSimplexCategory} (f : a ⟶ b) :
    finalSemi b.len = finalSemi a.len ≫ semiMap f := by
  apply SemiSimplexCategory.homEquiv.injective
  apply DFunLike.ext
  intro i
  change Fin.last (b.len+1) =
    (SimplexComplex.coneBasis (SemiSimplexCategory.homEquiv f)) (Fin.last (a.len+1))
  exact (SimplexComplex.coneBasis_last _).symm

def finalTransformation (n : SimplexCategory) :
    (Functor.const (Face (SSet.stdSimplex.obj n))).obj (finalObject n) ⟶ functor n where
  app := finalMap
  naturality a b f := by
    apply hom_ext
    change 𝟙 _ ≫ SemiSimplexCategory.toSimplexCategory.map (finalSemi b.unop.obj.unop.len) =
      SemiSimplexCategory.toSimplexCategory.map (finalSemi a.unop.obj.unop.len) ≫
        SemiSimplexCategory.toSimplexCategory.map (semiMap f.unop.hom.unop)
    rw [Category.id_comp, ← Functor.map_comp, finalSemi_naturality]

/-- The point collapse of the actual resolution of a standard simplex is weak. -/
theorem collapse_weak (n : SimplexCategory) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (nerve (Face (SSet.stdSimplex.obj n)))) := by
  let C := Face (SSet.stdSimplex.obj n)
  let f : nerve C ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from _
  let g : (Δ[0] : SSet.{0}) ⟶ nerve C := SSet.const (ComposableArrows.mk₀ (finalObject n))
  have wa : realizationWeakEquivalences (nerveMap (functor n)) :=
    (nerveNaturalHomotopy_weak_iff (prefixTransformation n)).mp
      (by
        have he : nerveMap (𝟭 C) = 𝟙 (nerve C) := by ext d s; rfl
        rw [he]
        exact realizationWeakEquivalences.id_mem _)
  have wc : realizationWeakEquivalences
      (nerveMap ((Functor.const C).obj (finalObject n))) :=
    (nerveNaturalHomotopy_weak_iff (finalTransformation n)).mpr wa
  have hfg : f ≫ g = nerveMap ((Functor.const C).obj (finalObject n)) := by
    ext d s
    rfl
  have hgf : g ≫ f = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact (realizationWeakEquivalences_two_out_of_six f g f
    (by rw [hfg]; exact wc) (by rw [hgf]; exact realizationWeakEquivalences.id_mem _)).1

end

end Thomason.Construction.FaceSimplexResolution.Append

namespace Thomason.Construction.FaceSimplexResolution

open CategoryTheory
open scoped Simplicial

/-- The resolution augmentation is weak on every representable, including
all degenerate faces in its face-simplex category. -/
theorem augmentation_standard_weak (n : SimplexCategory) :
    realizationWeakEquivalences (augmentation (SSet.stdSimplex.obj n)) := by
  let t := SSet.stdSimplex.isTerminalObj₀
  have ht : realizationWeakEquivalences (t.from (SSet.stdSimplex.obj n)) := by
    have he : t.from (SSet.stdSimplex.obj n) =
        SSet.stdSimplex.map (SimplexCategory.const n (.mk 0) 0) := t.hom_ext _ _
    rw [he]
    exact realized_simplex_map_weak _
  apply realizationWeakEquivalences.of_postcomp _ (t.from (SSet.stdSimplex.obj n)) ht
  have he : augmentation (SSet.stdSimplex.obj n) ≫ t.from (SSet.stdSimplex.obj n) =
      t.from (nerve (Face (SSet.stdSimplex.obj n))) := t.hom_ext _ _
  rw [he]
  exact Append.collapse_weak n

end Thomason.Construction.FaceSimplexResolution

end

section

/-! # The face-poset comparison over one greatest face

Both sides contract, and the target is the actual characteristic simplex
of the nonsingular target. These are the base cases for finite face gluing.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

variable {X : SSet.{0}} [X.Nonsingular]

omit [X.Nonsingular] in
theorem faceUnion_eq_of_greatest (S : Set X.N) (m : S) (hm : ∀ s : S, s ≤ m) :
    faceUnion S = m.val.subcomplex := by
  apply le_antisymm
  · apply iSup_le
    exact hm
  · exact le_iSup_of_le m le_rfl

/-- The actual collapse from any nerve with a greatest element is weak. -/
theorem greatest_collapse_weak (P : Type) [PartialOrder P]
    (m : P) (hm : ∀ p, p ≤ m) :
    realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve P)) := by
  let f : nerve P ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from _
  let z := NormalizedSimplexIdentities.orderSimplex (OrderHom.const (Fin 1) m)
  let g : (Δ[0] : SSet.{0}) ⟶ nerve P := SSet.const z
  have hc : nerveMap (OrderHom.const P m).monotone.functor =
      SSet.const (X := nerve P) z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl
  have hP : SSet.Homotopy (𝟙 (nerve P)) (f ≫ g) := by
    have H := orderNerveHomotopy (OrderHom.id : P →o P) (OrderHom.const P m) hm
    simpa only [orderNerveMap_id, hc, g, SSet.comp_const] using H
  have hT : SSet.Homotopy (𝟙 (Δ[0] : SSet.{0})) (g ≫ f) := by
    have he : g ≫ f = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [he]
    exact SSet.RelativeMorphism.Homotopy.refl _
  exact (simplicial_homotopy_inverse_weak_pair f g hP hT).1

/-- The comparison is weak over every collection with a greatest face. -/
theorem restrictedMap_weak_of_greatest (S : Set X.N) (m : S)
    (hm : ∀ s : S, s ≤ m) : realizationWeakEquivalences (restrictedMap S) := by
  let e : (faceUnion S).toSSet ≅ (Δ[m.val.dim] : SSet.{0}) :=
    SSet.Subcomplex.eqToIso (faceUnion_eq_of_greatest S m hm) ≪≫
      (SSet.Nonsingular.iso m.val.simplex m.val.nonDegenerate).symm
  let c : (faceUnion S).toSSet ⟶ (Δ[0] : SSet.{0}) := e.hom ≫
    SSet.stdSimplex.map (SimplexCategory.const (.mk m.val.dim) (.mk 0) 0)
  have hc : realizationWeakEquivalences c :=
    realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso e.hom) (realized_simplex_map_weak _)
  apply realizationWeakEquivalences.of_postcomp (restrictedMap S) c hc
  have he : restrictedMap S ≫ c = SSet.stdSimplex.isTerminalObj₀.from (nerve S) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact greatest_collapse_weak S m hm

theorem restrictedMap_weak_of_empty (S : Set X.N) [IsEmpty S] :
    realizationWeakEquivalences (restrictedMap S) := by
  have hs : IsInitial (nerve S) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact isEmptyElim (s.obj 0))
  have he : faceUnion S = ⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro s
    exact isEmptyElim s
  have ht : IsInitial (faceUnion S).toSSet := by
    rw [he]
    exact SSet.Subcomplex.isInitialBot
  have hf : restrictedMap S = (hs.uniqueUpToIso ht).hom := hs.hom_ext _ _
  rw [hf]
  exact realizationWeakEquivalences.of_isIso _

end

end Thomason.Construction.NonsingularLastVertex

end

section

/-! # Composition of the cofibrations used by simplicial gluing -/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

/-- Composition of relative cofibrations follows from the explicit second
pushout square, applied with C equal to the final A. -/
theorem Cofibration.comp {X Y Z : Diagram} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Cofibration f) (hg : Cofibration g) (kq : KanQuillenPublishedInput.{0}) :
    Cofibration (f ≫ g) := by
  have := kq.cofibrationFactorization
  let M := MorphismProperty.monomorphisms SSet.{0}
  have hM : M = (J.rlp ⊓ realizationWeakEquivalences).llp :=
    (MorphismProperty.llp_eq_of_wfs _ _).symm
  have : M.IsStableUnderCobaseChange := by rw [hM]; infer_instance
  have := hf.monoA
  have := hf.monoC
  have := hg.monoA
  have := hg.monoC
  refine ⟨?_, ?_, ?_⟩
  · change Mono (f.a ≫ g.a)
    infer_instance
  · change Mono (f.c ≫ g.c)
    infer_instance
  · let X' : Diagram := ⟨X.A, X.B, Z.A, X.left, f.a ≫ g.a⟩
    let Y' : Diagram := ⟨Y.A, Y.B, Z.A, Y.left, g.a⟩
    let d : X' ⟶ Y' := ⟨f.a, f.b, 𝟙 _, f.left_w, by simp [X', Y']⟩
    have hm : Mono (fromMiddle d) :=
      M.of_isPushout (fromMiddle_isPushout d).flip hf.monoRelative
    have he : relativeB (f ≫ g) = fromMiddle d ≫ relativeB g := by
      change relativeB (Hom.comp f g) = _
      dsimp only [relativeB, Hom.comp, fromMiddle, d, X', Y']
      apply Limits.pushout.hom_ext <;> simp only [Category.assoc,
        Limits.pushout.inl_desc, Limits.pushout.inr_desc,
        Limits.pushout.inl_desc_assoc, Limits.pushout.inr_desc_assoc]
    rw [he]
    have := hg.monoRelative
    exact @mono_comp _ _ _ _ _ (fromMiddle d) hm (relativeB g) hg.monoRelative

/-- Pointwise coproduct of the two spans. -/
noncomputable abbrev sum (X Y : Diagram) : Diagram where
  A := X.A ⨿ Y.A
  B := X.B ⨿ Y.B
  C := X.C ⨿ Y.C
  left := coprod.map X.left Y.left
  right := coprod.map X.right Y.right

noncomputable abbrev inl (X Y : Diagram) : X ⟶ sum X Y :=
  ⟨coprod.inl, coprod.inl, coprod.inl, by simp [sum], by simp [sum]⟩

noncomputable abbrev inr (X Y : Diagram) : Y ⟶ sum X Y :=
  ⟨coprod.inr, coprod.inr, coprod.inr, by simp [sum], by simp [sum]⟩

noncomputable def desc {X Y Z : Diagram} (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
  ⟨coprod.desc f.a g.a, coprod.desc f.b g.b, coprod.desc f.c g.c,
    by apply coprod.hom_ext <;> simp [sum, f.left_w, g.left_w],
    by apply coprod.hom_ext <;> simp [sum, f.right_w, g.right_w]⟩

@[simp] theorem inl_desc {X Y Z : Diagram} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inl X Y ≫ desc f g = f := by
  change Hom.comp (inl X Y) (desc f g) = f
  apply Hom.ext
  · exact coprod.inl_desc _ _
  · exact coprod.inl_desc _ _
  · exact coprod.inl_desc _ _

@[simp] theorem inr_desc {X Y Z : Diagram} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inr X Y ≫ desc f g = g := by
  change Hom.comp (inr X Y) (desc f g) = g
  apply Hom.ext
  · exact coprod.inr_desc _ _
  · exact coprod.inr_desc _ _
  · exact coprod.inr_desc _ _

end Thomason.Construction.SimplicialSpan

end

section

/-! # Coproduct inclusions of the cofibrant span diagrams -/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

theorem inl_relative_isPushout (X Y : Diagram) :
    IsPushout Y.left
      (coprod.inr ≫ Limits.pushout.inr X.left (inl X Y).a)
      (coprod.inr : Y.B ⟶ (sum X Y).B) (relativeB (inl X Y)) := by
  dsimp only [relativeB, inl, sum]
  refine ⟨⟨by simp [Category.assoc, Limits.pushout.inr_desc, coprod.inr_map]⟩, ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s => coprod.desc (Limits.pushout.inl X.left (inl X Y).a ≫ s.inr) s.inl
  · intro s
    simp only [coprod.inr_desc]
  · intro s
    apply Limits.pushout.hom_ext
    · simp only [Limits.pushout.inl_desc_assoc, coprod.inl_desc]
    · rw [Limits.pushout.inr_desc_assoc]
      apply coprod.hom_ext
      · simp only [sum, coprod.inl_map_assoc, coprod.inl_desc]
        rw [← Category.assoc, Limits.pushout.condition]
        simp
      · simp only [sum, coprod.inr_map_assoc, coprod.inr_desc]
        exact s.condition
  · intro s m hm hn
    apply coprod.hom_ext
    · have h := congrArg (fun q => Limits.pushout.inl X.left (inl X Y).a ≫ q) hn
      dsimp only [inl, sum] at h
      simpa only [Category.assoc, Limits.pushout.inl_desc_assoc, coprod.inl_desc, coprod.inr_desc] using h
    · simpa using hm

theorem inr_relative_isPushout (X Y : Diagram) :
    IsPushout X.left
      (coprod.inl ≫ Limits.pushout.inr Y.left (inr X Y).a)
      (coprod.inl : X.B ⟶ (sum X Y).B) (relativeB (inr X Y)) := by
  dsimp only [relativeB, inr, sum]
  refine ⟨⟨by simp [Category.assoc, Limits.pushout.inr_desc, coprod.inl_map]⟩, ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s => coprod.desc s.inl (Limits.pushout.inl Y.left (inr X Y).a ≫ s.inr)
  · intro s
    simp only [coprod.inl_desc]
  · intro s
    apply Limits.pushout.hom_ext
    · simp only [Limits.pushout.inl_desc_assoc, coprod.inr_desc]
    · rw [Limits.pushout.inr_desc_assoc]
      apply coprod.hom_ext
      · simp only [sum, coprod.inl_map_assoc, coprod.inl_desc]
        exact s.condition
      · simp only [sum, coprod.inr_map_assoc, coprod.inr_desc]
        rw [← Category.assoc, Limits.pushout.condition]
        simp
  · intro s m hm hn
    apply coprod.hom_ext
    · simpa using hm
    · have h := congrArg (fun q => Limits.pushout.inl Y.left (inr X Y).a ≫ q) hn
      dsimp only [inr, sum] at h
      simpa only [Category.assoc, Limits.pushout.inl_desc_assoc, coprod.inl_desc, coprod.inr_desc] using h

/-- The other summand needs a monomorphic left leg; there is no restriction
on either right leg. -/
theorem inl_cofibration (X Y : Diagram) [Mono Y.left]
    (kq : KanQuillenPublishedInput.{0}) : Cofibration (inl X Y) := by
  have := kq.cofibrationFactorization
  let M := MorphismProperty.monomorphisms SSet.{0}
  have hM : M = (J.rlp ⊓ realizationWeakEquivalences).llp :=
    (MorphismProperty.llp_eq_of_wfs _ _).symm
  have : M.IsStableUnderCobaseChange := by rw [hM]; infer_instance
  refine ⟨?_, ?_, ?_⟩
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.A Y.A) (by infer_instance)
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.C Y.C) (by infer_instance)
  · exact M.of_isPushout (inl_relative_isPushout X Y).flip (by infer_instance)

theorem inr_cofibration (X Y : Diagram) [Mono X.left]
    (kq : KanQuillenPublishedInput.{0}) : Cofibration (inr X Y) := by
  have := kq.cofibrationFactorization
  let M := MorphismProperty.monomorphisms SSet.{0}
  have hM : M = (J.rlp ⊓ realizationWeakEquivalences).llp :=
    (MorphismProperty.llp_eq_of_wfs _ _).symm
  have : M.IsStableUnderCobaseChange := by rw [hM]; infer_instance
  refine ⟨?_, ?_, ?_⟩
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.A Y.A).flip (by infer_instance)
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.C Y.C).flip (by infer_instance)
  · exact M.of_isPushout (inr_relative_isPushout X Y).flip (by infer_instance)

end Thomason.Construction.SimplicialSpan

end

section

/-! # Weak equivalences detected on the actual skeletal filtration -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

/-- A simplicial map carries the actual `n`-skeleton into the `n`-skeleton. -/
theorem image_skeleton_le {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) :
    (K.skeleton n).image f ≤ L.skeleton n := by
  change (⨆ (i : Fin n) (x : K.nonDegenerate i), SSet.Subcomplex.ofSimplex x.val).image f ≤ _
  simp only [SSet.Subcomplex.image_iSup, iSup_le_iff]
  intro i x
  rw [SSet.Subcomplex.image_ofSimplex]
  exact L.ofSimplex_le_skeleton _ i.isLt

/-- The induced map of skeletal subcomplexes, with its literal inclusion
square rather than an unspecified comparison isomorphism. -/
def skeletalMap {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) :
    (K.skeleton n : SSet) ⟶ (L.skeleton n : SSet) :=
  (K.skeleton n).toImage f ≫ SSet.Subcomplex.homOfLE (image_skeleton_le f n)

theorem skeletalMap_inclusion {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) :
    skeletalMap f n ≫ (L.skeleton n).ι = (K.skeleton n).ι ≫ f := rfl

/-- Stagewise skeletal comparison suffices for all actual homotopy groups,
without a Kan assumption on either simplicial set. -/
theorem realization_weak_of_skeletal {K L : SSet.{0}} (f : K ⟶ L)
    (hf : ∀ n, realizationWeakEquivalences (skeletalMap f n)) :
    realizationWeakEquivalences f :=
  exhaustion_map_weak f K.skeleton L.skeleton K.skeleton.monotone L.skeleton.monotone
    (skeletalMap f) (skeletalMap_inclusion f) K.iSup_skeleton L.iSup_skeleton hf

end

end Thomason.Construction.RealizationPrism

end

end OAI
