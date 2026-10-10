import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderPath
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

section

/-! # Identifying the strict globe with its positive chain realization

The canonical globe map is injective as well as surjective: the highest
nonzero chain records the dimension and sign of its unique generator.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev globeDimension {n : ℕ} (s : StrictOmegaCategory.Globe.Cell n) :=
  StrictOmegaCategory.Globe.dimension s

def globeBasis {n : ℕ} (s : StrictOmegaCategory.Globe.Cell n) :
    Basis n (globeDimension s) :=
  match s with
  | .top => ⟨false, Or.inr ⟨rfl, rfl⟩⟩
  | .boundary a k => ⟨a, Or.inl k.isLt⟩

theorem fromGlobe_top_table {n : ℕ} (s : StrictOmegaCategory.Globe.Cell n) :
    chainTable ((fromGlobe n).toFun s) false (globeDimension s) =
      Finsupp.single (globeBasis s) 1 := by
  cases s with
  | top => exact topTable_eq_single n n (globeBasis .top)
  | boundary a k =>
    change Cell.cutTable (topCell n) a k false k = _
    simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
    exact topTable_eq_single n k (globeBasis (.boundary a k))

theorem fromGlobe_dimension_iff {n k : ℕ} (s : StrictOmegaCategory.Globe.Cell n) :
    (complex n).realization.DimensionLE k ((fromGlobe n).toFun s) ↔
      globeDimension s ≤ k := by
  constructor
  · intro hs
    by_contra h
    have hks : k < globeDimension s := Nat.lt_of_not_ge h
    have hz : chainTable ((fromGlobe n).toFun s) false (globeDimension s) = 0 :=
      (Cell.dimensionLE_iff_zero_above ((fromGlobe n).toFun s) k).mp hs
        (globeDimension s) hks false
    rw [fromGlobe_top_table] at hz
    have hc := congrArg (fun u : Chains n (globeDimension s) => u (globeBasis s)) hz
    simp at hc
  · intro hs
    exact (complex n).realization.dimensionLE_mono hs
      (StrictOmegaCategory.Globe.evaluate_dimension _ (topCell n) (topCell_dimension n) s)

/-- Distinct signed globe cells remain distinct after positive realization. -/
theorem fromGlobe_injective (n : ℕ) : Function.Injective (fromGlobe n).toFun := by
  intro s t h
  have hs : (complex n).realization.DimensionLE (globeDimension s) ((fromGlobe n).toFun s) :=
    (fromGlobe_dimension_iff s).mpr le_rfl
  have ht : (complex n).realization.DimensionLE (globeDimension t) ((fromGlobe n).toFun t) :=
    (fromGlobe_dimension_iff t).mpr le_rfl
  have hst : globeDimension s = globeDimension t := by
    have h₁ := (fromGlobe_dimension_iff t).mp (h ▸ hs)
    have h₂ := (fromGlobe_dimension_iff s).mp (h.symm ▸ ht)
    exact Nat.le_antisymm h₂ h₁
  cases s with
  | top =>
    cases t with
    | top => rfl
    | boundary b l => exact False.elim (Nat.ne_of_gt l.isLt hst)
  | boundary a k =>
    cases t with
    | top => exact False.elim (Nat.ne_of_lt k.isLt hst)
    | boundary b l =>
      have hkl : k = l := Fin.ext hst
      subst l
      have hc := congrArg (fun x : Cell (complex n) => chainTable x false k) h
      have he := (fromGlobe_top_table (.boundary a k)).symm.trans
        (hc.trans (fromGlobe_top_table (.boundary b k)))
      have hb : globeBasis (.boundary a k) = globeBasis (.boundary b k) :=
        Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0) he
      have hab : a = b := congrArg Subtype.val hb
      subst b
      rfl

/-- The strict globe and its positive-table realization are isomorphic. -/
def globeIso (n : ℕ) : StrictOmegaCategory.Globe.category n ≅ (complex n).realization :=
  StrictOmegaCategory.isoOfBijective (fromGlobe n)
    ⟨fromGlobe_injective n, fromGlobe_surjective n⟩

@[simp] theorem globeIso_hom (n : ℕ) : (globeIso n).hom = fromGlobe n := rfl

/-- On the free globes, taking strict realization is a full and faithful
bijection of positive chain maps with actual strict functors. -/
def realizationHomEquiv (n : ℕ) (K : DirectedComplex.{0}) :
    Hom (complex n) K ≃ ((complex n).realization ⟶ K.realization) where
  toFun F := F.realization
  invFun f := cellMap n (f.toFun (topCell n))
  left_inv F := cellMap_top_inverse n F
  right_inv f := by
    apply (cancel_epi (globeIso n).hom).mp
    apply StrictOmegaCategory.Globe.hom_ext
    exact cellMap_top_of_bounded n (f.toFun (topCell n))
      (f.dimensionLE (topCell_dimension n))

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Functorial chain presentations on the strict globe parameters

All strict maps between globes lift uniquely to positive chain maps. Their
realizations are naturally isomorphic to the original strict globes. The
right chain cylinder therefore gives a functor on these finite parameters.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictOmegaCategory.Globe

/-- The small category of strict globe parameters and all strict maps. -/
structure Shapes where
  dim : ℕ

instance : SmallCategory Shapes where
  Hom m n := category m.dim ⟶ category n.dim
  id m := 𝟙 (category m.dim)
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

def inclusion : Shapes ⥤ StrictOmegaCategory.{0} where
  obj n := category n.dim
  map f := f

end StrictOmegaCategory.Globe

namespace DirectedGlobeComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- The unique positive map presenting an arbitrary strict globe map. -/
def chainMap {m n : ℕ} (f : StrictOmegaCategory.Globe.category m ⟶
    StrictOmegaCategory.Globe.category n) : Hom (complex m) (complex n) :=
  (realizationHomEquiv m (complex n)).symm
    ((globeIso m).inv ≫ f ≫ (globeIso n).hom)

@[simp] theorem chainMap_realization {m n : ℕ}
    (f : StrictOmegaCategory.Globe.category m ⟶ StrictOmegaCategory.Globe.category n) :
    (chainMap f).realization = (globeIso m).inv ≫ f ≫ (globeIso n).hom :=
  (realizationHomEquiv m (complex n)).apply_symm_apply _

def chainFunctor : StrictOmegaCategory.Globe.Shapes ⥤ DirectedComplex.{0} where
  obj n := complex n.dim
  map f := chainMap (StrictOmegaCategory.Globe.inclusion.map f)
  map_id n := by
    apply (realizationHomEquiv n.dim (complex n.dim)).injective
    change (chainMap (𝟙 _)).realization = (DirectedComplex.Hom.id _).realization
    rw [chainMap_realization]
    simp only [Category.id_comp, Iso.inv_hom_id]
    rfl
  map_comp {l m n} f g := by
    let f' : StrictOmegaCategory.Globe.category l.dim ⟶
        StrictOmegaCategory.Globe.category m.dim := f
    let g' : StrictOmegaCategory.Globe.category m.dim ⟶
        StrictOmegaCategory.Globe.category n.dim := g
    apply (realizationHomEquiv l.dim (complex n.dim)).injective
    change (chainMap (f' ≫ g')).realization =
      StrictOmegaCategory.Hom.comp (chainMap f').realization (chainMap g').realization
    rw [chainMap_realization (f' ≫ g'), chainMap_realization f', chainMap_realization g']
    change (globeIso l.dim).inv ≫ (f' ≫ g') ≫ (globeIso n.dim).hom =
      ((globeIso l.dim).inv ≫ f' ≫ (globeIso m.dim).hom) ≫
        ((globeIso m.dim).inv ≫ g' ≫ (globeIso n.dim).hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The comparison is natural for every strict map between globes. -/
def chainRealizationIso : chainFunctor ⋙ realizationFunctor ≅
    StrictOmegaCategory.Globe.inclusion :=
  NatIso.ofComponents (fun n => (globeIso n.dim).symm) (fun {m n} f => by
    let f' : StrictOmegaCategory.Globe.category m.dim ⟶
        StrictOmegaCategory.Globe.category n.dim := f
    change (chainMap f').realization ≫ (globeIso n.dim).inv = (globeIso m.dim).inv ≫ f'
    rw [chainMap_realization]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- The concrete signed right-cylinder functor on all strict globe maps. -/
def rightGlobeCylinder : StrictOmegaCategory.Globe.Shapes ⥤ StrictOmegaCategory.{0} :=
  chainFunctor ⋙ rightCylinderFunctor ⋙ realizationFunctor

/-- The two endpoint inclusions in the concrete globe cylinders. -/
def rightGlobeEndpoint (a : Bool) : StrictOmegaCategory.Globe.inclusion ⟶
    rightGlobeCylinder where
  app n := (globeIso n.dim).hom ≫ (RightCylinder.endpoint (complex n.dim) a).realization
  naturality m n f := by
    let f' : StrictOmegaCategory.Globe.category m.dim ⟶
        StrictOmegaCategory.Globe.category n.dim := f
    have hf : (globeIso m.dim).hom ≫ (chainMap f').realization =
        f' ≫ (globeIso n.dim).hom := by
      rw [chainMap_realization]
      simp only [Iso.hom_inv_id_assoc]
    have he : StrictOmegaCategory.Hom.comp (chainMap f').realization
        (RightCylinder.endpoint (complex n.dim) a).realization =
      StrictOmegaCategory.Hom.comp (RightCylinder.endpoint (complex m.dim) a).realization
        (RightCylinder.map (chainMap f')).realization := by
      apply StrictOmegaCategory.Hom.ext
      funext x
      apply Cell.ext
      funext b k
      exact (RightCylinder.map_endpoint (chainMap f') a k (x.table b k)).symm
    change f' ≫ ((globeIso n.dim).hom ≫ (RightCylinder.endpoint (complex n.dim) a).realization) =
      ((globeIso m.dim).hom ≫ (RightCylinder.endpoint (complex m.dim) a).realization) ≫
        (RightCylinder.map (chainMap f')).realization
    calc
      _ = ((globeIso m.dim).hom ≫ (chainMap f').realization) ≫
          (RightCylinder.endpoint (complex n.dim) a).realization := by rw [hf, Category.assoc]
      _ = (globeIso m.dim).hom ≫ ((chainMap f').realization ≫
          (RightCylinder.endpoint (complex n.dim) a).realization) := Category.assoc _ _ _
      _ = (globeIso m.dim).hom ≫ ((RightCylinder.endpoint (complex m.dim) a).realization ≫
          (RightCylinder.map (chainMap f')).realization) := congrArg _ he
      _ = _ := (Category.assoc _ _ _).symm

/-- The natural collapse returns the actual strict globe. -/
def rightGlobeProjection : rightGlobeCylinder ⟶ StrictOmegaCategory.Globe.inclusion where
  app n := (RightCylinder.projection (complex n.dim)).realization ≫ (globeIso n.dim).inv
  naturality m n f := by
    let f' : StrictOmegaCategory.Globe.category m.dim ⟶
        StrictOmegaCategory.Globe.category n.dim := f
    have hp : StrictOmegaCategory.Hom.comp (RightCylinder.map (chainMap f')).realization
        (RightCylinder.projection (complex n.dim)).realization =
      StrictOmegaCategory.Hom.comp (RightCylinder.projection (complex m.dim)).realization
        (chainMap f').realization := by
      apply StrictOmegaCategory.Hom.ext
      funext x
      exact RightCylinder.realization_projection_map (chainMap f') x
    have hf : (chainMap f').realization ≫ (globeIso n.dim).inv = (globeIso m.dim).inv ≫ f' := by
      rw [chainMap_realization]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change (RightCylinder.map (chainMap f')).realization ≫
        ((RightCylinder.projection (complex n.dim)).realization ≫ (globeIso n.dim).inv) =
      ((RightCylinder.projection (complex m.dim)).realization ≫ (globeIso m.dim).inv) ≫ f'
    calc
      _ = ((RightCylinder.map (chainMap f')).realization ≫
          (RightCylinder.projection (complex n.dim)).realization) ≫ (globeIso n.dim).inv :=
        (Category.assoc _ _ _).symm
      _ = ((RightCylinder.projection (complex m.dim)).realization ≫
          (chainMap f').realization) ≫ (globeIso n.dim).inv :=
        congrArg (fun q : (rightCylinder (complex m.dim)).realization ⟶
          (complex n.dim).realization => q ≫ (globeIso n.dim).inv) hp
      _ = _ := by rw [Category.assoc, hf, Category.assoc]

theorem rightGlobeEndpoint_projection (a : Bool) (n : StrictOmegaCategory.Globe.Shapes) :
    (rightGlobeEndpoint a).app n ≫ rightGlobeProjection.app n =
      𝟙 (StrictOmegaCategory.Globe.category n.dim) := by
  have he : StrictOmegaCategory.Hom.comp (RightCylinder.endpoint (complex n.dim) a).realization
      (RightCylinder.projection (complex n.dim)).realization =
        𝟙 (complex n.dim).realization := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact RightCylinder.realization_projection_endpoint (complex n.dim) a x
  change ((globeIso n.dim).hom ≫ (RightCylinder.endpoint (complex n.dim) a).realization) ≫
    ((RightCylinder.projection (complex n.dim)).realization ≫ (globeIso n.dim).inv) = _
  calc
    _ = (globeIso n.dim).hom ≫ (((RightCylinder.endpoint (complex n.dim) a).realization ≫
        (RightCylinder.projection (complex n.dim)).realization) ≫ (globeIso n.dim).inv) := by
      simp only [Category.assoc]
    _ = (globeIso n.dim).hom ≫ (𝟙 (complex n.dim).realization ≫ (globeIso n.dim).inv) :=
      congrArg (fun q : (complex n.dim).realization ⟶ (complex n.dim).realization =>
        (globeIso n.dim).hom ≫ (q ≫ (globeIso n.dim).inv)) he
    _ = _ := by simp only [Category.id_comp, Iso.hom_inv_id]

end

end DirectedGlobeComplex

end Thomason.Construction

end

section

/-! # Exact coordinates for the interval tensor of an ordered atom basis

The endpoint and mixed basis is identified with the actual tuple of chain
groups by additive equivalences. This construction uses finite support of
each chain, rather than any finiteness assumption on the whole basis.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

abbrev CylinderIndex (p : ℕ) := RightCylinderBasis.Basis B.Index p

private def zeroIndexEquiv : B.CylinderIndex 0 ≃ (B.Index 0 ⊕ B.Index 0) where
  toFun
    | .endpoint false b => Sum.inl b
    | .endpoint true b => Sum.inr b
  invFun
    | .inl b => .endpoint false b
    | .inr b => .endpoint true b
  left_inv b := by cases b with | endpoint a b => cases a <;> rfl
  right_inv b := by cases b <;> rfl

private def succIndexEquiv (p : ℕ) :
    B.CylinderIndex (p+1) ≃ (B.Index (p+1) ⊕ (B.Index (p+1) ⊕ B.Index p)) where
  toFun
    | .endpoint false b => Sum.inl b
    | .endpoint true b => Sum.inr (Sum.inl b)
    | .mixed b => Sum.inr (Sum.inr b)
  invFun
    | .inl b => .endpoint false b
    | .inr (.inl b) => .endpoint true b
    | .inr (.inr b) => .mixed b
  left_inv b := by cases b with
    | endpoint a b => cases a <;> rfl
    | mixed b => rfl
  right_inv b := by cases b with
    | inl b => rfl
    | inr b => cases b <;> rfl

/-- Coordinates are formed by the actual endpoint and mixed direct sums. -/
noncomputable def cylinderCoordinates : (p : ℕ) →
    (rightCylinder K).group p ≃+ (B.CylinderIndex p →₀ ℤ)
  | 0 =>
    (AddEquiv.prodCongr (B.coordinates 0) (B.coordinates 0)).trans
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm.trans
        (Finsupp.domCongr B.zeroIndexEquiv.symm))
  | p+1 =>
    (AddEquiv.prodCongr (B.coordinates (p+1))
      (AddEquiv.prodCongr (B.coordinates (p+1)) (B.coordinates p))).trans
      ((AddEquiv.prodCongr (AddEquiv.refl _)
        Finsupp.sumFinsuppAddEquivProdFinsupp.symm).trans
        (Finsupp.sumFinsuppAddEquivProdFinsupp.symm.trans
          (Finsupp.domCongr (B.succIndexEquiv p).symm)))

def cylinderCoefficient : {p : ℕ} → B.CylinderIndex p → (rightCylinder K).group p → ℤ
  | 0, .endpoint false b, x => B.coordinates 0 x.1 b
  | 0, .endpoint true b, x => B.coordinates 0 x.2 b
  | p+1, .endpoint false b, x => B.coordinates (p+1) x.1 b
  | p+1, .endpoint true b, x => B.coordinates (p+1) x.2.1 b
  | p+1, .mixed b, x => B.coordinates p x.2.2 b

@[simp] theorem cylinderCoordinates_apply {p : ℕ} (x : (rightCylinder K).group p)
    (b : B.CylinderIndex p) : B.cylinderCoordinates p x b = B.cylinderCoefficient b x := by
  cases p with
  | zero => cases b with | endpoint a b => cases a <;> rfl
  | succ p => cases b with
    | endpoint a b => cases a <;> rfl
    | mixed b => rfl

/-- These exact coordinates characterize the actual positive tensor cone. -/
theorem cylinder_positive_iff (p : ℕ) (x : (rightCylinder K).group p) :
    x ∈ (rightCylinder K).positive p ↔ ∀ b, 0 ≤ B.cylinderCoordinates p x b := by
  cases p with
  | zero =>
    constructor
    · intro hx b
      cases b with
      | endpoint a b =>
        cases a
        · exact B.coordinate_nonnegative 0 x.1 hx.1 b
        · exact B.coordinate_nonnegative 0 x.2 hx.2 b
    · intro hx
      exact ⟨(B.positive_iff 0 x.1).mpr (fun b => hx (.endpoint false b)),
        (B.positive_iff 0 x.2).mpr (fun b => hx (.endpoint true b))⟩
  | succ p =>
    constructor
    · intro hx b
      cases b with
      | endpoint a b =>
        cases a
        · exact B.coordinate_nonnegative (p+1) x.1 hx.1 b
        · exact B.coordinate_nonnegative (p+1) x.2.1 hx.2.1 b
      | mixed b => exact B.coordinate_nonnegative p x.2.2 hx.2.2 b
    · intro hx
      exact ⟨(B.positive_iff (p+1) x.1).mpr (fun b => hx (.endpoint false b)),
        (B.positive_iff (p+1) x.2.1).mpr (fun b => hx (.endpoint true b)),
        (B.positive_iff p x.2.2).mpr (fun b => hx (.mixed b))⟩

/-- The ordinary tensor augmentation is the sum of all degree-zero
coordinates, with neither endpoint omitted. -/
theorem cylinder_augmentation (x : (rightCylinder K).group 0) :
    (rightCylinder K).augmentation x =
      (B.cylinderCoordinates 0 x).sum (fun _ z => z) := by
  change K.augmentation x.1 + K.augmentation x.2 =
    (Finsupp.equivMapDomain B.zeroIndexEquiv.symm
      ((B.coordinates 0 x.1).sumElim (B.coordinates 0 x.2))).sum (fun _ z => z)
  rw [B.augmentation, B.augmentation, Finsupp.sum_equivMapDomain, Finsupp.sum_sumElim]
  rfl

/-- The basis vectors in the actual tensor coordinates. -/
noncomputable def cylinderVector {p : ℕ} (b : B.CylinderIndex p) : (rightCylinder K).group p :=
  (B.cylinderCoordinates p).symm (Finsupp.single b 1)

@[simp] theorem cylinderVector_coordinates {p : ℕ} (b : B.CylinderIndex p) :
    B.cylinderCoordinates p (B.cylinderVector b) = Finsupp.single b 1 :=
  (B.cylinderCoordinates p).apply_symm_apply _

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Actual endpoint and mixed atoms for the interval tensor

The mixed cells are the checked prism construction. Their top rows are
literal mixed basis vectors; all lower cells retain the signed table.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem atom_dimension (p : ℕ) (b : B.Index p) :
    K.realization.DimensionLE p (B.atom p b) :=
  Cell.dimensionLE_of_table_zero (B.atom_above p b)

def cylinderAtom : {p : ℕ} → B.CylinderIndex p → Cell (rightCylinder K)
  | _, .endpoint a b => Cell.map (RightCylinder.endpoint K a) (B.atom _ b)
  | _, .mixed b => RightCylinder.prism (B.atom _ b)

theorem cylinderAtom_dimension {p : ℕ} (b : B.CylinderIndex p) :
    (rightCylinder K).realization.DimensionLE p (B.cylinderAtom b) := by
  cases b with
  | endpoint a b => exact (RightCylinder.endpoint K a).realization.dimensionLE (B.atom_dimension _ b)
  | mixed b => exact RightCylinder.prism_dimension _ (B.atom_dimension _ b)

theorem cylinderAtom_above {p : ℕ} (b : B.CylinderIndex p)
    (q : ℕ) (hpq : p < q) (side : Bool) : (B.cylinderAtom b).table side q = 0 :=
  Cell.table_zero_of_dimensionLE (B.cylinderAtom_dimension b) hpq side

theorem cylinderAtom_top {p : ℕ} (b : B.CylinderIndex p) (side : Bool) :
    B.cylinderCoordinates p ((B.cylinderAtom b).table side p) = Finsupp.single b 1 := by
  classical
  apply Finsupp.ext
  intro c
  rw [B.cylinderCoordinates_apply]
  cases b with
  | @endpoint p a b =>
    cases p with
    | zero =>
      cases c with
      | endpoint a' c =>
        cases a <;> cases a' <;>
          simp [cylinderAtom, Cell.map, RightCylinder.endpoint, RightCylinder.endpointMap,
            cylinderCoefficient, B.atom_top, Finsupp.single_apply]
    | succ p =>
      cases c with
      | endpoint a' c =>
        cases a <;> cases a' <;>
          simp [cylinderAtom, Cell.map, RightCylinder.endpoint, RightCylinder.endpointMap,
            cylinderCoefficient, B.atom_top, Finsupp.single_apply]
      | mixed c =>
        cases a <;>
          simp [cylinderAtom, Cell.map, RightCylinder.endpoint, RightCylinder.endpointMap,
            cylinderCoefficient]
  | @mixed p b =>
    have ht := RightCylinder.prism_top (B.atom p b) (B.atom_dimension p b) side
    change B.cylinderCoefficient c ((RightCylinder.prism (B.atom p b)).table side (p+1)) = _
    rw [ht]
    cases c with
    | endpoint a c => cases a <;> simp [cylinderCoefficient]
    | mixed c => simp [cylinderCoefficient, B.atom_top, Finsupp.single_apply]

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Side-height bounds for interval-tensor atoms

The tensor height separates its endpoint copies by one. This matches the
alternating endpoint of the actual prism, including the degree-zero row.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

/-- The stronger side-height information used when tensoring the basis.
It is supplied by the already proved signed simplex boundary order. -/
def SideHeight : Prop := ∀ p (b : B.Index p) q, q < p → ∀ (side : Bool) (c : B.Index q),
  B.coordinates q ((B.atom p b).table side q) c ≠ 0 →
    if side then B.height p b < B.height q c else B.height q c < B.height p b

theorem atom_side_height_le (hs : B.SideHeight) (p : ℕ) (b : B.Index p)
    (side : Bool) (q : ℕ) (hqp : q ≤ p) (c : B.Index q)
    (hc : B.coordinates q ((B.atom p b).table side q) c ≠ 0) :
    if side then B.height p b ≤ B.height q c else B.height q c ≤ B.height p b := by
  rcases hqp.eq_or_lt with rfl | hqp
  · have he : c = b := by
      by_contra hn
      rw [B.atom_top, Finsupp.single_eq_of_ne hn] at hc
      exact hc rfl
    subst c
    cases side <;> exact le_rfl
  · have hh := hs p b q hqp side c hc
    cases side <;> exact hh.le

theorem prismSide_sourceEndpoint (p : ℕ) :
    RightCylinder.prismSide p false = RightCylinderBasis.sourceEndpoint p := by
  simp only [RightCylinder.prismSide, Bool.false_eq_true, ite_false,
    RightCylinderBasis.sourceEndpoint, Nat.mod_two_of_bodd]
  cases p.bodd <;> rfl

theorem prismSide_targetEndpoint (p : ℕ) :
    RightCylinder.prismSide p true = !(RightCylinderBasis.sourceEndpoint p) := by
  rw [← prismSide_sourceEndpoint p]
  rfl

/-- The shifted rank of the endpoint selected by the prism has the exact
sign of that prism side. -/
theorem prism_endpoint_height (p : ℕ) (b : B.Index p) (side : Bool) :
    RightCylinderBasis.height B.height (.endpoint (RightCylinder.prismSide p side) b) =
      3 * B.height p b + if side then 1 else -1 := by
  cases side
  · simp [RightCylinderBasis.height, prismSide_sourceEndpoint]
  · simp [RightCylinderBasis.height, prismSide_targetEndpoint]

theorem endpointAtom_endpointCoefficient {p q : ℕ} (a : Bool) (b : B.Index p)
    (side d : Bool) (c : B.Index q) :
    B.cylinderCoefficient (.endpoint d c)
      ((B.cylinderAtom (.endpoint a b)).table side q) =
      if d = a then B.coordinates q ((B.atom p b).table side q) c else 0 := by
  cases q <;> cases a <;> cases d <;>
    simp [cylinderAtom, Cell.map, RightCylinder.endpoint, RightCylinder.endpointMap,
      cylinderCoefficient]

theorem endpointAtom_mixedCoefficient {p q : ℕ} (a : Bool) (b : B.Index p)
    (side : Bool) (c : B.Index q) :
    B.cylinderCoefficient (.mixed c)
      ((B.cylinderAtom (.endpoint a b)).table side (q+1)) = 0 := by
  cases a <;> simp [cylinderAtom, Cell.map, RightCylinder.endpoint,
    RightCylinder.endpointMap, cylinderCoefficient]

theorem mixedAtom_mixedCoefficient {p q : ℕ} (b : B.Index p)
    (side : Bool) (c : B.Index q) :
    B.cylinderCoefficient (.mixed c) ((B.cylinderAtom (.mixed b)).table side (q+1)) =
      B.coordinates q ((B.atom p b).table side q) c := by
  simp only [cylinderAtom, RightCylinder.prism, RightCylinder.prismTable]
  split_ifs <;> rfl

theorem mixedAtom_endpointCoefficient {p q : ℕ} (b : B.Index p)
    (side d : Bool) (c : B.Index q) :
    B.cylinderCoefficient (.endpoint d c) ((B.cylinderAtom (.mixed b)).table side q) =
      if d = RightCylinder.prismSide q side then
        B.coordinates q ((B.atom p b).table side q) c else 0 := by
  cases q with
  | zero =>
    cases side <;> cases d <;>
      simp [cylinderAtom, RightCylinder.prism, RightCylinder.prismTable,
        RightCylinder.prismSide, cylinderCoefficient]
  | succ q =>
    cases d <;>
      simp only [cylinderAtom, RightCylinder.prism, RightCylinder.prismTable]
    all_goals split_ifs <;> simp_all [cylinderCoefficient]

/-- Every strict lower face of an actual endpoint or prism atom has the
required strict signed-height bound. -/
theorem cylinderAtom_side_height (hs : B.SideHeight) {p : ℕ} (b : B.CylinderIndex p)
    (side : Bool) (q : ℕ) (hqp : q < p) (c : B.CylinderIndex q)
    (hc : B.cylinderCoefficient c ((B.cylinderAtom b).table side q) ≠ 0) :
    if side then RightCylinderBasis.height B.height b < RightCylinderBasis.height B.height c
    else RightCylinderBasis.height B.height c < RightCylinderBasis.height B.height b := by
  cases b with
  | @endpoint p a b =>
    cases c with
    | endpoint d c =>
      rw [B.endpointAtom_endpointCoefficient] at hc
      split_ifs at hc with hda
      · subst d
        have hh := hs p b q hqp side c hc
        cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hh ⊢
        all_goals simp only [RightCylinderBasis.height]; split_ifs <;> omega
      · exact (hc rfl).elim
    | mixed c => exact (hc (B.endpointAtom_mixedCoefficient a b side c)).elim
  | @mixed p b =>
    cases c with
    | endpoint d c =>
      rw [B.mixedAtom_endpointCoefficient] at hc
      split_ifs at hc with hd
      · subst d
        by_cases hqlt : q < p
        · have hh := hs p b q hqlt side c hc
          cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hh ⊢
          all_goals simp only [RightCylinderBasis.height]; split_ifs <;> omega
        · have hqe : q = p := by omega
          subst q
          have hcb : c = b := by
            by_contra hn
            rw [B.atom_top, Finsupp.single_eq_of_ne hn] at hc
            exact hc rfl
          subst c
          rw [B.prism_endpoint_height]
          cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
            RightCylinderBasis.height] <;> omega
      · exact (hc rfl).elim
    | @mixed q c =>
      rw [B.mixedAtom_mixedCoefficient] at hc
      have hh := hs p b q (by omega) side c hc
      cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        RightCylinderBasis.height] at hh ⊢ <;> omega

/-- The concrete tensor atoms therefore have disjoint ordered boundaries. -/
theorem cylinder_atoms_disjoint (hs : B.SideHeight) {p q r : ℕ}
    (b : B.CylinderIndex p) (c : B.CylinderIndex q) (hrp : r < p) (hrq : r < q)
    (hbc : RightCylinderBasis.height B.height b ≤ RightCylinderBasis.height B.height c)
    (e : B.CylinderIndex r) :
    B.cylinderCoordinates r ((B.cylinderAtom b).table false r) e = 0 ∨
      B.cylinderCoordinates r ((B.cylinderAtom c).table true r) e = 0 := by
  simp only [B.cylinderCoordinates_apply]
  by_cases hb : B.cylinderCoefficient e ((B.cylinderAtom b).table false r) = 0
  · exact Or.inl hb
  · right
    by_contra hc
    have hbe := B.cylinderAtom_side_height hs b false r hrp e hb
    have hec := B.cylinderAtom_side_height hs c true r hrq e hc
    exact (not_lt_of_ge hbc) (hec.trans hbe)

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Positive truncation comparisons for right chain cylinders

A positive bridge in the first factor gives two endpoint bridges in its
right cylinder. The interval component cancels because the maps agree
in the degree immediately below the truncation bound.
-/

namespace Thomason.Construction.DirectedComplex

open CategoryTheory

universe u

variable {K L : DirectedComplex.{u}}

/-- Agreement below a bound survives right tensoring with the interval. -/
theorem rightCylinderMap_agree_below
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k < n → f.app k = g.app k) :
    ∀ k, k < n → (RightCylinder.map f).app k = (RightCylinder.map g).app k := by
  intro k hk
  exact rightCylinderMap_agree_through f g
    (fun l hl => hfg l (lt_of_le_of_lt hl hk)) k le_rfl

/-- The positive degree bridge transports through the actual signed
right-cylinder differential. -/
theorem rightCylinderMap_positive_degree_bridge
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k < n → f.app k = g.app k)
    (hbridge : ∀ v : K.group n, v ∈ K.positive n →
      ∃ z : L.group (n+1), z ∈ L.positive (n+1) ∧
        L.differential n z = g.app n v - f.app n v) :
    ∀ v : (rightCylinder K).group n, v ∈ (rightCylinder K).positive n →
      ∃ z : (rightCylinder L).group (n+1), z ∈ (rightCylinder L).positive (n+1) ∧
        (rightCylinder L).differential n z =
          (RightCylinder.map g).app n v - (RightCylinder.map f).app n v := by
  intro v hv
  cases n with
  | zero =>
    obtain ⟨z₀, hz₀, hd₀⟩ := hbridge v.1 hv.1
    obtain ⟨z₁, hz₁, hd₁⟩ := hbridge v.2 hv.2
    refine ⟨(z₀, z₁, 0), ⟨hz₀, hz₁, (L.positive 0).zero_mem⟩, ?_⟩
    change (L.differential 0 z₀ - 0, L.differential 0 z₁ + 0) =
      (g.app 0 v.1 - f.app 0 v.1, g.app 0 v.2 - f.app 0 v.2)
    simp only [sub_zero, add_zero, hd₀, hd₁]
  | succ n =>
    obtain ⟨z₀, hz₀, hd₀⟩ := hbridge v.1 hv.1
    obtain ⟨z₁, hz₁, hd₁⟩ := hbridge v.2.1 hv.2.1
    refine ⟨(z₀, z₁, 0), ⟨hz₀, hz₁, (L.positive (n+1)).zero_mem⟩, ?_⟩
    change (L.differential (n+1) z₀ - ((-1 : ℤ)^(n+1)) • 0,
        L.differential (n+1) z₁ + ((-1 : ℤ)^(n+1)) • 0,
        L.differential n 0) =
      (g.app (n+1) v.1 - f.app (n+1) v.1,
        g.app (n+1) v.2.1 - f.app (n+1) v.2.1,
        g.app n v.2.2 - f.app n v.2.2)
    rw [hfg n (Nat.lt_succ_self n)]
    simp only [smul_zero, sub_zero, add_zero, map_zero, sub_self, hd₀, hd₁]

/-- Positive bridges in the original complexes force exact equality after
mapping the right-cylinder realizations into a truncated target. -/
theorem rightCylinder_realization_comp_eq_of_positive_degree_bridge
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k < n → f.app k = g.app k)
    (hbridge : ∀ v : K.group n, v ∈ K.positive n →
      ∃ z : L.group (n+1), z ∈ L.positive (n+1) ∧
        L.differential n z = g.app n v - f.app n v)
    {Y : StrictOmegaCategory.{u}} (hY : Y.IsTruncated n)
    (H : (rightCylinder L).realization ⟶ Y) :
    (RightCylinder.map f).realization ≫ H = (RightCylinder.map g).realization ≫ H :=
  realization_comp_eq_of_positive_degree_bridge _ _
    (rightCylinderMap_agree_below f g hfg)
    (rightCylinderMap_positive_degree_bridge f g hfg hbridge) hY H

end Thomason.Construction.DirectedComplex

end

section

/-! # The chain groups generated by strict cells

In degree n the generators are the actual cells of dimension at most n.
Composition below n becomes addition. This is the degreewise construction
of Steiner's left adjoint lambda, needed to compare strict pasting with
positive chain pasting in the right interval tensor.
-/

namespace Thomason.Construction.StrictOmegaCategory.Abelianization

open CategoryTheory

noncomputable section

variable (C : StrictOmegaCategory.{0})

abbrev Bounded (n : ℕ) := { x : C // C.DimensionLE n x }
abbrev Free (n : ℕ) := FreeAbelianGroup (Bounded C n)

def composite {n : ℕ} (k : ℕ) (hk : k < n) (x y : Bounded C n)
    (h : C.target k x.val = C.source k y.val) : Bounded C n :=
  ⟨C.comp k x.val y.val h, C.dimensionLE_comp hk x.property y.property h⟩

/-- The defining additive relation for one actual strict composition. -/
def Relations (n : ℕ) : Set (Free C n) :=
  { z | ∃ (k : ℕ) (hk : k < n) (x y : Bounded C n)
      (h : C.target k x.val = C.source k y.val),
      z = FreeAbelianGroup.of (composite C k hk x y h) -
        FreeAbelianGroup.of x - FreeAbelianGroup.of y }

def relations (n : ℕ) : AddSubgroup (Free C n) := AddSubgroup.closure (Relations C n)

abbrev Chains (n : ℕ) := Free C n ⧸ relations C n

def generator (n : ℕ) (x : Bounded C n) : Chains C n :=
  QuotientAddGroup.mk' (relations C n) (FreeAbelianGroup.of x)

/-- Strict composition is addition in the constructed chain group. -/
theorem generator_composite {n : ℕ} (k : ℕ) (hk : k < n) (x y : Bounded C n)
    (h : C.target k x.val = C.source k y.val) :
    generator C n (composite C k hk x y h) = generator C n x + generator C n y := by
  have hm : FreeAbelianGroup.of (composite C k hk x y h) -
      FreeAbelianGroup.of x - FreeAbelianGroup.of y ∈ relations C n :=
    AddSubgroup.subset_closure ⟨k, hk, x, y, h, rfl⟩
  have hz := (QuotientAddGroup.eq_zero_iff _).mpr hm
  change (QuotientAddGroup.mk' (relations C n))
    (FreeAbelianGroup.of (composite C k hk x y h) -
      FreeAbelianGroup.of x - FreeAbelianGroup.of y) = 0 at hz
  simp only [map_sub] at hz
  change generator C n (composite C k hk x y h) - generator C n x - generator C n y = 0 at hz
  exact sub_eq_zero.mp (by simpa only [sub_add_eq_sub_sub] using hz)

/-- Identity extensions have zero positive-dimensional chain. -/
theorem generator_identity (n : ℕ) (x : C) (hx : C.DimensionLE n x) :
    generator C (n + 1) ⟨x, C.dimensionLE_mono (Nat.le_succ n) hx⟩ = 0 := by
  let a : Bounded C (n + 1) := ⟨x, C.dimensionLE_mono (Nat.le_succ n) hx⟩
  have hxx : C.target n x = C.source n x := hx.2.trans hx.1.symm
  have hc : composite C n (Nat.lt_succ_self n) a a hxx = a := by
    apply Subtype.ext
    change C.comp n x x hxx = x
    have hu := C.left_unit n x (by rw [C.face_face_same])
    simpa only [hx.1] using hu
  have he := generator_composite C n (Nat.lt_succ_self n) a a hxx
  rw [hc] at he
  exact (add_eq_left.mp he.symm)

/-- The degreewise universal property, retaining every composition relation. -/
def lift {A : Type*} [AddCommGroup A] (n : ℕ) (f : Bounded C n → A)
    (hf : ∀ (k : ℕ) (hk : k < n) (x y : Bounded C n)
      (h : C.target k x.val = C.source k y.val),
      f (composite C k hk x y h) = f x + f y) : Chains C n →+ A :=
  QuotientAddGroup.lift (relations C n) (FreeAbelianGroup.lift f) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨k, hk, x, y, h, rfl⟩
    change (FreeAbelianGroup.lift f) _ = 0
    simp only [map_sub, FreeAbelianGroup.lift_apply_of, hf]
    abel)

@[simp] theorem lift_generator {A : Type*} [AddCommGroup A] (n : ℕ)
    (f : Bounded C n → A) (hf) (x : Bounded C n) :
    lift C n f hf (generator C n x) = f x := by
  exact FreeAbelianGroup.lift_apply_of f x

@[ext] theorem hom_ext {A : Type*} [AddCommGroup A] (n : ℕ)
    (f g : Chains C n →+ A) (h : ∀ x, f (generator C n x) = g (generator C n x)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  exact h

/-- A face generator is defined with its canonical dimension witness. -/
def faceGenerator (a : Bool) (n : ℕ) (x : C) : Chains C n :=
  generator C n ⟨C.face a n x, C.face_dimensionLE a n x⟩

theorem faceGenerator_composite {n : ℕ} (a : Bool) (k : ℕ) (hk : k < n)
    (x y : C) (h : C.target k x = C.source k y) :
    faceGenerator C a n (C.comp k x y h) =
      faceGenerator C a n x + faceGenerator C a n y := by
  have hh : C.target k (C.face a n x) = C.source k (C.face a n y) := by
    simpa only [source, target, C.globular, hk, ite_true] using h
  have hc := C.face_comp a n k hk x y h hh
  have he : (⟨C.face a n (C.comp k x y h), C.face_dimensionLE a n _⟩ : Bounded C n) =
      composite C k hk ⟨C.face a n x, C.face_dimensionLE a n x⟩
        ⟨C.face a n y, C.face_dimensionLE a n y⟩ hh := Subtype.ext hc
  change generator C n _ = _
  rw [he]
  exact generator_composite C k hk _ _ hh

/-- The signed boundary respects each relation in degree n+1. -/
theorem boundary_composite (n k : ℕ) (hk : k < n + 1) (x y : Bounded C (n + 1))
    (h : C.target k x.val = C.source k y.val) :
    (faceGenerator C true n (composite C k hk x y h).val -
      faceGenerator C false n (composite C k hk x y h).val) =
    (faceGenerator C true n x.val - faceGenerator C false n x.val) +
      (faceGenerator C true n y.val - faceGenerator C false n y.val) := by
  by_cases hkn : k < n
  · simp only [composite, faceGenerator_composite C _ k hkn]
    abel
  · have he : k = n := by omega
    subst k
    have hm : faceGenerator C true n x.val = faceGenerator C false n y.val := by
      apply congrArg (generator C n)
      exact Subtype.ext h
    change faceGenerator C true n (C.comp n x.val y.val h) -
      faceGenerator C false n (C.comp n x.val y.val h) = _
    have ht : faceGenerator C true n (C.comp n x.val y.val h) =
        faceGenerator C true n y.val := congrArg (generator C n) (Subtype.ext (C.target_comp _ _ _ _))
    have hs : faceGenerator C false n (C.comp n x.val y.val h) =
        faceGenerator C false n x.val := congrArg (generator C n) (Subtype.ext (C.source_comp _ _ _ _))
    rw [ht, hs, hm]
    abel

/-- Differential of lambda, defined on the quotient rather than postulated. -/
def differential (n : ℕ) : Chains C (n + 1) →+ Chains C n :=
  lift C (n + 1) (fun x => faceGenerator C true n x.val - faceGenerator C false n x.val)
    (boundary_composite C n)

@[simp] theorem differential_generator (n : ℕ) (x : Bounded C (n + 1)) :
    differential C n (generator C (n + 1) x) =
      faceGenerator C true n x.val - faceGenerator C false n x.val :=
  lift_generator C _ _ _ x

@[simp] theorem differential_faceGenerator (n : ℕ) (a : Bool) (x : C) :
    differential C n (faceGenerator C a (n + 1) x) =
      faceGenerator C true n (C.face a (n + 1) x) -
        faceGenerator C false n (C.face a (n + 1) x) :=
  differential_generator C n _

@[simp] theorem faceGenerator_face (a b : Bool) {n m : ℕ} (hnm : n < m) (x : C) :
    faceGenerator C a n (C.face b m x) = faceGenerator C a n x := by
  apply congrArg (generator C n)
  apply Subtype.ext
  exact (C.globular a b n m x).trans (ite_eq_left hnm)

theorem differential_squared (n : ℕ) (x : Chains C (n + 2)) :
    differential C n (differential C (n + 1) x) = 0 := by
  have he : (differential C n).comp (differential C (n + 1)) = 0 := by
    apply hom_ext
    intro y
    simp only [AddMonoidHom.comp_apply, differential_generator, map_sub,
      differential_faceGenerator, faceGenerator_face C _ _ (Nat.lt_succ_self n),
      sub_self, AddMonoidHom.zero_apply]
  exact DFunLike.congr_fun he x

def augmentation : Chains C 0 →+ ℤ :=
  lift C 0 (fun _ => 1) (by intro k hk; omega)

@[simp] theorem augmentation_generator (x : Bounded C 0) :
    augmentation C (generator C 0 x) = 1 := lift_generator C _ _ _ x

@[simp] theorem augmentation_faceGenerator (a : Bool) (x : C) :
    augmentation C (faceGenerator C a 0 x) = 1 := augmentation_generator C _

theorem augmentation_differential (x : Chains C 1) :
    augmentation C (differential C 0 x) = 0 := by
  have he : (augmentation C).comp (differential C 0) = 0 := by
    apply hom_ext
    intro y
    simp only [AddMonoidHom.comp_apply, differential_generator, map_sub,
      augmentation_faceGenerator, sub_self, AddMonoidHom.zero_apply]
  exact DFunLike.congr_fun he x

/-- The positive monoid consists of sums of actual cell generators. -/
def positive (n : ℕ) : AddSubmonoid (Chains C n) :=
  AddSubmonoid.closure (Set.range (generator C n))

theorem generator_positive (n : ℕ) (x : Bounded C n) :
    generator C n x ∈ positive C n := AddSubmonoid.subset_closure ⟨x, rfl⟩

/-- The actual augmented directed complex associated to a strict category. -/
def complex : DirectedComplex.{0} where
  group n := AddCommGrpCat.of (Chains C n)
  differential := differential C
  differential_squared := differential_squared C
  augmentation := augmentation C
  augmentation_differential := augmentation_differential C
  positive := positive C

end

end Thomason.Construction.StrictOmegaCategory.Abelianization

end

end OAI
