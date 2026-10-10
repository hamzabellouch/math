import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.FlagGalleries

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
variable {n m r : ℕ}

/-- Finite, exhaustive intersection-rank indexing set. Zero blocks and repeated flag terms are retained at this stage, rather than excluded by genericity. -/
def RankShape (n m r : ℕ) :=
  {d : Fin n × Fin m → Fin (r+1) // ∑ p, (d p).val=r}

instance (n m r : ℕ) : Fintype (RankShape n m r) := by
  unfold RankShape
  infer_instance

abbrev BlockCoordinates (K : Type*) (d : RankShape n m r) :=
  (p : Fin n × Fin m) → Fin ((d.val p).val) → K

def coordinateBlock (d : RankShape n m r) (p : Fin n × Fin m) :
    Submodule K (BlockCoordinates K d) :=
  LinearMap.range (LinearMap.single K (fun q => Fin ((d.val q).val) → K) p : (Fin ((d.val p).val) → K) →ₗ[K] BlockCoordinates K d)

def boundedGrid {n m : ℕ} (P : Fin n × Fin m → Submodule K V) (i j : ℕ) : Submodule K V :=
  ⨆ (p : Fin n × Fin m) (_ : p.1.val < i ∧ p.2.val < j), P p

omit [FiniteDimensional K V] in
lemma boundedGrid_eq (W : ℕ → ℕ → Submodule K V) {n m i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    boundedGrid (fun p : Fin n × Fin m => W p.1.val p.2.val) i j=flagGridSum W i j := by
  unfold boundedGrid flagGridSum
  apply le_antisymm
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact le_iSup_of_le (⟨p.1.val,hp.1⟩ : Fin i)
      (le_iSup (fun y : Fin j => W p.1.val y.val) ⟨p.2.val,hp.2⟩)
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    exact le_iSup_of_le ((⟨x.val,lt_of_lt_of_le x.isLt hi⟩,⟨y.val,lt_of_lt_of_le y.isLt hj⟩) : Fin n × Fin m)
      (le_iSup_of_le (show x.val < i ∧ y.val < j from ⟨x.isLt,y.isLt⟩) le_rfl)

omit [FiniteDimensional K V] in
lemma finiteSubmoduleSum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Submodule K V) (p : ι) (v : P p) :
    finiteSubmoduleSum P (Pi.single p v)=v.val := by
  change (∑ q, ((Pi.single p v : (q:ι) → P q) q : V))=v.val
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro q _ hqp
    rw [Pi.single_eq_of_ne hqp]
    rfl
  · simp

omit [FiniteDimensional K V] in
lemma piEquiv_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)]
    (e : ∀ i, A i ≃ₗ[K] B i) (p : ι) (v : A p) :
    LinearEquiv.piCongrRight e (Pi.single p v)=Pi.single p (e p v) := by
  funext q
  by_cases h : q=p
  · subst q
    simp only [LinearEquiv.piCongrRight_apply,Pi.single_eq_same]
  · simp only [LinearEquiv.piCongrRight_apply,Pi.single_eq_of_ne h,map_zero]

/-- Every pair of finite flags is in one of these finitely many split matrix charts. There is no regularity, opposite-flags, or strict-rank premise. -/
theorem finite_shape_frame_covers
    (F H : ℕ → Submodule K V) (hF : Monotone F) (hH : Monotone H)
    (hF0 : F 0=⊥) (hH0 : H 0=⊥) (n m : ℕ) (hFn : F n=⊤) (hHm : H m=⊤) :
    ∃ (d : RankShape n m (Module.finrank K V)) (e : BlockCoordinates K d ≃ₗ[K] V),
      ∀ i j, i ≤ n → j ≤ m →
        F i ⊓ H j=boundedGrid (fun p => (coordinateBlock d p).map e.toLinearMap) i j := by
  obtain ⟨W,hspan,hbij⟩ := two_flag_common_splitting F H hF hH hF0 hH0 n m hFn hHm
  let P : Fin n × Fin m → Submodule K V := fun p => W p.1.val p.2.val
  let sumEquiv : ((p : Fin n × Fin m) → P p) ≃ₗ[K] V :=
    LinearEquiv.ofBijective (finiteSubmoduleSum P) hbij
  have hs : (∑ p,Module.finrank K (P p))=Module.finrank K V := by
    rw [← Module.finrank_pi_fintype]
    exact sumEquiv.finrank_eq
  let dim : Fin n × Fin m → Fin (Module.finrank K V+1) :=
    fun p => ⟨Module.finrank K (P p),Nat.lt_succ_of_le (P p).finrank_le⟩
  let d : RankShape n m (Module.finrank K V) := ⟨dim,hs⟩
  let basisMap : (p : Fin n × Fin m) → (Fin ((d.val p).val) → K) ≃ₗ[K] P p :=
    fun p => (Module.finBasis K (P p)).equivFun.symm
  let e : BlockCoordinates K d ≃ₗ[K] V :=
    (LinearEquiv.piCongrRight basisMap).trans sumEquiv
  have he (p : Fin n × Fin m) (v : Fin ((d.val p).val) → K) :
      e (Pi.single p v)=(basisMap p v).val := by
    change sumEquiv (LinearEquiv.piCongrRight basisMap (Pi.single p v))=_
    rw [piEquiv_single]
    exact finiteSubmoduleSum_single P p _
  have hblock (p : Fin n × Fin m) : (coordinateBlock d p).map e.toLinearMap=P p := by
    apply le_antisymm
    · rintro v ⟨u,⟨w,rfl⟩,rfl⟩
      change e (Pi.single p w) ∈ P p
      rw [he]
      exact (basisMap p w).property
    · intro v hv
      refine ⟨Pi.single p ((basisMap p).symm ⟨v,hv⟩),⟨_,rfl⟩,?_⟩
      change e (Pi.single p ((basisMap p).symm ⟨v,hv⟩))=v
      rw [he,LinearEquiv.apply_symm_apply]
  refine ⟨d,e,?_⟩
  intro i j hi hj
  simp only [hblock]
  rw [boundedGrid_eq W hi hj]
  exact hspan i j

end IntegralCharacterVarieties.TwoFlagBand
namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
open OccurrenceIncidence.VertexTable

/-- Distinct occurrences survive even if two original graded spaces are isomorphic, zero, or come from the same repeatedly incident facet. -/
inductive BandColor (n m : ℕ)
  | parent : BandColor n m
  | row : Fin n → BandColor n m
  | col : Fin m → BandColor n m
  | cell : Fin n → Fin m → BandColor n m
  deriving DecidableEq, Fintype

namespace RankShape
variable {n m r : ℕ} (d : RankShape n m r)
def bandRank : BandColor n m → ℕ
  | .parent => r
  | .row i => ∑ j,(d.val (i,j)).val
  | .col j => ∑ i,(d.val (i,j)).val
  | .cell i j => (d.val (i,j)).val

lemma parent_row_rank : d.bandRank .parent=∑ i,d.bandRank (.row i) := by
  exact d.property.symm.trans (Fintype.sum_prod_type (fun p : Fin n × Fin m => (d.val p).val))

/-- Canonically choose one finite allowed port band for each bounded rank shape. This producer does not take any affine-bundle hypothesis. -/
noncomputable def band : RealizedBand (BandColor.parent : BandColor n m)
    (List.ofFn BandColor.row) (List.ofFn BandColor.col) :=
  (produced_ranked_two_flag_band (r:=d.bandRank) BandColor.row BandColor.col BandColor.cell
    d.parent_row_rank (fun _ => rfl) (fun _ => rfl)).choose

theorem band_conservative : ∀ v,(d.band.decoration v).Conservative d.bandRank :=
  (produced_ranked_two_flag_band (r:=d.bandRank) BandColor.row BandColor.col BandColor.cell
    d.parent_row_rank (fun _ => rfl) (fun _ => rfl)).choose_spec

/-- The combined family is finite: lengths may vary with the intersection shape, but there are finitely many shapes and each band is finite. -/
abbrev BandVertex := (d : RankShape n m r) × Fin (d.band.length+1)
instance finiteBandVertex : Fintype (BandVertex (n:=n) (m:=m) (r:=r)) := inferInstance
end RankShape

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/-- Exhaustive actual-flags linkage: the finite band family is indexed by the intersection pieces of every pair of flags, and every local allowed vertex has its rank identity. No opposite-flags or generic Jordan condition is introduced. Geometric reconstruction of the whole disk still has to attach these bands. -/
theorem actual_flags_in_produced_bands
    (F H : ℕ → Submodule K V) (hF : Monotone F) (hH : Monotone H)
    (hF0 : F 0=⊥) (hH0 : H 0=⊥) (n m : ℕ) (hFn : F n=⊤) (hHm : H m=⊤) :
    ∃ (d : RankShape n m (Module.finrank K V)) (e : BlockCoordinates K d ≃ₗ[K] V),
      (∀ i j, i ≤ n → j ≤ m →
        F i ⊓ H j=boundedGrid (fun p => (coordinateBlock d p).map e.toLinearMap) i j) ∧
      (∀ v,(d.band.decoration v).Conservative d.bandRank) := by
  obtain ⟨d,e,he⟩ := finite_shape_frame_covers F H hF hH hF0 hH0 n m hFn hHm
  exact ⟨d,e,he,d.band_conservative⟩

/-- Multiple cuts are indexed simultaneously by a finite product of bounded rank arrays, not by an unbounded fresh family chosen for each old solution. -/
abbrev CutShapes {Cut : Type} (rows cols size : Cut → ℕ) :=
  (c : Cut) → RankShape (rows c) (cols c) (size c)
instance finiteCutShapes {Cut : Type} [Fintype Cut] (rows cols size : Cut → ℕ) :
    Fintype (CutShapes rows cols size) := inferInstance

structure FlagPair (n m : ℕ) where
  left : ℕ → Submodule K V
  right : ℕ → Submodule K V
  left_mono : Monotone left
  right_mono : Monotone right
  left_zero : left 0=⊥
  right_zero : right 0=⊥
  left_top : left n=⊤
  right_top : right m=⊤

/-- Exhaustivity holds simultaneously on any fixed finite incidence list of cuts, including several distinct occurrences of the same surface component. -/
theorem all_cuts_in_finite_band_family {Cut : Type} [Fintype Cut]
    (rows cols : Cut → ℕ) (flags : (c : Cut) → FlagPair (K:=K) (V:=V) (rows c) (cols c)) :
    ∃ d : CutShapes rows cols (fun _ => Module.finrank K V),
      ∀ c, ∃ e : BlockCoordinates K (d c) ≃ₗ[K] V,
        (∀ i j, i ≤ rows c → j ≤ cols c →
          (flags c).left i ⊓ (flags c).right j=
            boundedGrid (fun p => (coordinateBlock (d c) p).map e.toLinearMap) i j) ∧
        ∀ v,((d c).band.decoration v).Conservative (d c).bandRank := by
  have H (c : Cut) := actual_flags_in_produced_bands (flags c).left (flags c).right
    (flags c).left_mono (flags c).right_mono (flags c).left_zero (flags c).right_zero
    (rows c) (cols c) (flags c).left_top (flags c).right_top
  choose d e he hd using H
  exact ⟨d,fun c => ⟨e c,he c,hd c⟩⟩
end IntegralCharacterVarieties.TwoFlagBand


namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {V F : Type} {kind : V → Kind}
namespace PortWiring
variable (W : PortWiring kind) (d : (v : V) → Decoration (kind v) F)

/-- The ordered list is extended by its parent off its finite domain. Using a natural numbered occurrence makes all reindexing by equality transparent. -/
def natColor (p : LocalPort V kind) : Option ℕ → F
  | none => (d p.1).color ⟨p.2,none⟩
  | some i => if h : i < (kind p.1).arity p.2 then
      (d p.1).portColor p.2 (some ⟨i,h⟩) else (d p.1).color ⟨p.2,none⟩

lemma natColor_local (p : LocalPort V kind) (c : Option ((kind p.1).table.Child p.2)) :
    natColor d p (c.map (fun j => ((kind p.1).childEnumeration p.2 j).val))=
      (d p.1).color ⟨p.2,c⟩ := by
  cases c with
  | none => rfl
  | some j =>
    dsimp only [Option.map_some,natColor]
    rw [dite_eq_left ((kind p.1).childEnumeration p.2 j).isLt]
    exact (d p.1).portColor_child p.2 j

/-- Entire ordered lists, not merely multisets of ranks, agree at opposite ends. -/
def ColorCompatible : Prop := ∀ (s : W.Seam),
  natColor d (W.wire s).val = natColor d s.val

def coloredFacet (z : Side W.Seam W.seamArity) : F :=
  natColor d z.1.val (z.2.map Fin.val)

lemma castFin_val {n m : ℕ} (h : n=m) (i : Fin n) :
    (h ▸ i : Fin m).val=i.val := by subst m; rfl

lemma sideOf_color (hd : W.ColorCompatible d) (x : LocalEnd V kind) :
    W.coloredFacet d (W.sideOf x)=(d x.1).color x.2 := by
  rcases x with ⟨v,p,c⟩
  change natColor d (W.endOf ⟨v,p⟩).1.val
    ((c.map (fun j => (W.count ⟨v,p⟩).symm ▸ (kind v).childEnumeration p j)).map Fin.val)=_
  have hc : ((c.map (fun j => (W.count ⟨v,p⟩).symm ▸ (kind v).childEnumeration p j)).map Fin.val)=
      c.map (fun j => ((kind v).childEnumeration p j).val) := by
    cases c <;> simp only [Option.map_none,Option.map_some,castFin_val]
  rw [hc]
  by_cases h : (kind v).table.endpoint p=true
  · simpa only [endOf,dite_eq_left h] using natColor_local d ⟨v,p⟩ c
  · let s : W.Seam := W.wire.symm ⟨⟨v,p⟩,Bool.eq_false_iff.mpr h⟩
    have hw : (W.wire s).val=⟨v,p⟩ := congrArg Subtype.val (W.wire.apply_symm_apply _)
    have hh := hd s
    rw [hw] at hh
    change natColor d (W.endOf ⟨v,p⟩).1.val _=_
    simp only [endOf,dite_eq_right h]
    change natColor d s.val _=_
    rw [← hh]
    exact natColor_local d ⟨v,p⟩ c

/-- Every corner-color equation follows from vertex tables and wiring. -/
def fromDecoration (hd : W.ColorCompatible d) :
    PortAssembly F W.Seam V W.seamArity :=
  W.assemble (W.coloredFacet d) (by
    intro x
    rw [W.sideOf_color d hd,W.sideOf_color d hd]
    exact (d x.1).corner x.2)

/-- Finite ordered port equality suffices; off-domain colors are the parents. -/
lemma compatible_of_portColor
    (h : ∀ (s : W.Seam) (j : Option (Fin (W.seamArity s))),
      (d (W.wire s).val.1).portColor (W.wire s).val.2
        (j.map (finCongr (W.arity s).symm)) = (d s.val.1).portColor s.val.2 j) :
    W.ColorCompatible d := by
  intro s
  funext c
  cases c with
  | none => exact h s none
  | some i =>
    have ha := W.arity s
    by_cases hi : i<(kind s.val.1).arity s.val.2
    · have hj := h s (some ⟨i,hi⟩)
      change natColor d _ (some i)=natColor d _ (some i)
      dsimp only [natColor]
      rw [dite_eq_left hi,dite_eq_left (by simpa only [ha] using hi)]
      exact hj
    · have hi' : ¬ i<(kind (W.wire s).val.1).arity (W.wire s).val.2 := by
        simpa only [ha] using hi
      simp only [natColor,dite_eq_right hi,dite_eq_right hi']
      exact h s none

end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable

/-- Numerical side labels are injective because the finite arity is retained by the seam itself. Used only to discharge dependent casts at sewing. -/
def sideNumber {S : Type} {arity : S → ℕ} (z : Side S arity) : S × Option ℕ :=
  (z.1,z.2.map Fin.val)

lemma sideNumber_injective {S : Type} {arity : S → ℕ} :
    Function.Injective (@sideNumber S arity) := by
  rintro ⟨s,c⟩ ⟨t,d⟩ h
  have hst : s=t := congrArg Prod.fst h
  subst t
  apply congrArg (Sigma.mk s)
  have hcd : c.map Fin.val=d.map Fin.val := congrArg Prod.snd h
  cases c <;> cases d <;> simp_all only [Option.map_none,Option.map_some,Option.some.injEq,
    reduceCtorEq,Fin.val_inj]

namespace PortWiring
variable {V F : Type} {kind : V → Kind} (W : PortWiring kind)

lemma sideOf_number (x : LocalEnd V kind) : sideNumber (W.sideOf x)=
    ((W.endOf ⟨x.1,x.2.1⟩).1,x.2.2.map (fun j => ((kind x.1).childEnumeration x.2.1 j).val)) := by
  dsimp only [sideNumber,sideOf]
  congr 1
  cases x.2.2 <;> simp only [Option.map_none,Option.map_some,castFin_val]

lemma sideOf_eq (x y : LocalEnd V kind)
    (hp : (W.endOf ⟨x.1,x.2.1⟩).1=(W.endOf ⟨y.1,y.2.1⟩).1)
    (hc : x.2.2.map (fun j => ((kind x.1).childEnumeration x.2.1 j).val)=
      y.2.2.map (fun j => ((kind y.1).childEnumeration y.2.1 j).val)) :
    W.sideOf x=W.sideOf y := by
  apply sideNumber_injective
  rw [W.sideOf_number,W.sideOf_number,hp,hc]

lemma finCongr_eq_cast {n m : ℕ} (h : n=m) (i : Fin n) : finCongr h i=h ▸ i := by
  subst m
  rfl

lemma realize_assemble (facet : Side W.Seam W.seamArity → F)
    (h : ∀ x, facet (W.sideOf (localMate x))=facet (W.sideOf x)) (x : LocalEnd V kind) :
    (W.assemble facet h).realize x=(W.sideOf x,(kind x.1).table.endpoint x.2.1) := by
  calc
    _ = _ := (W.assemble facet h).realize_apply x
    _ = _ := ?_
  apply Prod.ext
  · dsimp only [PortAssembly.childEquiv,assemble,sideOf]
    congr 1
    cases x.2.2 with
    | none => rfl
    | some j =>
      apply congrArg some
      exact finCongr_eq_cast _ _
  · exact W.endpoint _


lemma boundaryNext_local (facet : Side W.Seam W.seamArity → F)
    (h : ∀ x, facet (W.sideOf (localMate x))=facet (W.sideOf x))
    (x : LocalEnd V kind)
    (he : (kind x.1).table.endpoint x.2.1=x.2.2.isNone) :
    (W.assemble facet h).vertexAssembly.corners.boundaryNext (W.sideOf x)=
      W.sideOf (localMate x) := by
  have hx : (W.assemble facet h).realize x=finish (W.sideOf x) := by
    rw [W.realize_assemble]
    apply Prod.ext
    · rfl
    rw [he]
    dsimp only [finish,positive,sideOf]
    cases x.2.2 <;> rfl
  change ((W.assemble facet h).realize
    (localMate ((W.assemble facet h).realize.symm (finish (W.sideOf x))))).1=_
  have hi : (W.assemble facet h).realize.symm (finish (W.sideOf x))=x := by
    rw [← hx]
    exact (W.assemble facet h).realize.symm_apply_apply x
  calc
    _ = ((W.assemble facet h).realize (localMate x)).1 :=
      congrArg (fun z => ((W.assemble facet h).realize (localMate z)).1) hi
    _ = _ := congrArg Prod.fst (W.realize_assemble facet h (localMate x))

end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable

/-- Separate copies of every vertex and port are retained under replacement. Even two uses of the very same template have disjoint sigma-indexed vertices. -/
def familyKind {T : Type} {V : T → Type} (k : (t : T) → V t → Kind) :
    ((t : T) × V t) → Kind := fun z => k z.1 z.2

def familyPortEquiv {T : Type} {V : T → Type} (k : (t : T) → V t → Kind) (b : Bool) :
    ((t : T) × PortAt (k t) b) ≃ PortAt (familyKind k) b where
  toFun z := ⟨⟨⟨z.1,z.2.val.1⟩,z.2.val.2⟩,z.2.property⟩
  invFun z := ⟨z.val.1.1,⟨⟨z.val.1.2,z.val.2⟩,z.property⟩⟩
  left_inv := by rintro ⟨t,⟨⟨v,p⟩,h⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨t,v⟩,p⟩,h⟩; rfl

namespace PortPatch
variable {T : Type} {V I A B : T → Type} {k : (t : T) → V t → Kind}
variable (P : (t : T) → PortPatch (k t) (I t) (A t) (B t))

/-- A finite collection of open templates, before interface sewing. Internal seams never acquire identifications between different copies. -/
def family : PortPatch (familyKind k) ((t : T) × I t) ((t : T) × A t) ((t : T) × B t) where
  plus := (Equiv.sigmaSumDistrib I A).symm |>.trans
    (Equiv.sigmaCongrRight (fun t => (P t).plus)) |>.trans (familyPortEquiv k true)
  minus := (Equiv.sigmaSumDistrib I B).symm |>.trans
    (Equiv.sigmaCongrRight (fun t => (P t).minus)) |>.trans (familyPortEquiv k false)
  internalArity z := (P z.1).internalArity z.2

@[simp] lemma family_plus_internal (t : T) (i : I t) :
    (family P).plus (.inl ⟨t,i⟩)=familyPortEquiv k true ⟨t,(P t).plus (.inl i)⟩ := rfl
@[simp] lemma family_minus_internal (t : T) (i : I t) :
    (family P).minus (.inl ⟨t,i⟩)=familyPortEquiv k false ⟨t,(P t).minus (.inl i)⟩ := rfl
@[simp] lemma family_plus_external (t : T) (a : A t) :
    (family P).plus (.inr ⟨t,a⟩)=familyPortEquiv k true ⟨t,(P t).plus (.inr a)⟩ := rfl
@[simp] lemma family_minus_external (t : T) (b : B t) :
    (family P).minus (.inr ⟨t,b⟩)=familyPortEquiv k false ⟨t,(P t).minus (.inr b)⟩ := rfl

/-- Preservation of every internal seam under arbitrary legitimate external gluing, including self-incidence and repeated old facet names. -/
theorem family_internal_unchanged (e : ((t : T) × A t) ≃ ((t : T) × B t))
    (he : ∀ a, (familyKind k ((family P).minus (.inr (e a))).val.1).arity
      ((family P).minus (.inr (e a))).val.2 =
      (familyKind k ((family P).plus (.inr a)).val.1).arity ((family P).plus (.inr a)).val.2)
    (t : T) (i : I t) :
    ((family P).complete e he).wire (familyPortEquiv k true ⟨t,(P t).plus (.inl i)⟩)=
      familyPortEquiv k false ⟨t,(P t).minus (.inl i)⟩ :=
  (family P).complete_internal e he ⟨t,i⟩

end PortPatch

/-- Old facet names may repeat while every new strip has its own copy. -/
def familyDecoration {T F : Type} {V : T → Type} {k : (t : T) → V t → Kind}
    (d : (t : T) → (v : V t) → Decoration (k t v) F) :
    (z : (t : T) × V t) → Decoration (familyKind k z) F := fun z => d z.1 z.2

end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable

/-- Inclusion of one occurrence-sensitive local patch into a disjoint family. -/
def familyEnd {T : Type} {V : T → Type} (k : (t : T) → V t → Kind)
    (t : T) (x : LocalEnd (V t) (k t)) : LocalEnd ((t : T) × V t) (familyKind k) :=
  ⟨⟨t,x.1⟩,x.2⟩

@[simp] lemma familyEnd_mate {T : Type} {V : T → Type} (k : (t : T) → V t → Kind)
    (t : T) (x : LocalEnd (V t) (k t)) :
    localMate (familyEnd k t x)=familyEnd k t (localMate x) := rfl

namespace PortPatch
variable {V I A B : Type} {k : V → Kind}

/-- Explicit internal oriented polygon. Every field is finite combinatorial source data; no flag lift or geometric bundle property is a field here. -/
structure InternalCycle (P : PortPatch k I A B) (l : ℕ) where
  positive : 0<l
  seam : Fin l ↪ I
  plusEnd : Fin l → LocalEnd V k
  minusEnd : Fin l → LocalEnd V k
  plus_port : ∀ j, (⟨(plusEnd j).1,(plusEnd j).2.1⟩ : LocalPort V k)=(P.plus (.inl (seam j))).val
  minus_port : ∀ j, (⟨(minusEnd j).1,(minusEnd j).2.1⟩ : LocalPort V k)=(P.minus (.inl (seam j))).val
  child : ∀ j, (minusEnd j).2.2.isNone=false
  same_number : ∀ j,
    (plusEnd j).2.2.map (fun c => ((k (plusEnd j).1).childEnumeration (plusEnd j).2.1 c).val)=
      (minusEnd j).2.2.map (fun c => ((k (minusEnd j).1).childEnumeration (minusEnd j).2.1 c).val)
  corner : ∀ j, localMate (minusEnd j)=plusEnd ⟨(j.val+1)%l,Nat.mod_lt _ positive⟩

namespace InternalCycle
variable {T : Type} {V I A B : T → Type} {k : (t : T) → V t → Kind}
variable (P : (t : T) → PortPatch (k t) (I t) (A t) (B t))
variable (e : ((t : T) × A t) ≃ ((t : T) × B t))
variable (he : ∀ a, (familyKind k ((family P).minus (.inr (e a))).val.1).arity
      ((family P).minus (.inr (e a))).val.2 =
      (familyKind k ((family P).plus (.inr a)).val.1).arity ((family P).plus (.inr a)).val.2)
variable {t : T} {l : ℕ} (C : InternalCycle (P t) l)

lemma plus_end (j : Fin l) :
    ((family P).complete e he).endOf
      ⟨⟨t,(C.plusEnd j).1⟩,(C.plusEnd j).2.1⟩=
        ((family P).plus (.inl ⟨t,C.seam j⟩),true) := by
  have hp : (⟨⟨t,(C.plusEnd j).1⟩,(C.plusEnd j).2.1⟩ : LocalPort _ (familyKind k))=
      ((family P).plus (.inl ⟨t,C.seam j⟩)).val :=
    congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k)))
      (C.plus_port j)
  rw [hp]
  exact ((family P).complete e he).endOf_portAt ((family P).plus (.inl ⟨t,C.seam j⟩),true)

lemma minus_end (j : Fin l) :
    ((family P).complete e he).endOf
      ⟨⟨t,(C.minusEnd j).1⟩,(C.minusEnd j).2.1⟩=
        ((family P).plus (.inl ⟨t,C.seam j⟩),false) := by
  have hp : (⟨⟨t,(C.minusEnd j).1⟩,(C.minusEnd j).2.1⟩ : LocalPort _ (familyKind k))=
      ((family P).minus (.inl ⟨t,C.seam j⟩)).val :=
    congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k)))
      (C.minus_port j)
  rw [hp,← (family P).complete_internal e he ⟨t,C.seam j⟩]
  exact ((family P).complete e he).endOf_portAt ((family P).plus (.inl ⟨t,C.seam j⟩),false)

lemma sides_equal (j : Fin l) :
    ((family P).complete e he).sideOf (familyEnd k t (C.plusEnd j))=
      ((family P).complete e he).sideOf (familyEnd k t (C.minusEnd j)) := by
  apply PortWiring.sideOf_eq
  · exact (congrArg Prod.fst (C.plus_end P e he j)).trans
      (congrArg Prod.fst (C.minus_end P e he j)).symm
  · exact C.same_number j

lemma side_seam (j : Fin l) :
    (((family P).complete e he).sideOf (familyEnd k t (C.plusEnd j))).1=
      (family P).plus (.inl ⟨t,C.seam j⟩) := congrArg Prod.fst (C.plus_end P e he j)

lemma sides_injective : Function.Injective (fun j =>
    ((family P).complete e he).sideOf (familyEnd k t (C.plusEnd j))) := by
  intro i j hh
  have hs := congrArg Sigma.fst hh
  rw [C.side_seam P e he,C.side_seam P e he] at hs
  have hs' := Sum.inl.inj ((family P).plus.injective hs)
  have hj : C.seam i=C.seam j := eq_of_heq (Sigma.mk.inj_iff.mp hs').2
  exact C.seam.injective hj

/-- Protected boundary polygon in an arbitrarily large sewn family, including every wrap and any repeated use of an old facet. -/
theorem boundary_next {F : Type}
    (facet : Side ((family P).complete e he).Seam ((family P).complete e he).seamArity → F)
    (hc : ∀ x, facet (((family P).complete e he).sideOf (localMate x))=
      facet (((family P).complete e he).sideOf x)) (j : Fin l) :
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext
      (((family P).complete e he).sideOf (familyEnd k t (C.plusEnd j)))=
        ((family P).complete e he).sideOf
          (familyEnd k t (C.plusEnd ⟨(j.val+1)%l,Nat.mod_lt _ C.positive⟩)) := by
  rw [C.sides_equal P e he j]
  rw [PortWiring.boundaryNext_local]
  · rw [familyEnd_mate,C.corner]
  · change (k t (C.minusEnd j).1).table.endpoint (C.minusEnd j).2.1=(C.minusEnd j).2.2.isNone
    rw [C.child]
    have hp := congrArg (fun p : LocalPort (V t) (k t) => (k t p.1).table.endpoint p.2)
      (C.minus_port j)
    exact hp.trans ((P t).minus (.inl (C.seam j))).property

end InternalCycle
end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortPatch
variable {V I A B : Type} {k : V → Kind}

/-- A finite parent route in a replacement, before any global sewing. The only fields are endpoint equalities in finite permitted-vertex tables. -/
structure ParentPath (P : PortPatch k I A B) (n : ℕ) (a : A) (b : B) where
  node : Fin (n+1) → LocalEnd V k
  parent : ∀ j,(node j).2.2=none
  parentMate : ∀ j,(localMate (node j)).2.2=none
  positive : ∀ j,(k (node j).1).table.endpoint (node j).2.1=true
  seam : Fin n → I
  plus_port : ∀ i, (⟨(node i.succ).1,(node i.succ).2.1⟩ : LocalPort V k)=(P.plus (.inl (seam i))).val
  minus_port : ∀ i, (⟨(localMate (node i.castSucc)).1,(localMate (node i.castSucc)).2.1⟩ : LocalPort V k)=
    (P.minus (.inl (seam i))).val
  first_port : (⟨(node 0).1,(node 0).2.1⟩ : LocalPort V k)=(P.plus (.inr a)).val
  last_port : (⟨(localMate (node (Fin.last n))).1,(localMate (node (Fin.last n))).2.1⟩ : LocalPort V k)=
    (P.minus (.inr b)).val

namespace ParentPath
variable {T : Type} {V I A B : T → Type} {k : (t : T) → V t → Kind}
variable (P : (t : T) → PortPatch (k t) (I t) (A t) (B t))
variable (e : ((t : T) × A t) ≃ ((t : T) × B t))
variable (he : ∀ a, (familyKind k ((family P).minus (.inr (e a))).val.1).arity
      ((family P).minus (.inr (e a))).val.2 =
      (familyKind k ((family P).plus (.inr a)).val.1).arity ((family P).plus (.inr a)).val.2)
variable {t : T} {n : ℕ} {a : A t} {b : B t} (C : ParentPath (P t) n a b)

lemma along_sides (i : Fin n) :
    ((family P).complete e he).sideOf (familyEnd k t (localMate (C.node i.castSucc)))=
      ((family P).complete e he).sideOf (familyEnd k t (C.node i.succ)) := by
  apply PortWiring.sideOf_eq
  · have hplus : (⟨⟨t,(C.node i.succ).1⟩,(C.node i.succ).2.1⟩ : LocalPort _ (familyKind k))=
        ((family P).plus (.inl ⟨t,C.seam i⟩)).val :=
      congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k))) (C.plus_port i)
    have hminus : (⟨⟨t,(localMate (C.node i.castSucc)).1⟩,(localMate (C.node i.castSucc)).2.1⟩ :
        LocalPort _ (familyKind k))=((family P).minus (.inl ⟨t,C.seam i⟩)).val :=
      congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k))) (C.minus_port i)
    change (((family P).complete e he).endOf _).1=(((family P).complete e he).endOf _).1
    dsimp only [familyEnd]
    rw [hplus,hminus,← (family P).complete_internal e he ⟨t,C.seam i⟩]
    exact (congrArg Prod.fst (((family P).complete e he).endOf_portAt
      ((family P).plus (.inl ⟨t,C.seam i⟩),false))).trans
      (congrArg Prod.fst (((family P).complete e he).endOf_portAt
        ((family P).plus (.inl ⟨t,C.seam i⟩),true))).symm
  · change (localMate (C.node i.castSucc)).2.2.map _=(C.node i.succ).2.2.map _
    rw [C.parentMate,C.parent]
    rfl

lemma first_side :
    ((family P).complete e he).sideOf (familyEnd k t (C.node 0))=
      ⟨(family P).plus (.inr ⟨t,a⟩),none⟩ := by
  apply sideNumber_injective
  rw [PortWiring.sideOf_number]
  have hp : (⟨⟨t,(C.node 0).1⟩,(C.node 0).2.1⟩ : LocalPort _ (familyKind k))=
      ((family P).plus (.inr ⟨t,a⟩)).val :=
    congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k))) C.first_port
  dsimp only [familyEnd,sideNumber]
  rw [C.parent,hp]
  exact congrArg (fun z => (z.1,(none : Option ℕ)))
    (((family P).complete e he).endOf_portAt ((family P).plus (.inr ⟨t,a⟩),true))

lemma last_side :
    ((family P).complete e he).sideOf (familyEnd k t (localMate (C.node (Fin.last n))))=
      ⟨(family P).plus (.inr (e.symm ⟨t,b⟩)),none⟩ := by
  apply sideNumber_injective
  rw [PortWiring.sideOf_number]
  have hp : (⟨⟨t,(localMate (C.node (Fin.last n))).1⟩,(localMate (C.node (Fin.last n))).2.1⟩ :
      LocalPort _ (familyKind k))=((family P).minus (.inr ⟨t,b⟩)).val :=
    congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k))) C.last_port
  have hw := (family P).complete_external e he (e.symm ⟨t,b⟩)
  rw [e.apply_symm_apply] at hw
  dsimp only [familyEnd,sideNumber]
  rw [C.parentMate,hp,← hw]
  exact congrArg (fun z => (z.1,(none : Option ℕ)))
    (((family P).complete e he).endOf_portAt ((family P).plus (.inr (e.symm ⟨t,b⟩)),false))

variable {F : Type}
variable (facet : Side ((family P).complete e he).Seam ((family P).complete e he).seamArity → F)
variable (hc : ∀ x, facet (((family P).complete e he).sideOf (localMate x))=
  facet (((family P).complete e he).sideOf x))

lemma boundary_step (i : Fin n) :
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext
      (((family P).complete e he).sideOf (familyEnd k t (C.node i.castSucc)))=
        ((family P).complete e he).sideOf (familyEnd k t (C.node i.succ)) := by
  rw [PortWiring.boundaryNext_local]
  · rw [familyEnd_mate]
    exact C.along_sides P e he i
  · change (k t (C.node i.castSucc).1).table.endpoint (C.node i.castSucc).2.1=(C.node i.castSucc).2.2.isNone
    rw [C.parent,C.positive]
    rfl

lemma boundary_iterate (j : Fin (n+1)) :
    ((((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext^[j.val])
      (((family P).complete e he).sideOf (familyEnd k t (C.node 0)))=
        ((family P).complete e he).sideOf (familyEnd k t (C.node j)) := by
  refine Fin.induction ?_ (fun i ih => ?_) j
  · rfl
  · simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ,Function.iterate_succ_apply',ih]
    exact C.boundary_step P e he facet hc i

/-- The sewn boundary traverses the full parent route and exits on its designated exterior lane; exterior wiring was completely arbitrary. -/
theorem boundary_exit :
    ((((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext^[n+1])
      (((family P).complete e he).sideOf (familyEnd k t (C.node 0)))=
        ((family P).complete e he).sideOf (familyEnd k t (localMate (C.node (Fin.last n)))) := by
  rw [Function.iterate_succ_apply']
  have hh := C.boundary_iterate P e he facet hc (Fin.last n)
  simp only [Fin.val_last] at hh
  rw [hh]
  rw [PortWiring.boundaryNext_local]
  · rfl
  · change (k t (C.node (Fin.last n)).1).table.endpoint (C.node (Fin.last n)).2.1=
      (C.node (Fin.last n)).2.2.isNone
    rw [C.parent,C.positive]
    rfl
include C in

theorem boundary_exterior :
    ((((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext^[n+1])
      ⟨(family P).plus (.inr ⟨t,a⟩),none⟩=
        ⟨(family P).plus (.inr (e.symm ⟨t,b⟩)),none⟩ := by
  rw [← C.first_side P e he,← C.last_side P e he]
  exact C.boundary_exit P e he facet hc

end ParentPath
end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical
open VertexTable

/-- The ten permitted vertices for the band reduction, complementary-swap replacement. U,Q follow old positive time; A,B follow the opposite orientation. -/
inductive Vertex where
  | uIn | bIn | qIn | aIn | uSwap | qSwap | uOut | aOut | qOut | bOut
  deriving DecidableEq

inductive Facet where
  | U | Q | A | B | TB | HX | TA | HY | a | b | h | x | y
  deriving DecidableEq


def vertexEnum : Fin 10 → Vertex := ![.uIn,.bIn,.qIn,.aIn,.uSwap,.qSwap,.uOut,.aOut,.qOut,.bOut]
instance : Finite Vertex := Finite.of_surjective vertexEnum (by
  intro v
  cases v <;> first
    | exact ⟨0,rfl⟩
    | exact ⟨1,rfl⟩
    | exact ⟨2,rfl⟩
    | exact ⟨3,rfl⟩
    | exact ⟨4,rfl⟩
    | exact ⟨5,rfl⟩
    | exact ⟨6,rfl⟩
    | exact ⟨7,rfl⟩
    | exact ⟨8,rfl⟩
    | exact ⟨9,rfl⟩)

def facetEnum : Fin 13 → Facet := ![.U,.Q,.A,.B,.TB,.HX,.TA,.HY,.a,.b,.h,.x,.y]
instance : Finite Facet := Finite.of_surjective facetEnum (by
  intro f
  cases f <;> first
    | exact ⟨0,rfl⟩
    | exact ⟨1,rfl⟩
    | exact ⟨2,rfl⟩
    | exact ⟨3,rfl⟩
    | exact ⟨4,rfl⟩
    | exact ⟨5,rfl⟩
    | exact ⟨6,rfl⟩
    | exact ⟨7,rfl⟩
    | exact ⟨8,rfl⟩
    | exact ⟨9,rfl⟩
    | exact ⟨10,rfl⟩
    | exact ⟨11,rfl⟩
    | exact ⟨12,rfl⟩)

def kind : Vertex → Kind
  | .uIn => .splitting 1 2 0 false
  | .bIn => .splitting 0 2 1 true
  | .qIn => .splitting 0 2 1 false
  | .aIn => .splitting 1 2 0 true
  | .uSwap => .passage 3 (.interchange 0)
  | .qSwap => .passage 3 (.interchange 1)
  | .uOut => .splitting 1 2 0 true
  | .aOut => .splitting 0 2 1 false
  | .qOut => .splitting 0 2 1 true
  | .bOut => .splitting 1 2 0 false

/-- The first ten entries are internal seams; the last four are the exposed U,Q,A,B positive-endpoint ports. Each is a whole ordered seam list. -/
def plusList : Fin 14 → PortAt kind true := ![
  ⟨⟨.uIn,.branch⟩,rfl⟩, ⟨⟨.qIn,.branch⟩,rfl⟩,
  ⟨⟨.aOut,.branch⟩,rfl⟩, ⟨⟨.bOut,.branch⟩,rfl⟩,
  ⟨⟨.uSwap,false⟩,rfl⟩, ⟨⟨.uOut,.after⟩,rfl⟩,
  ⟨⟨.qSwap,false⟩,rfl⟩, ⟨⟨.qOut,.after⟩,rfl⟩,
  ⟨⟨.aIn,.after⟩,rfl⟩, ⟨⟨.bIn,.after⟩,rfl⟩,
  ⟨⟨.uIn,.before⟩,rfl⟩, ⟨⟨.qIn,.before⟩,rfl⟩,
  ⟨⟨.aOut,.before⟩,rfl⟩, ⟨⟨.bOut,.before⟩,rfl⟩]

def minusList : Fin 14 → PortAt kind false := ![
  ⟨⟨.bIn,.branch⟩,rfl⟩, ⟨⟨.aIn,.branch⟩,rfl⟩,
  ⟨⟨.uOut,.branch⟩,rfl⟩, ⟨⟨.qOut,.branch⟩,rfl⟩,
  ⟨⟨.uIn,.after⟩,rfl⟩, ⟨⟨.uSwap,true⟩,rfl⟩,
  ⟨⟨.qIn,.after⟩,rfl⟩, ⟨⟨.qSwap,true⟩,rfl⟩,
  ⟨⟨.aOut,.after⟩,rfl⟩, ⟨⟨.bOut,.after⟩,rfl⟩,
  ⟨⟨.uOut,.before⟩,rfl⟩, ⟨⟨.qOut,.before⟩,rfl⟩,
  ⟨⟨.aIn,.before⟩,rfl⟩, ⟨⟨.bIn,.before⟩,rfl⟩]

def plusIndex : LocalPort Vertex kind → Fin 14
  | ⟨.uIn,.branch⟩ => 0 | ⟨.qIn,.branch⟩ => 1
  | ⟨.aOut,.branch⟩ => 2 | ⟨.bOut,.branch⟩ => 3
  | ⟨.uSwap,false⟩ => 4 | ⟨.uOut,.after⟩ => 5
  | ⟨.qSwap,false⟩ => 6 | ⟨.qOut,.after⟩ => 7
  | ⟨.aIn,.after⟩ => 8 | ⟨.bIn,.after⟩ => 9
  | ⟨.uIn,.before⟩ => 10 | ⟨.qIn,.before⟩ => 11
  | ⟨.aOut,.before⟩ => 12 | ⟨.bOut,.before⟩ => 13
  | _ => 0

def minusIndex : LocalPort Vertex kind → Fin 14
  | ⟨.bIn,.branch⟩ => 0 | ⟨.aIn,.branch⟩ => 1
  | ⟨.uOut,.branch⟩ => 2 | ⟨.qOut,.branch⟩ => 3
  | ⟨.uIn,.after⟩ => 4 | ⟨.uSwap,true⟩ => 5
  | ⟨.qIn,.after⟩ => 6 | ⟨.qSwap,true⟩ => 7
  | ⟨.aOut,.after⟩ => 8 | ⟨.bOut,.after⟩ => 9
  | ⟨.uOut,.before⟩ => 10 | ⟨.qOut,.before⟩ => 11
  | ⟨.aIn,.before⟩ => 12 | ⟨.bIn,.before⟩ => 13
  | _ => 0

def plusEquiv : Fin 14 ≃ PortAt kind true where
  toFun := plusList
  invFun p := plusIndex p.val
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨v,p⟩,he⟩
    cases v <;> cases p <;> first | rfl | cases he

def minusEquiv : Fin 14 ≃ PortAt kind false where
  toFun := minusList
  invFun p := minusIndex p.val
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨v,p⟩,he⟩
    cases v <;> cases p <;> first | rfl | cases he

/-- Local incidence recipe. It contains all ten allowed vertices and all ten internal seams, with the eight boundary ports left exposed. -/
def patch : PortPatch kind (Fin 10) (Fin 4) (Fin 4) where
  plus := finSumFinEquiv.trans plusEquiv
  minus := finSumFinEquiv.trans minusEquiv
  internalArity i := by fin_cases i <;> rfl

/-- The facet/strip names incident at every corner. A global use may map different A/B names to the same old facet without changing occurrences. -/
def decoration : (v : Vertex) → Decoration (kind v) Facet
  | .uIn => splittingDecoration false .U .TB ![.a] ![.b,.h] ![]
  | .bIn => splittingDecoration true .B .TB ![] ![.b,.h] ![.y]
  | .qIn => splittingDecoration false .Q .HX ![] ![.h,.x] ![.y]
  | .aIn => splittingDecoration true .A .HX ![.a] ![.h,.x] ![]
  | .uSwap => passageDecoration (.interchange 0) .U ![.a,.b,.h]
  | .qSwap => passageDecoration (.interchange 1) .Q ![.h,.x,.y]
  | .uOut => splittingDecoration true .U .TA ![.b] ![.a,.h] ![]
  | .aOut => splittingDecoration false .A .TA ![] ![.a,.h] ![.x]
  | .qOut => splittingDecoration true .Q .HY ![] ![.h,.y] ![.x]
  | .bOut => splittingDecoration false .B .HY ![.b] ![.h,.y] ![]

/-- The source's numerical rank array, before deletion of zero pieces. -/
def rank (a b h x y : ℕ) : Facet → ℕ
  | .U => a+b+h | .Q => h+x+y | .A => a+h+x | .B => b+h+y
  | .TB => b+h | .HX => h+x | .TA => a+h | .HY => h+y
  | .a => a | .b => b | .h => h | .x => x | .y => y

end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch

namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical
open VertexTable

/-- U route: split tilde-b, interchange a,b, merge a,h. -/
def uParentPath : PortPatch.ParentPath patch 2 (0 : Fin 4) 0 where
  node := ![⟨.uIn,.before,none⟩,⟨.uSwap,false,none⟩,⟨.uOut,.after,none⟩]
  parent j := by fin_cases j <;> rfl
  parentMate j := by fin_cases j <;> rfl
  positive j := by fin_cases j <;> rfl
  seam := ![4,5]
  plus_port i := by fin_cases i <;> rfl
  minus_port i := by fin_cases i <;> rfl
  first_port := rfl
  last_port := rfl

/-- Q route, through the complementary interchange x,y. -/
def qParentPath : PortPatch.ParentPath patch 2 (1 : Fin 4) 1 where
  node := ![⟨.qIn,.before,none⟩,⟨.qSwap,false,none⟩,⟨.qOut,.after,none⟩]
  parent j := by fin_cases j <;> rfl
  parentMate j := by fin_cases j <;> rfl
  positive j := by fin_cases j <;> rfl
  seam := ![6,7]
  plus_port i := by fin_cases i <;> rfl
  minus_port i := by fin_cases i <;> rfl
  first_port := rfl
  last_port := rfl

/-- A keeps its old surface orientation; time on it is opposite to U,Q. -/
def aParentPath : PortPatch.ParentPath patch 1 (2 : Fin 4) 2 where
  node := ![⟨.aOut,.before,none⟩,⟨.aIn,.after,none⟩]
  parent j := by fin_cases j <;> rfl
  parentMate j := by fin_cases j <;> rfl
  positive j := by fin_cases j <;> rfl
  seam := ![8]
  plus_port i := by fin_cases i; rfl
  minus_port i := by fin_cases i; rfl
  first_port := rfl
  last_port := rfl

def bParentPath : PortPatch.ParentPath patch 1 (3 : Fin 4) 3 where
  node := ![⟨.bOut,.before,none⟩,⟨.bIn,.after,none⟩]
  parent j := by fin_cases j <;> rfl
  parentMate j := by fin_cases j <;> rfl
  positive j := by fin_cases j <;> rfl
  seam := ![9]
  plus_port i := by fin_cases i; rfl
  minus_port i := by fin_cases i; rfl
  first_port := rfl
  last_port := rfl

/-- All parent route nodes preserve the named surface, not only ranks. -/
theorem parent_path_colors :
    (∀ j,(decoration (uParentPath.node j).1).color (uParentPath.node j).2=.U) ∧
    (∀ j,(decoration (qParentPath.node j).1).color (qParentPath.node j).2=.Q) ∧
    (∀ j,(decoration (aParentPath.node j).1).color (aParentPath.node j).2=.A) ∧
    (∀ j,(decoration (bParentPath.node j).1).color (bParentPath.node j).2=.B) := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro j <;> fin_cases j <;> rfl
end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch

end

end OAI
