import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.GraftCircuits
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryReordering

namespace OAI

/-!
# Boundary orbits of the refined inverse-band diagram.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))

include hp hc hc' in
lemma refinedAtomicGraft_seamRank (s) :
    D.ports.refinedRank q d D.rank ((D.ports.refinedAtomicGraft q d).facet ⟨s,none⟩)=
      ∑ i,D.ports.refinedRank q d D.rank ((D.ports.refinedAtomicGraft q d).facet ⟨s,some i⟩) := by
  apply (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)).graftBand_seamRank q
    (D.ports.refinedBandForSeam q d) (D.ports.refinedRank q d D.rank)
  · exact D.seamRank
  · exact d.refinedAtomicBand_conservative D.rank (D.ports.facet ⟨q,none⟩)
      (fun i => D.ports.facet ⟨q,some i⟩) (fun i => D.ports.facet ⟨q,some i⟩) hp hc hc'

noncomputable def refinedGenus : D.ports.RefinedBandFacet q d → ℕ
  | .inl f => if f=D.ports.facet ⟨q,none⟩ then D.genus f-1 else D.genus f
  | .inr _ => 0

/-- Literal inverse-band occurrence diagram with a distinct lower-rank disk for
each uncontacted strip. ALL circles are taken from the actual boundary successor;
none is supplied as a cyclic-template coverage assumption. The full solution
lift is a separate obligation and is not asserted by this constructor. -/
noncomputable def refinedCutDiagram [Finite V] :=
  SurfacePresentation.fromPorts (D.ports.refinedAtomicGraft q d)
    (D.ports.refinedRank q d D.rank) (D.refinedGenus q d)
    (D.refinedAtomicGraft_seamRank q d hp hc hc')

lemma refinedCutDiagram_rank_inl [Finite V] (f : F) :
    (D.refinedCutDiagram q d hp hc hc').rank (.inl f)=D.rank f := rfl
lemma refinedCutDiagram_genus_selected [Finite V] :
    (D.refinedCutDiagram q d hp hc hc').genus (.inl (D.ports.facet ⟨q,none⟩))=
      D.genus (D.ports.facet ⟨q,none⟩)-1 := by
  simp only [refinedCutDiagram,SurfacePresentation.fromPorts,refinedGenus,ite_true]
lemma refinedCutDiagram_genus_lt [Finite V] (hg : 0<D.genus (D.ports.facet ⟨q,none⟩)) :
    (D.refinedCutDiagram q d hp hc hc').genus (.inl (D.ports.facet ⟨q,none⟩))<
      D.genus (D.ports.facet ⟨q,none⟩) := by
  rw [D.refinedCutDiagram_genus_selected]
  omega

lemma refinedCutDiagram_fresh_rank_lt [Finite V]
    (hlt : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)<r) (x : d.atomicBand.FreshStrip) :
    (D.refinedCutDiagram q d hp hc hc').rank (.inr x)<r :=
  D.ports.refinedRank_fresh_lt q d D.rank (fun i => (hc i) ▸ hlt i)
    (fun i => (hc' i) ▸ hlt i) x

variable {R : Type*} [CommRing R] [Finite V]
noncomputable def refinedCutPunctures (P : D.Punctures R) :
    (D.refinedCutDiagram q d hp hc hc').Punctures R where
  count f := match f with
    | .inl f => P.count f
    | .inr _ => 0
  scalar f j := match f with
    | .inl f => P.scalar f j
    | .inr _ => Fin.elim0 j
end IntegralCharacterVarieties.SurfacePresentation.Diagram

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)

abbrev PortFrames := (p : LocalPort V D.ports.kind) →
  MatrixIso R ((D.vertexRanks p.1).Columns p.2) ((D.vertexRanks p.1).Parent p.2)

def localFrameUnit (f : D.PortFrames (R:=R)) (p : LocalPort V D.ports.kind) :
    (Matrix (Fin (D.seamDim (D.ports.attach p).1)) (Fin (D.seamDim (D.ports.attach p).1)) R)ˣ :=
  ((f p).reindex (D.portColumnIndex p).symm (D.portRowIndex p).symm).toUnit

def frameValues (f : D.PortFrames (R:=R)) (s : S) (b : Bool) :
    (Matrix (Fin (D.seamDim s)) (Fin (D.seamDim s)) R)ˣ :=
  cast (congrArg (fun s => (Matrix (Fin (D.seamDim s)) (Fin (D.seamDim s)) R)ˣ)
    (congrArg Prod.fst (D.ports.attach.apply_symm_apply (s,b))))
    (D.localFrameUnit f (D.ports.attach.symm (s,b)))

lemma frameValues_attach (f : D.PortFrames (R:=R)) (p : LocalPort V D.ports.kind) :
    D.frameValues f (D.ports.attach p).1 (D.ports.attach p).2=D.localFrameUnit f p := by
  unfold frameValues
  generalize_proofs h
  have aux {I : Type} (T : I → Type) (w : (i : I) → T i)
      {i j : I} (he : i=j) (ht : T i=T j) : cast ht (w i)=w j := by
    subst j
    rfl
  exact aux _ (D.localFrameUnit f) (D.ports.attach.symm_apply_apply p) h

abbrev SideValues := (a : Side S arity) →
  (Matrix (Fin (D.rank (D.ports.facet a))) (Fin (D.rank (D.ports.facet a))) R)ˣ
abbrev HandleValues := (f : F) → Fin (D.genus f) → Bool →
  (Matrix (Fin (D.rank f)) (Fin (D.rank f)) R)ˣ

def valuesFromPorts (f : D.PortFrames (R:=R)) (side : D.SideValues (R:=R))
    (handle : D.HandleValues (R:=R)) :
    (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ
  | .side a => side a
  | .frame s b => D.frameValues f s b
  | .handle z i b => handle z i b

lemma portFrame_valuesFromPorts (f : D.PortFrames (R:=R)) (side : D.SideValues (R:=R))
    (handle : D.HandleValues (R:=R)) (p : LocalPort V D.ports.kind) :
    D.portFrame (D.valuesFromPorts f side handle) p=f p := by
  change (MatrixIso.unit (D.frameValues f _ _)).reindex _ _=f p
  rw [D.frameValues_attach]
  simp only [localFrameUnit,MatrixIso.unit_toUnit,MatrixIso.reindex_reindex_eq,
    Equiv.self_trans_symm,MatrixIso.reindex_refl_eq]

lemma vertexHolds_valuesFromPorts (f : D.PortFrames (R:=R)) (side : D.SideValues (R:=R))
    (handle : D.HandleValues (R:=R))
    (hf : ∀ v,(VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
      (fun p => f ⟨v,p⟩)).Holds) :
    D.VertexHolds (D.valuesFromPorts f side handle) := by
  intro v
  simpa only [vertexComparison,D.portFrame_valuesFromPorts] using hf v
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression BoundarySurgery
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity)

def boundaryEntry (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) : Side S arity := D.boundarySide ⟨f,b,i⟩

lemma boundaryEntry_injective (f : F) (b : Fin (D.boundaryCount f)) :
    Function.Injective (D.boundaryEntry f b) := by
  intro i j h
  have he := D.boundarySide.injective h
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he

lemma boundaryEntry_next (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    D.ports.vertexAssembly.corners.boundaryNext (D.boundaryEntry f b i)=
      D.boundaryEntry f b (finRotate (D.boundaryLength f b) i) := by
  rw [boundaryEntry,D.boundaryNext]
  congr 1
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  apply Fin.ext
  simp [finRotate_apply, Fin.add_def, Nat.add_mod]

lemma boundaryEntry_pow_lt (f : F) (b : Fin (D.boundaryCount f)) (k : ℕ)
    (hk : k<D.boundaryLength f b) :
    (D.ports.vertexAssembly.corners.boundaryNext^k)
      (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩)=D.boundaryEntry f b ⟨k,hk⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih (by omega),D.boundaryEntry_next]
    congr 1
    apply Fin.ext
    simpa [finRotate_apply, Fin.add_def, Nat.add_mod] using (Nat.mod_eq_of_lt hk)

def boundarySet (f : F) (b : Fin (D.boundaryCount f)) : Finset (Side S arity) :=
  Finset.univ.image (D.boundaryEntry f b)

lemma boundarySet_coe (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundarySet f b : Set (Side S arity))=Set.range (D.boundaryEntry f b) := by
  ext x
  simp [boundarySet]

lemma boundarySet_card (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundarySet f b).card=D.boundaryLength f b := by
  simp [boundarySet,Finset.card_image_of_injective _ (D.boundaryEntry_injective f b)]

lemma boundarySet_isCycle (f : F) (b : Fin (D.boundaryCount f)) :
    D.ports.vertexAssembly.corners.boundaryNext.IsCycleOn (D.boundarySet f b : Set (Side S arity)) := by
  rw [D.boundarySet_coe]
  refine ⟨⟨?_,D.ports.vertexAssembly.corners.boundaryNext.injective.injOn,?_⟩,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨_,(D.boundaryEntry_next f b i).symm⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨D.boundaryEntry f b ((finRotate _).symm i),⟨_,rfl⟩,
      by rw [D.boundaryEntry_next,Equiv.apply_symm_apply]⟩
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    have hi : D.ports.vertexAssembly.corners.boundaryNext.SameCycle
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryEntry f b i) :=
      ⟨(i.val : ℤ),by simpa using D.boundaryEntry_pow_lt f b i.val i.isLt⟩
    have hj : D.ports.vertexAssembly.corners.boundaryNext.SameCycle
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryEntry f b j) :=
      ⟨(j.val : ℤ),by simpa using D.boundaryEntry_pow_lt f b j.val j.isLt⟩
    exact hi.symm.trans hj

def sideCoefficient (u : D.SideValues (R:=A)) (f : F) (a : Side S arity) :
    (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ :=
  if h : D.ports.facet a=f then rebaseUnit (congrArg D.rank h) (u a) else 1

lemma sideCoefficient_boundary (u : D.SideValues (R:=A)) (f : F)
    (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    D.sideCoefficient u f (D.boundaryEntry f b i)=
      rebaseUnit (congrArg D.rank (D.boundaryFacet f b i)) (u (D.boundaryEntry f b i)) := by
  unfold sideCoefficient boundaryEntry
  rw [dite_eq_left (D.boundaryFacet f b i)]

lemma eval_subst_rank {E : Type} {rank : E → ℕ} (φ : R →+* A)
    (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) A)ˣ)
    {n m : ℕ} (h : n=m) (t : Term R E rank n) :
    Term.eval φ g (h ▸ t)=rebaseUnit h (Term.eval φ g t) := by
  subst m
  rfl

lemma boundaryWord_cycleWord (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord f b).eval φ g=
      cycleWord D.ports.vertexAssembly.corners.boundaryNext
        (D.sideCoefficient (fun a=>g (.side a)) f)
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryLength f b) := by
  rw [D.boundaryWord_eval_raw]
  unfold cycleWord
  congr 2
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hki : k < D.boundaryLength f b := by simpa using hk
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [D.boundaryEntry_pow_lt f b k hki]
    erw [D.sideCoefficient_boundary]
    unfold boundaryEdgeWord
    convert! eval_subst_rank φ g (congrArg D.rank (D.boundaryFacet f b ⟨k,hki⟩))
        (D.sideWord (D.boundarySide ⟨f,b,⟨k,hki⟩⟩)) using 1
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma oldEmbedding_any_parent (s : S) : oldEmbedding A q B ⟨s,none⟩=oldSide A q B s := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inl (A.wiringSides ⟨s,none⟩)))=_
  rw [A.toWiring.sumSides_number_left]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inl x.1),x.2))
    (A.wiringSides_number ⟨s,none⟩)
lemma bandEmbedding_origPrincipal (v : Fin (B.length+1)) :
    bandEmbedding A q B (B.origPrincipal v)=originalSide A q B v := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.origPrincipal v)))=_
  rw [A.toWiring.sumSides_number_right]
  have h : sideNumber (B.origPrincipal v)=
      (sumPortAt B.kind (mirrorKind B.kind) true (.inl (VariableGallery.input B.kind v)),none) := by
    rw [RealizedBand.origPrincipal,B.doubleWiring.sideOf_number]
    change ((B.doubleWiring.endOf (sumPortAt B.kind (mirrorKind B.kind) true
      (.inl (VariableGallery.input B.kind v))).val).1,none)=_
    rw [B.doubleWiring.endOf_positive]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h
lemma bandEmbedding_mirrorPrincipal (v : Fin (B.length+1)) :
    bandEmbedding A q B (B.mirrorPrincipal v)=mirrorSide A q B v := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.mirrorPrincipal v)))=_
  rw [A.toWiring.sumSides_number_right]
  have h : sideNumber (B.mirrorPrincipal v)=
      (sumPortAt B.kind (mirrorKind B.kind) true (.inr
        (mirrorPortAt B.kind false (VariableGallery.output B.kind v))),none) := by
    rw [RealizedBand.mirrorPrincipal,B.doubleWiring.sideOf_number]
    change ((B.doubleWiring.endOf (sumPortAt B.kind (mirrorKind B.kind) true
      (.inr (mirrorPortAt B.kind false (VariableGallery.output B.kind v)))).val).1,none)=_
    rw [B.doubleWiring.endOf_positive]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h

noncomputable def principalCircle (s : Finset (Side S arity)) :
    Finset (Side (base A q B).Seam (base A q B).seamArity) :=
  s.map (oldEmbedding A q B) ∪ Finset.univ.image (originalSide A q B)

lemma principalCircle_coe (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∈s)
    (hno : ∀ z i,A.facet ⟨z,some i⟩≠A.facet ⟨q,none⟩) :
    (principalCircle A q B s : Set (Side (base A q B).Seam (base A q B).seamArity))=
      ((fun a : Side S arity => oldSide A q B a.1) '' (s : Set (Side S arity)) ∪
      Set.range (originalSide A q B)) := by
  have he : Set.EqOn (oldEmbedding A q B) (fun a : Side S arity => oldSide A q B a.1) (s : Set (Side S arity)) := by
    intro a ha
    have h := oldPrincipal_parent A q s hs hq hno a ha
    rcases a with ⟨z,c⟩; dsimp only at h; subst c
    exact oldEmbedding_any_parent A q B z
  have hc : (Finset.univ.image (originalSide A q B) : Set
      (Side (wiring A q B).Seam (wiring A q B).seamArity))=Set.range (originalSide A q B) := by
    ext a
    constructor
    · intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      exact ⟨i,hi⟩
    · rintro ⟨i,rfl⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  simp only [principalCircle,Finset.coe_union,Finset.coe_map]
  erw [hc]
  exact congrArg (fun t => t ∪ Set.range (originalSide A q B)) (Set.image_congr he)

lemma principalCircle_isCycle (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∈s)
    (hno : ∀ z i,A.facet ⟨z,some i⟩≠A.facet ⟨q,none⟩) :
    (next A q B).IsCycleOn (principalCircle A q B s : Set (Side (base A q B).Seam (base A q B).seamArity)) := by
  rw [principalCircle_coe A q B s hs hq hno]
  exact principalChain_isCycle A q B s hs hq hno
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    (B : RealizedBand (D.ports.facet ⟨q,none⟩) (D.ports.seamChildren q) (D.ports.seamChildren q))
noncomputable def oldGraftCircle (f : F) (b : Fin (D.boundaryCount f)) :
    Finset (Side (base D.ports q B).Seam (base D.ports q B).seamArity) :=
  if (⟨q,none⟩ : Side S arity)∈D.boundarySet f b then principalCircle D.ports q B (D.boundarySet f b)
  else secondaryCircle D.ports q B (D.boundarySet f b)

lemma boundarySet_exhaustive (a : Side S arity) :
    ∃ f b,a∈D.boundarySet f b := by
  obtain ⟨⟨f,b,i⟩,rfl⟩ := D.boundarySide.surjective a
  exact ⟨f,b,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

lemma old_mem_graftCircle (f : F) (b : Fin (D.boundaryCount f))
    (a : Side S arity) (ha : a∈D.boundarySet f b) :
    oldEmbedding D.ports q B a∈D.oldGraftCircle q B f b := by
  by_cases h : (⟨q,none⟩ : Side S arity)∈D.boundarySet f b
  · rw [oldGraftCircle,ite_eq_left h]
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
  · rw [oldGraftCircle,ite_eq_right h]
    exact attachedCircleOn_subset _ _ _ _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩)

lemma oldGraftCircle_isCycle (f : F) (b : Fin (D.boundaryCount f))
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩) :
    (next D.ports q B).IsCycleOn
      (D.oldGraftCircle q B f b : Set (Side (base D.ports q B).Seam (base D.ports q B).seamArity)) := by
  by_cases h : (⟨q,none⟩ : Side S arity)∈D.boundarySet f b
  · rw [oldGraftCircle,ite_eq_left h]
    exact principalCircle_isCycle D.ports q B _ (D.boundarySet_isCycle f b) h hno
  · rw [oldGraftCircle,ite_eq_right h]
    exact (actual_secondary_circle D.ports q B _ (D.boundarySet_isCycle f b) h hinj
      (fun _ => (1 : Equiv.Perm Unit)) (by intros; rfl)).1

/-- Every side of the actual reconstructed diagram belongs to an explicitly
identified actual circle: one from an old boundary, the extra principal circle,
or a single untouched connected strip. This is an exhaustive geometric sewing
statement, not rank conservation or a template enumeration. -/
theorem actual_circle_exhaustion
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (a : Side (base D.ports q B).Seam (base D.ports q B).seamArity) :
    (∃ f b,a∈D.oldGraftCircle q B f b) ∨
    (∃ i,a=mirrorEntry D.ports q B i) ∨
    (∃ r : B.FreshStrip,a∈(B.stripFinset r.val.val).map (bandEmbedding D.ports q B)) := by
  rcases literal_germ_exhaustion D.ports q B a with
    ⟨x,rfl⟩|⟨v,rfl⟩|⟨v,rfl⟩|⟨j,hj⟩|hf
  · obtain ⟨f,b,hb⟩ := D.boundarySet_exhaustive x
    exact Or.inl ⟨f,b,D.old_mem_graftCircle q B f b x hb⟩
  · obtain ⟨f,b,hb⟩ := D.boundarySet_exhaustive ⟨q,none⟩
    apply Or.inl
    refine ⟨f,b,?_⟩
    rw [oldGraftCircle,ite_eq_left hb,bandEmbedding_origPrincipal]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  · apply Or.inr; apply Or.inl
    refine ⟨v.rev,?_⟩
    rw [bandEmbedding_mirrorPrincipal,mirrorEntry,Fin.rev_rev]
  · obtain ⟨f,b,hb⟩ := D.boundarySet_exhaustive ⟨q,some (finCongr (cutPort_arity D.ports q B) j.1)⟩
    have hn : (⟨q,none⟩ : Side S arity)∉D.boundarySet f b := by
      intro hp
      have hh := oldPrincipal_parent D.ports q _ (D.boundarySet_isCycle f b) hp hno _ hb
      cases hh
    apply Or.inl
    refine ⟨f,b,?_⟩
    rw [oldGraftCircle,ite_eq_right hn]
    exact shortCycle_in_secondary D.ports q B _ j hb hj
  · exact Or.inr (Or.inr hf)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
variable {α ι : Type}
lemma mem_attachedCircleOn_iff (s : Finset α) (x : ι → α) (t : ι → Finset α)
    (is : List ι) (a : α) (ha : ∀ i,a∉t i) :
    a∈attachedCircleOn s x t is ↔ a∈s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    change a∈attachedCircleOn (if x i∈s then s∪t i else s) x t is ↔ a∈s
    rw [ih]
    by_cases h : x i∈s
    · rw [ite_eq_left h,Finset.mem_union]
      exact or_iff_left (ha i)
    · rw [ite_eq_right h]
lemma disjoint_cycles_of_mem_not_mem (N : Equiv.Perm α) (s t : Finset α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (a : α) (ha : a∈s) (hat : a∉t) : Disjoint s t := by
  apply Finset.disjoint_left.mpr
  intro b hb hbt
  obtain ⟨k,_,hk⟩ := hs.exists_pow_eq hb ha
  have hh : ∀ k : ℕ,(N^k) b∈t := by
    intro k
    induction k with
    | zero => exact hbt
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ht.1.mapsTo ih
  exact hat (hk ▸ hh k)
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma old_not_shortCycle (a : Side S arity) (j) : oldEmbedding A q B a∉shortCycle A q B j := by
  intro h
  obtain ⟨z,_,hz⟩ := Finset.mem_map.mp h
  exact old_band_ne A q B a z hz.symm
lemma old_secondaryCircle_iff (a : Side S arity) (s : Finset (Side S arity)) :
    oldEmbedding A q B a∈secondaryCircle A q B s ↔ a∈s := by
  rw [secondaryCircle,mem_attachedCircleOn_iff _ _ _ _ _ (old_not_shortCycle A q B a)]
  exact Finset.mem_map' (oldEmbedding A q B)
lemma old_principalCircle_iff (a : Side S arity) (s : Finset (Side S arity)) :
    oldEmbedding A q B a∈principalCircle A q B s ↔ a∈s := by
  rw [principalCircle,Finset.mem_union]
  have hn : oldEmbedding A q B a∉Finset.univ.image (originalSide A q B) := by
    intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    rw [←bandEmbedding_origPrincipal] at hi
    exact old_band_ne A q B a _ hi.symm
  exact (or_iff_left hn).trans (Finset.mem_map' (oldEmbedding A q B))

noncomputable def mirrorCircle : Finset (Side (base A q B).Seam (base A q B).seamArity) :=
  Finset.univ.image (mirrorEntry A q B)
lemma mirrorCircle_isCycle : (next A q B).IsCycleOn
    (mirrorCircle A q B : Set (Side (base A q B).Seam (base A q B).seamArity)) := by
  have he : (mirrorCircle A q B : Set (Side (base A q B).Seam (base A q B).seamArity))=
      Set.range (mirrorEntry A q B) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
      exact ⟨i,hi⟩
    · rintro ⟨i,rfl⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [he]
  exact mirror_isCycle A q B

lemma old_not_mirrorCircle (a : Side S arity) : oldEmbedding A q B a∉mirrorCircle A q B := by
  intro h
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  change mirrorSide A q B i.rev=oldEmbedding A q B a at hi
  rw [←bandEmbedding_mirrorPrincipal] at hi
  exact old_band_ne A q B a _ hi.symm
lemma old_not_stripCircle (a : Side S arity) (r : B.StripRoot) :
    oldEmbedding A q B a∉(B.stripFinset r.val).map (bandEmbedding A q B) := by
  intro h
  obtain ⟨z,_,hz⟩ := Finset.mem_map.mp h
  exact old_band_ne A q B a z hz.symm
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    (B : RealizedBand (D.ports.facet ⟨q,none⟩) (D.ports.seamChildren q) (D.ports.seamChildren q))
lemma old_mem_graftCircle_iff (f : F) (b : Fin (D.boundaryCount f)) (a : Side S arity) :
    oldEmbedding D.ports q B a∈D.oldGraftCircle q B f b ↔ a∈D.boundarySet f b := by
  by_cases h : (⟨q,none⟩ : Side S arity)∈D.boundarySet f b
  · rw [oldGraftCircle,ite_eq_left h]
    exact old_principalCircle_iff D.ports q B a _
  · rw [oldGraftCircle,ite_eq_right h]
    exact old_secondaryCircle_iff D.ports q B a _
lemma boundarySet_unique (z w : (f : F) × Fin (D.boundaryCount f)) (a : Side S arity)
    (hz : a∈D.boundarySet z.1 z.2) (hw : a∈D.boundarySet w.1 w.2) : z=w := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
  have he := D.boundarySide.injective (hi.trans hj.symm)
  exact congrArg (fun c : (f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b) =>
    (⟨c.1,c.2.1⟩ : (f : F) × Fin (D.boundaryCount f))) he
lemma oldGraftCircle_nonempty (f : F) (b : Fin (D.boundaryCount f)) :
    (D.oldGraftCircle q B f b).Nonempty := by
  refine ⟨oldEmbedding D.ports q B (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩),?_⟩
  apply D.old_mem_graftCircle q B
  exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
lemma oldGraftCircle_disjoint
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (z w : (f : F) × Fin (D.boundaryCount f)) (hne : z≠w) :
    Disjoint (D.oldGraftCircle q B z.1 z.2) (D.oldGraftCircle q B w.1 w.2) := by
  let a := D.boundaryEntry z.1 z.2 ⟨0,D.boundaryPositive z.1 z.2⟩
  have ha : a∈D.boundarySet z.1 z.2 := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  apply disjoint_cycles_of_mem_not_mem (next D.ports q B) _ _
    (D.oldGraftCircle_isCycle q B _ _ hinj hno) (D.oldGraftCircle_isCycle q B _ _ hinj hno)
    (oldEmbedding D.ports q B a) (D.old_mem_graftCircle q B _ _ _ ha)
  intro hw
  exact hne (D.boundarySet_unique z w a ha ((D.old_mem_graftCircle_iff q B _ _ a).mp hw))
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
noncomputable def freshCircle (r : B.FreshStrip) :=
  (B.stripFinset r.val.val).map (bandEmbedding A q B)
lemma freshCircle_nonempty (r : B.FreshStrip) : (freshCircle A q B r).Nonempty := by
  refine ⟨bandEmbedding A q B (B.origStripSide r.val.val),Finset.mem_map.mpr ⟨_,?_,rfl⟩⟩
  apply (B.mem_stripFinset _ _).mpr
  have h := B.stripCycle_mem_orig r.val.val
  rwa [B.stripForest.root_of_source r.val.val r.val.property] at h
lemma mirrorCircle_nonempty : (mirrorCircle A q B).Nonempty := by
  exact ⟨mirrorEntry A q B ⟨0,Nat.zero_lt_succ _⟩,
    Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩
lemma mirror_not_freshCircle (r : B.FreshStrip) (i) :
    mirrorEntry A q B i∉freshCircle A q B r := by
  intro h
  obtain ⟨b,hb,he⟩ := Finset.mem_map.mp h
  change bandEmbedding A q B b=mirrorSide A q B i.rev at he
  rw [←bandEmbedding_mirrorPrincipal] at he
  have hh := (bandEmbedding A q B).injective he
  subst b
  have hr := (B.sideStripRoot_eq_some_iff _ _).mpr ((B.mem_stripFinset _ _).mp hb)
  rw [B.sideStripRoot_mirrorPrincipal] at hr
  cases hr
lemma mirror_fresh_disjoint (r : B.FreshStrip) :
    Disjoint (mirrorCircle A q B) (freshCircle A q B r) := by
  apply Finset.disjoint_left.mpr
  intro a ha hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact mirror_not_freshCircle A q B r i hf
lemma freshCircle_disjoint {r t : B.FreshStrip} (h : r≠t) :
    Disjoint (freshCircle A q B r) (freshCircle A q B t) := by
  apply Finset.disjoint_left.mpr
  intro a ha ht
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨c,hc,hcb⟩ := Finset.mem_map.mp ht
  have he := (bandEmbedding A q B).injective hcb
  subst c
  exact Finset.disjoint_left.mp (B.stripFinset_disjoint
    (fun he => h (Subtype.ext (Subtype.ext he)))) hb hc
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    (B : RealizedBand (D.ports.facet ⟨q,none⟩) (D.ports.seamChildren q) (D.ports.seamChildren q))
lemma oldGraftCircle_mirror_disjoint
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (f : F) (b : Fin (D.boundaryCount f)) :
    Disjoint (D.oldGraftCircle q B f b) (mirrorCircle D.ports q B) := by
  let a := D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩
  have ha : a∈D.boundarySet f b := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  exact disjoint_cycles_of_mem_not_mem _ _ _ (D.oldGraftCircle_isCycle q B f b hinj hno)
    (mirrorCircle_isCycle D.ports q B) (oldEmbedding D.ports q B a)
    (D.old_mem_graftCircle q B f b a ha) (old_not_mirrorCircle D.ports q B a)
lemma oldGraftCircle_fresh_disjoint
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (f : F) (b : Fin (D.boundaryCount f)) (r : B.FreshStrip) :
    Disjoint (D.oldGraftCircle q B f b) (freshCircle D.ports q B r) := by
  let a := D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩
  have ha : a∈D.boundarySet f b := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  exact disjoint_cycles_of_mem_not_mem _ _ _ (D.oldGraftCircle_isCycle q B f b hinj hno)
    (freshStrip_actual_circle D.ports q B r) (oldEmbedding D.ports q B a)
    (D.old_mem_graftCircle q B f b a ha) (old_not_stripCircle D.ports q B a r.val)
abbrev GraftCircleLabel := ((f : F) × Fin (D.boundaryCount f)) ⊕ (Unit ⊕ B.FreshStrip)
noncomputable def graftCircle : D.GraftCircleLabel q B →
    Finset (Side (base D.ports q B).Seam (base D.ports q B).seamArity)
  | .inl ⟨f,b⟩ => D.oldGraftCircle q B f b
  | .inr (.inl _) => mirrorCircle D.ports q B
  | .inr (.inr r) => freshCircle D.ports q B r
lemma graftCircle_nonempty (c : D.GraftCircleLabel q B) : (D.graftCircle q B c).Nonempty := by
  rcases c with ⟨f,b⟩|(_|r)
  · exact D.oldGraftCircle_nonempty q B f b
  · exact mirrorCircle_nonempty D.ports q B
  · exact freshCircle_nonempty D.ports q B r
lemma graftCircle_isCycle
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (c : D.GraftCircleLabel q B) : (next D.ports q B).IsCycleOn
      (D.graftCircle q B c : Set (Side (base D.ports q B).Seam (base D.ports q B).seamArity)) := by
  rcases c with ⟨f,b⟩|(_|r)
  · exact D.oldGraftCircle_isCycle q B f b hinj hno
  · exact mirrorCircle_isCycle D.ports q B
  · exact freshStrip_actual_circle D.ports q B r
lemma graftCircle_disjoint
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    {c d : D.GraftCircleLabel q B} (hne : c≠d) :
    Disjoint (D.graftCircle q B c) (D.graftCircle q B d) := by
  rcases c with c|(_|c) <;> rcases d with d|(_|d)
  · exact D.oldGraftCircle_disjoint q B hinj hno c d (fun he => hne (congrArg Sum.inl he))
  · exact D.oldGraftCircle_mirror_disjoint q B hinj hno c.1 c.2
  · exact D.oldGraftCircle_fresh_disjoint q B hinj hno c.1 c.2 d
  · exact (D.oldGraftCircle_mirror_disjoint q B hinj hno d.1 d.2).symm
  · exact (hne rfl).elim
  · exact mirror_fresh_disjoint D.ports q B d
  · exact (D.oldGraftCircle_fresh_disjoint q B hinj hno d.1 d.2 c).symm
  · exact (mirror_fresh_disjoint D.ports q B c).symm
  · exact freshCircle_disjoint D.ports q B (fun he => hne (congrArg (Sum.inr ∘ Sum.inr) he))
lemma graftCircle_cover
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
    (a : Side (base D.ports q B).Seam (base D.ports q B).seamArity) :
    ∃ c : D.GraftCircleLabel q B,a∈D.graftCircle q B c := by
  rcases D.actual_circle_exhaustion q B hno a with ⟨f,b,hb⟩|⟨i,rfl⟩|⟨r,hr⟩
  · exact ⟨.inl ⟨f,b⟩,hb⟩
  · exact ⟨.inr (.inl ()),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  · exact ⟨.inr (.inr r),hr⟩
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end OAI
