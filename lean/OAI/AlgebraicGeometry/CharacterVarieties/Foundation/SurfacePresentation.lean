import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.Incidence

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression

/-- The finite oriented boundary cycles contain each side occurrence exactly once. Their successor is the one constructed from the allowed vertices. No cycle is discarded if a facet or a seam appears repeatedly. -/
structure Diagram (F S V : Type) (arity : S → ℕ) where
  ports : PortAssembly F S V arity
  rank : F → ℕ
  seamRank : ∀ s, rank (ports.facet ⟨s,none⟩)=∑ j, rank (ports.facet ⟨s,some j⟩)
  genus : F → ℕ
  boundaryCount : F → ℕ
  boundaryLength : (f : F) → Fin (boundaryCount f) → ℕ
  boundaryPositive : ∀ f b, 0 < boundaryLength f b
  boundarySide : ((f : F) × (b : Fin (boundaryCount f)) × Fin (boundaryLength f b)) ≃ Side S arity
  boundaryFacet : ∀ f b i, ports.facet (boundarySide ⟨f,b,i⟩)=f
  boundaryNext : ∀ f b i, ports.vertexAssembly.corners.boundaryNext (boundarySide ⟨f,b,i⟩)=
    boundarySide ⟨f,b,⟨(i.val+1) % boundaryLength f b,Nat.mod_lt _ (boundaryPositive f b)⟩⟩

namespace Diagram
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

def seamDim (s : S) : ℕ := ∑ j, D.rank (D.ports.facet ⟨s,some j⟩)
def childDim (s : S) (j : Fin (arity s)) : ℕ := D.rank (D.ports.facet ⟨s,some j⟩)

/-- Every frame and every transport has its own occurrence index. Handle generators are retained even on closed or multiply incident facets. -/
inductive Generator where
  | side (a : Side S arity)
  | frame (s : S) (endpoint : Bool)
  | handle (f : F) (k : Fin (D.genus f)) (which : Bool)

def generatorRank : D.Generator → ℕ
  | .side a => D.rank (D.ports.facet a)
  | .frame s _ => D.seamDim s
  | .handle f _ _ => D.rank f

instance finiteGenerator [Finite F] [Finite S] : Finite D.Generator := by
  let E := Side S arity ⊕ ((S × Bool) ⊕ ((f : F) × Fin (D.genus f) × Bool))
  let e : E ≃ D.Generator :=
    { toFun := fun x => match x with
        | .inl a => .side a
        | .inr (.inl (s,b)) => .frame s b
        | .inr (.inr ⟨f,k,b⟩) => .handle f k b
      invFun := fun x => match x with
        | .side a => .inl a
        | .frame s b => .inr (.inl (s,b))
        | .handle f k b => .inr (.inr ⟨f,k,b⟩)
      left_inv := by rintro (a|⟨s,b⟩|⟨f,k,b⟩) <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  exact Finite.of_equiv E e

variable (R : Type*) [CommRing R]
abbrev Word (n : ℕ) := Term R D.Generator D.generatorRank n

/-- Scalar punctures, as prescribed full-ring units. Quasi-unipotence will be imposed at the density stage; the representing scheme itself needs only units. -/
structure Punctures (D : Diagram F S V arity) (R : Type*) [CommRing R] where
  count : F → ℕ
  scalar : (f : F) → Fin (count f) → Rˣ

variable {R}
def frameWord (s : S) (b : Bool) : D.Word R (D.seamDim s) := .generator (Generator.frame (D:=D) s b)
def sideWord (a : Side S arity) : D.Word R (D.rank (D.ports.facet a)) := .generator (Generator.side (D:=D) a)

def parentWord (s : S) : D.Word R (D.seamDim s) := cast (congrArg (D.Word R) (D.seamRank s)) (D.sideWord (R:=R) ⟨s,none⟩)
def childWord (s : S) (j : Fin (arity s)) : D.Word R (D.childDim s j) := D.sideWord ⟨s,some j⟩

def wordProduct {n : ℕ} (L : List (D.Word R n)) : D.Word R n :=
  L.foldr Term.mul (.constant 1)

def commutatorWord (f : F) (k : Fin (D.genus f)) : D.Word R (D.rank f) :=
  let a : D.Word R (D.rank f) := .generator (Generator.handle (D:=D) f k false)
  let b : D.Word R (D.rank f) := .generator (Generator.handle (D:=D) f k true)
  .mul (.mul (.mul a b) (.inv a)) (.inv b)

def boundaryEdgeWord (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    D.Word R (D.rank f) :=
  congrArg D.rank (D.boundaryFacet f b i) ▸ D.sideWord (D.boundarySide ⟨f,b,i⟩)

/-- Matrix transport reads a positive boundary path from right to left. -/
def boundaryWord (f : F) (b : Fin (D.boundaryCount f)) : D.Word R (D.rank f) :=
  D.wordProduct ((List.ofFn (D.boundaryEdgeWord (R:=R) f b)).reverse)

def surfaceWord (f : F) : D.Word R (D.rank f) :=
  .mul (D.wordProduct (List.ofFn (D.commutatorWord (R:=R) f)))
    (D.wordProduct (List.ofFn (D.boundaryWord (R:=R) f)))

def scalarUnit (n : ℕ) (u : Rˣ) : (Matrix (Fin n) (Fin n) R)ˣ :=
  Units.map (algebraMap R (Matrix (Fin n) (Fin n) R)).toMonoidHom u

def surfaceTarget (P : D.Punctures R) (f : F) : D.Word R (D.rank f) :=
  .constant (scalarUnit (D.rank f) (∏ j, P.scalar f j)⁻¹)

/-- Seam-parallel transport from false to true uses the inverse CHILD transport, since each child's boundary orientation is opposite to the parent's. -/
def seamLeft (s : S) : D.Word R (D.seamDim s) := .mul (D.parentWord s) (D.frameWord s false)
def seamRight (s : S) : D.Word R (D.seamDim s) :=
  .mul (D.frameWord s true) (.block (D.childDim s) (fun j => .inv (D.childWord s j)))

/-- Ordered flag grade for the direct sum of the child fibers. -/
def seamGrade (s : S) (i : Fin (D.seamDim s)) : ℕ := ((blockIndex (D.childDim s)) i).1.val

/-- The surface and regular seam part of the diagram equations. -/
def edgeCircuit (P : D.Punctures R) : FlagCircuit.Data R D.Generator D.generatorRank (F ⊕ S) where
  dim := Sum.elim D.rank D.seamDim
  grade := fun j => match j with | .inl _ => fun _ => 0 | .inr s => D.seamGrade s
  left := fun j => match j with | .inl f => D.surfaceWord f | .inr s => D.seamLeft s
  right := fun j => match j with | .inl f => D.surfaceTarget P f | .inr s => D.seamRight s

/-- The finite matrix presentation of this portion of the local-system scheme, including inverses and all oriented boundary/facet equations. -/
abbrev EdgeCoordinate (P : D.Punctures R) := (D.edgeCircuit P).Coordinate

variable {A : Type*} [CommRing A] [Algebra R A]

def edgePointsEquiv (P : D.Punctures R) :
    (D.edgeCircuit P).Solution A ≃ (D.EdgeCoordinate P →ₐ[R] A) :=
  (D.edgeCircuit P).pointsEquiv

end Diagram
end IntegralCharacterVarieties.SurfacePresentation

namespace IntegralCharacterVarieties
open scoped Classical Matrix

/-- A genuinely invertible rectangular coordinate matrix; source and target fiber labels can differ, even if both occur on a single facet. -/
structure MatrixIso (R : Type*) [CommRing R] (α β : Type*) [Fintype α] [Fintype β] where
  val : Matrix β α R
  inv : Matrix α β R
  val_inv : val*inv=1
  inv_val : inv*val=1

namespace MatrixIso
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def linearEquiv (x : MatrixIso R α β) : (α → R) ≃ₗ[R] (β → R) where
  toLinearMap := Matrix.toLin' x.val
  invFun := fun v => x.inv *ᵥ v
  left_inv v := by change x.inv *ᵥ (x.val *ᵥ v)=v; rw [Matrix.mulVec_mulVec,x.inv_val,Matrix.one_mulVec]
  right_inv v := by change x.val *ᵥ (x.inv *ᵥ v)=v; rw [Matrix.mulVec_mulVec,x.val_inv,Matrix.one_mulVec]

def refl : MatrixIso R α α := ⟨1,1,one_mul _,one_mul _⟩
def symm (x : MatrixIso R α β) : MatrixIso R β α := ⟨x.inv,x.val,x.inv_val,x.val_inv⟩
def trans (x : MatrixIso R α β) (y : MatrixIso R β γ) : MatrixIso R α γ where
  val := y.val*x.val
  inv := x.inv*y.inv
  val_inv := by rw [Matrix.mul_assoc,← Matrix.mul_assoc x.val,x.val_inv,Matrix.one_mul,y.val_inv]
  inv_val := by rw [Matrix.mul_assoc,← Matrix.mul_assoc y.inv,y.inv_val,Matrix.one_mul,x.inv_val]

def unit [DecidableEq α] (x : (Matrix α α R)ˣ) : MatrixIso R α α where
  val := x.val
  inv := x.inv
  val_inv := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  inv_val := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.one_apply,h]

def reindex {α' β' : Type*} [Fintype α'] [Fintype β']
    (x : MatrixIso R α β) (a : α' ≃ α) (b : β' ≃ β) : MatrixIso R α' β' where
  val := x.val.submatrix b a
  inv := x.inv.submatrix a b
  val_inv := by rw [Matrix.submatrix_mul_equiv,x.val_inv]; exact Matrix.submatrix_one_equiv _
  inv_val := by rw [Matrix.submatrix_mul_equiv,x.inv_val]; exact Matrix.submatrix_one_equiv _

def congr (e : α ≃ β) : MatrixIso R α β := reindex (refl (R:=R) (α:=β)) e (Equiv.refl _)

def block {ι : Type*} [Fintype ι] {a b : ι → Type*} [∀ i, Fintype (a i)] [∀ i, Fintype (b i)]
    (f : ∀ i, MatrixIso R (a i) (b i)) : MatrixIso R ((i : ι) × a i) ((i : ι) × b i) where
  val := Matrix.blockDiagonal' (fun i => (f i).val)
  inv := Matrix.blockDiagonal' (fun i => (f i).inv)
  val_inv := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [val_inv]
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases h : i=k
    · subst k; simp [Matrix.blockDiagonal',Matrix.one_apply]
    · simp [Matrix.blockDiagonal',Matrix.one_apply,h]
  inv_val := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [inv_val]
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases h : i=k
    · subst k; simp [Matrix.blockDiagonal',Matrix.one_apply]
    · simp [Matrix.blockDiagonal',Matrix.one_apply,h]

def sum {α' β' : Type*} [Fintype α'] [Fintype β']
    (x : MatrixIso R α β) (y : MatrixIso R α' β') : MatrixIso R (α ⊕ α') (β ⊕ β') where
  val := Matrix.fromBlocks x.val 0 0 y.val
  inv := Matrix.fromBlocks x.inv 0 0 y.inv
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,x.val_inv,y.val_inv]
    ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,x.inv_val,y.inv_val]
    ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]

def map {S : Type*} [CommRing S] (φ : R →+* S) (x : MatrixIso R α β) : MatrixIso S α β where
  val := x.val.map φ
  inv := x.inv.map φ
  val_inv := by rw [← Matrix.map_mul,x.val_inv]; exact Matrix.map_one φ (map_zero φ) (map_one φ)
  inv_val := by rw [← Matrix.map_mul,x.inv_val]; exact Matrix.map_one φ (map_zero φ) (map_one φ)

/-- Identified-flag equality, in matrix coordinates without equating or forgetting any of its named fibers. -/
theorem sameFramedFlag_iff (a : α → ℕ) (x y : MatrixIso R α β) :
    SameFramedFlag a x.linearEquiv y.linearEquiv ↔
      ∀ i j, a j ≤ a i → (y.inv*x.val) i j=(1 : Matrix α α R) i j := by
  rw [IntegralCharacterVarieties.sameFramedFlag_iff,sameCoordinateFlag_iff_lowering]
  have hM := filteredMatrixStabilizer_iff a a (y.inv*x.val-1)
  have hact : ∀ v : α → R,
      (y.inv*x.val-1) *ᵥ v=(x.linearEquiv.trans y.linearEquiv.symm) v-v := by
    intro v
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    congr 1
    exact (Matrix.mulVec_mulVec _ _ _).symm
  simp only [hact] at hM
  rw [← hM]
  change (∀ i j, a j ≤ a i → (y.inv*x.val) i j-(1 : Matrix α α R) i j=0) ↔ _
  simp only [sub_eq_zero]

end MatrixIso
end IntegralCharacterVarieties

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
namespace VertexTable
instance fintypePort (k : Kind) : Fintype k.table.Port := Fintype.ofFinite _
instance fintypeChild (k : Kind) (p : k.table.Port) : Fintype (k.table.Child p) := Fintype.ofFinite _

/-- Ranks are attached to local occurrences. Their only identification is the corner pairing from the source vertex table. -/
structure LocalRanks (k : Kind) where
  rank : (p : k.table.Port) → Option (k.table.Child p) → ℕ
  corner : ∀ x, rank (k.table.mate x).1 (k.table.mate x).2=rank x.1 x.2
  sum : ∀ p, rank p none=∑ c, rank p (some c)

namespace LocalRanks
variable {k : Kind} (d : LocalRanks k)
abbrev Parent (p : k.table.Port) := Fin (d.rank p none)
abbrev Child (p : k.table.Port) (c : k.table.Child p) := Fin (d.rank p (some c))
abbrev Columns (p : k.table.Port) := (c : k.table.Child p) × d.Child p c
instance fintypeColumns (p : k.table.Port) : Fintype (d.Columns p) :=
  inferInstanceAs (Fintype ((c : k.table.Child p) × Fin (d.rank p (some c))))


def cornerEquiv (x : (p : k.table.Port) × Option (k.table.Child p)) :
    Fin (d.rank x.1 x.2) ≃ Fin (d.rank (k.table.mate x).1 (k.table.mate x).2) :=
  finCongr (d.corner x).symm
end LocalRanks
end VertexTable
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.SurfacePresentation
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
namespace Diagram
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

/-- Each local port remembers its entire parent/child list at that precise endpoint. Facet labels may repeat without identifying any side coordinates. -/
def portSide (p : LocalPort V D.ports.kind) (c : Option ((D.ports.kind p.1).table.Child p.2)) : Side S arity :=
  ⟨(D.ports.attach p).1,c.map (D.ports.childEquiv p)⟩

lemma portSide_eq (x : LocalEnd V D.ports.kind) :
    D.portSide ⟨x.1,x.2.1⟩ x.2.2=(D.ports.realize x).1 := rfl

lemma portFacet_corner (x : LocalEnd V D.ports.kind) :
    D.ports.facet (D.portSide ⟨(localMate x).1,(localMate x).2.1⟩ (localMate x).2.2)=
      D.ports.facet (D.portSide ⟨x.1,x.2.1⟩ x.2.2) :=
  D.ports.vertexAssembly.facetContinuation x

/-- Local vertex ranks are derived from the diagram, NOT additional rank hypotheses that might exclude one of its solutions. -/
def vertexRanks (v : V) : VertexTable.LocalRanks (D.ports.kind v) where
  rank p c := D.rank (D.ports.facet (D.portSide ⟨v,p⟩ c))
  corner x := congrArg D.rank (D.portFacet_corner ⟨v,x⟩)
  sum p := by
    change D.rank (D.ports.facet ⟨(D.ports.attach ⟨v,p⟩).1,none⟩)=_
    rw [D.seamRank]
    exact (Equiv.sum_comp (D.ports.childEquiv ⟨v,p⟩)
      (fun i => D.rank (D.ports.facet ⟨(D.ports.attach ⟨v,p⟩).1,some i⟩))).symm

def portColumnIndex (p : LocalPort V D.ports.kind) :
    (D.vertexRanks p.1).Columns p.2 ≃ Fin (D.seamDim (D.ports.attach p).1) :=
  (Equiv.sigmaCongr (D.ports.childEquiv p) (fun _ => Equiv.refl _)).trans
    (blockIndex (D.childDim (D.ports.attach p).1)).symm

def portRowIndex (p : LocalPort V D.ports.kind) :
    (D.vertexRanks p.1).Parent p.2 ≃ Fin (D.seamDim (D.ports.attach p).1) :=
  finCongr (D.seamRank (D.ports.attach p).1)

variable {R : Type*} [CommRing R]

/-- The rectangular seam frame. Both child and parent bases come from named occurrences; all reindexings are fixed by the source incidence data. -/
def portFrame (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (p : LocalPort V D.ports.kind) :
    MatrixIso R ((D.vertexRanks p.1).Columns p.2) ((D.vertexRanks p.1).Parent p.2) :=
  (MatrixIso.unit (g (.frame (D.ports.attach p).1 (D.ports.attach p).2))).reindex
    (D.portColumnIndex p) (D.portRowIndex p)

end Diagram
end IntegralCharacterVarieties.SurfacePresentation

namespace IntegralCharacterVarieties
open scoped Classical Matrix

/-- One comparison of flags carrying their named graded fibers. -/
structure FlagComparison (R : Type*) [CommRing R] where
  Source : Type
  Target : Type
  sourceFinite : Fintype Source
  targetFinite : Fintype Target
  grade : Source → ℕ
  left : @MatrixIso R _ Source Target sourceFinite targetFinite
  right : @MatrixIso R _ Source Target sourceFinite targetFinite
attribute [instance] FlagComparison.sourceFinite FlagComparison.targetFinite

namespace FlagComparison
variable {R : Type*} [CommRing R] (c : FlagComparison R)
abbrev Entry := {ij : c.Source × c.Source // c.grade ij.2 ≤ c.grade ij.1}
def equation (ij : c.Entry) : R := (c.right.inv*c.left.val) ij.1.1 ij.1.2-(1 : Matrix c.Source c.Source R) ij.1.1 ij.1.2
def Holds : Prop := SameFramedFlag c.grade c.left.linearEquiv c.right.linearEquiv

theorem holds_iff_equations : c.Holds ↔ ∀ ij, c.equation ij=0 := by
  rw [Holds,MatrixIso.sameFramedFlag_iff]
  constructor
  · intro h ⟨⟨i,j⟩,hij⟩
    exact sub_eq_zero.mpr (h i j hij)
  · intro h i j hij
    exact sub_eq_zero.mp (h ⟨(i,j),hij⟩)
end FlagComparison

namespace OccurrenceIncidence.VertexTable
namespace LocalRanks
variable {R : Type*} [CommRing R]

/-- Fine list positions, with exactly the prescribed pair merged for an adjacent interchange. This retains the entire A⊕B identified quotient. -/
def passageGrade {m : ℕ} (t : Passage m) (j : Fin m) : ℕ :=
  match t with
  | .continuation => j.val
  | .interchange i => if j.val=i.val+1 then i.val else j.val

def passageColumns {m : ℕ} {t : Passage m} (d : LocalRanks (.passage m t)) :
    d.Columns false ≃ d.Columns true :=
  Equiv.sigmaCongr t.permutation (fun j => finCongr (by
    exact (d.corner ⟨false,some j⟩).symm))

def passageParent {m : ℕ} {t : Passage m} (d : LocalRanks (.passage m t)) :
    d.Parent false ≃ d.Parent true :=
  finCongr (by
    exact (d.corner ⟨false,none⟩).symm)

def passageComparison {m : ℕ} {t : Passage m} (d : LocalRanks (.passage m t))
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p)) : FlagComparison R := by
  let : Fintype (d.Columns false) := d.fintypeColumns false
  let : Fintype (d.Columns true) := d.fintypeColumns true
  exact {
    Source := d.Columns false
    Target := d.Parent false
    sourceFinite := inferInstance
    targetFinite := inferInstance
    grade := fun j => passageGrade t j.1
    left := f false
    right := (f true).reindex d.passageColumns d.passageParent }

variable {a b c : ℕ}
/-- Reversal changes germ endpoint directions, not any fiber/refinement data. -/
def forwardRanks (d : LocalRanks (.splitting a b c true)) : LocalRanks (.splitting a b c false) :=
  ⟨d.rank,d.corner,d.sum⟩

def prefixRank (d : LocalRanks (.splitting a b c false)) : Bool → Fin a → ℕ
  | false,i => d.rank .before (some (.inl i))
  | true,i => d.rank .after (some (.inl i))
def suffixRank (d : LocalRanks (.splitting a b c false)) : Bool → Fin c → ℕ
  | false,i => d.rank .before (some (.inr (.inr i)))
  | true,i => d.rank .after (some (.inr (.inr i)))
abbrev SplitA (d : LocalRanks (.splitting a b c false)) (p : Bool) :=
  (i : Fin a) × Fin (d.prefixRank p i)
abbrev SplitC (d : LocalRanks (.splitting a b c false)) (p : Bool) :=
  (i : Fin c) × Fin (d.suffixRank p i)
abbrev SplitB (d : LocalRanks (.splitting a b c false)) :=
  (i : Fin b) × Fin (d.rank .after (some (.inr (.inl i))))
abbrev SplitW (d : LocalRanks (.splitting a b c false)) :=
  Fin (d.rank .before (some (.inr (.inl ()))))

/-- Ordered source decomposition of before and after lists. -/
def splitBefore (d : LocalRanks (.splitting a b c false)) :
    d.Columns .before ≃ (d.SplitA false ⊕ (d.SplitW ⊕ d.SplitC false)) where
  toFun | ⟨.inl i,j⟩ => .inl ⟨i,j⟩
        | ⟨.inr (.inl ()),j⟩ => .inr (.inl j)
        | ⟨.inr (.inr i),j⟩ => .inr (.inr ⟨i,j⟩)
  invFun | .inl ⟨i,j⟩ => ⟨.inl i,j⟩
         | .inr (.inl j) => ⟨.inr (.inl ()),j⟩
         | .inr (.inr ⟨i,j⟩) => ⟨.inr (.inr i),j⟩
  left_inv := by
    rintro ⟨i,j⟩
    rcases i with i|u|i
    · rfl
    · cases u; rfl
    · rfl
  right_inv := by rintro (⟨i,j⟩|j|⟨i,j⟩) <;> rfl

def splitAfter (d : LocalRanks (.splitting a b c false)) :
    d.Columns .after ≃ (d.SplitA true ⊕ (d.SplitB ⊕ d.SplitC true)) where
  toFun | ⟨.inl i,j⟩ => .inl ⟨i,j⟩
        | ⟨.inr (.inl i),j⟩ => .inr (.inl ⟨i,j⟩)
        | ⟨.inr (.inr i),j⟩ => .inr (.inr ⟨i,j⟩)
  invFun | .inl ⟨i,j⟩ => ⟨.inl i,j⟩
         | .inr (.inl ⟨i,j⟩) => ⟨.inr (.inl i),j⟩
         | .inr (.inr ⟨i,j⟩) => ⟨.inr (.inr i),j⟩
  left_inv := by rintro ⟨i,j⟩; rcases i with i|i|i <;> rfl
  right_inv := by rintro (⟨i,j⟩|⟨i,j⟩|⟨i,j⟩) <;> rfl

def splitPrefix (d : LocalRanks (.splitting a b c false)) : d.SplitA true ≃ d.SplitA false :=
  Equiv.sigmaCongrRight (fun i => finCongr (d.corner ⟨.after,some (.inl i)⟩).symm)
def splitSuffix (d : LocalRanks (.splitting a b c false)) : d.SplitC true ≃ d.SplitC false :=
  Equiv.sigmaCongrRight (fun i => finCongr (d.corner ⟨.after,some (.inr (.inr i))⟩).symm)
def splitBranchChildren (d : LocalRanks (.splitting a b c false)) : d.SplitB ≃ d.Columns .branch :=
  Equiv.sigmaCongrRight (fun i => finCongr (d.corner ⟨.after,some (.inr (.inl i))⟩).symm)
def splitBranchParent (d : LocalRanks (.splitting a b c false)) : d.SplitW ≃ d.Parent .branch :=
  finCongr (d.corner ⟨.before,some (.inr (.inl ()))⟩).symm
def splitParent (d : LocalRanks (.splitting a b c false)) : d.Parent .after ≃ d.Parent .before :=
  finCongr (d.corner ⟨.after,none⟩).symm

/-- Refinement: leave every old prefix/suffix fiber unchanged, and in exactly the old W-block insert its named third-seam frame. -/
def splitRefinement (d : LocalRanks (.splitting a b c false))
    (w : @MatrixIso R _ (d.Columns .branch) (d.Parent .branch) (d.fintypeColumns .branch) inferInstance) :
    @MatrixIso R _ (d.Columns .after) (d.Columns .before) (d.fintypeColumns .after) (d.fintypeColumns .before) := by
  let : Fintype (d.Columns .after) := d.fintypeColumns .after
  let : Fintype (d.Columns .before) := d.fintypeColumns .before
  let : Fintype (d.Columns .branch) := d.fintypeColumns .branch
  exact ((MatrixIso.congr d.splitPrefix).sum
    ((w.reindex d.splitBranchChildren d.splitBranchParent).sum
      (MatrixIso.congr d.splitSuffix))).reindex d.splitAfter d.splitBefore

def splitComparison (d : LocalRanks (.splitting a b c false))
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p)) : FlagComparison R := by
  let : Fintype (d.Columns .after) := d.fintypeColumns .after
  let : Fintype (d.Columns .before) := d.fintypeColumns .before
  let : Fintype (d.Columns .branch) := d.fintypeColumns .branch
  exact {
    Source := d.Columns .after
    Target := d.Parent .after
    sourceFinite := inferInstance
    targetFinite := inferInstance
    grade := fun j => ((Kind.splitting a b c false).childEnumeration .after j.1).val
    left := f .after
    right := ((d.splitRefinement (f .branch)).trans (f .before)).reindex (Equiv.refl _) d.splitParent }

/-- All and only the permitted source vertex comparisons, including complement and quotient maps at a swap, and reverse refinement at a merge. -/
def comparison : (k : Kind) → (d : LocalRanks k) →
    (∀ p, MatrixIso R (d.Columns p) (d.Parent p)) → FlagComparison R
  | .passage _ _,d,f => d.passageComparison f
  | .splitting _ _ _ false,d,f => d.splitComparison f
  | .splitting _ _ _ true,d,f => d.forwardRanks.splitComparison f

end LocalRanks
end OccurrenceIncidence.VertexTable
end IntegralCharacterVarieties
namespace IntegralCharacterVarieties
open scoped Classical Matrix
namespace MatrixIso
variable {R S : Type*} [CommRing R] [CommRing S]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext (x y : MatrixIso R α β) (hv : x.val=y.val) (hi : x.inv=y.inv) : x=y := by
  cases x; cases y; cases hv; cases hi; rfl

@[simp] lemma map_refl (φ : R →+* S) : map φ (refl (R:=R) (α:=α))=refl := by
  apply ext <;> exact Matrix.map_one φ (map_zero φ) (map_one φ)

@[simp] lemma map_trans (φ : R →+* S) (x : MatrixIso R α β) (y : MatrixIso R β γ) :
    map φ (x.trans y)=(map φ x).trans (map φ y) := by
  apply ext <;> exact Matrix.map_mul

@[simp] lemma map_reindex {α' β' : Type*} [Fintype α'] [Fintype β']
    (φ : R →+* S) (x : MatrixIso R α β) (a : α' ≃ α) (b : β' ≃ β) :
    map φ (x.reindex a b)=(map φ x).reindex a b := rfl

@[simp] lemma map_congr (φ : R →+* S) (e : α ≃ β) :
    map φ (congr e)=congr e := by simp only [congr,map_reindex,map_refl]

@[simp] lemma map_sum {α' β' : Type*} [Fintype α'] [Fintype β']
    (φ : R →+* S) (x : MatrixIso R α β) (y : MatrixIso R α' β') :
    map φ (x.sum y)=(map φ x).sum (map φ y) := by
  apply ext <;> ext i j <;> cases i <;> cases j <;> simp [map,sum,Matrix.fromBlocks]

@[simp] lemma map_unit {n : ℕ} (φ : R →+* S) (x : (Matrix (Fin n) (Fin n) R)ˣ) :
    map φ (unit x)=unit (MatrixExpression.mapUnit φ x) := rfl
end MatrixIso

namespace FlagComparison
variable {R S : Type*} [CommRing R] [CommRing S]
def map (φ : R →+* S) (c : FlagComparison R) : FlagComparison S where
  Source := c.Source
  Target := c.Target
  sourceFinite := c.sourceFinite
  targetFinite := c.targetFinite
  grade := c.grade
  left := c.left.map φ
  right := c.right.map φ

@[simp] theorem equation_map (φ : R →+* S) (c : FlagComparison R) (ij : c.Entry) :
    (c.map φ).equation ij=φ (c.equation ij) := by
  change ((c.right.inv.map φ)*(c.left.val.map φ)) ij.1.1 ij.1.2 -
    (1 : Matrix c.Source c.Source S) ij.1.1 ij.1.2=φ _
  rw [← Matrix.map_mul]
  change φ ((c.right.inv*c.left.val) ij.1.1 ij.1.2)-(1 : Matrix c.Source c.Source S) ij.1.1 ij.1.2=
    φ ((c.right.inv*c.left.val) ij.1.1 ij.1.2-(1 : Matrix c.Source c.Source R) ij.1.1 ij.1.2)
  rw [map_sub]
  congr 1
  exact congrFun (congrFun (Matrix.map_one φ (map_zero φ) (map_one φ)).symm ij.1.1) ij.1.2
end FlagComparison

namespace OccurrenceIncidence.VertexTable.LocalRanks
variable {R S : Type*} [CommRing R] [CommRing S]
variable {k : Kind} (d : LocalRanks k)

theorem splitComparison_map {a b c : ℕ} (d : LocalRanks (.splitting a b c false)) (φ : R →+* S)
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p)) :
    d.splitComparison (fun p => (f p).map φ)=(d.splitComparison f).map φ := by
  let : Fintype (d.Columns .after) := d.fintypeColumns .after
  let : Fintype (d.Columns .before) := d.fintypeColumns .before
  let : Fintype (d.Columns .branch) := d.fintypeColumns .branch
  dsimp only [splitComparison,FlagComparison.map,splitRefinement]
  congr 1
  rw [MatrixIso.map_reindex,MatrixIso.map_trans,MatrixIso.map_reindex,
    MatrixIso.map_sum,MatrixIso.map_congr,MatrixIso.map_sum,
    MatrixIso.map_reindex,MatrixIso.map_congr]

@[simp] theorem comparison_map (φ : R →+* S)
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p)) :
    comparison k d (fun p => (f p).map φ)=(comparison k d f).map φ := by
  cases k with
  | passage m t => rfl
  | splitting a b c r =>
    cases r with
    | false => exact splitComparison_map d φ f
    | true => exact splitComparison_map d.forwardRanks φ f
end OccurrenceIncidence.VertexTable.LocalRanks

namespace SurfacePresentation.Diagram
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
variable {R A : Type*} [CommRing R] [CommRing A]

@[simp] theorem portFrame_map (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (p : LocalPort V D.ports.kind) :
    D.portFrame (fun e => MatrixExpression.mapUnit φ (g e)) p=(D.portFrame g p).map φ := by
  rfl

/-- Comparison at this vertex, with the occurrence transports already expressed in the shared facet frames. -/
def vertexComparison
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (v : V) : FlagComparison R :=
  VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
    (fun p => D.portFrame g ⟨v,p⟩)

@[simp] theorem vertexComparison_map (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (v : V) :
    D.vertexComparison (fun e => MatrixExpression.mapUnit φ (g e)) v=(D.vertexComparison g v).map φ := by
  simp only [vertexComparison,portFrame_map,VertexTable.LocalRanks.comparison_map]
end SurfacePresentation.Diagram
end IntegralCharacterVarieties
namespace IntegralCharacterVarieties.EquationQuotient
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
variable {J : Type*} (e : J → B)
def ideal : Ideal B := Ideal.span (Set.range e)
abbrev Coordinate := B ⧸ ideal e

lemma ideal_le_ker (φ : B →ₐ[R] A) (h : ∀ j, φ (e j)=0) :
    ideal e ≤ RingHom.ker φ.toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨j,rfl⟩
  exact h j

/-- Exact equation quotient over any full coefficient ring. -/
def pointsEquiv : {φ : B →ₐ[R] A // ∀ j, φ (e j)=0} ≃ (Coordinate e →ₐ[R] A) where
  toFun φ := Ideal.Quotient.liftₐ (ideal e) φ.val (ideal_le_ker e φ.val φ.property)
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mkₐ R (ideal e)),by
    intro j
    change ψ (Ideal.Quotient.mk (ideal e) (e j))=0
    have hz : Ideal.Quotient.mk (ideal e) (e j)=0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_range_self j))
    rw [hz,map_zero]⟩
  left_inv φ := by
    apply Subtype.ext
    ext b
    rfl
  right_inv ψ := by
    apply Ideal.Quotient.algHom_ext
    ext b
    rfl
end IntegralCharacterVarieties.EquationQuotient
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (P : D.Punctures R)

def universalEdge (e : D.Generator) :
    (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) (D.EdgeCoordinate P))ˣ :=
  FiniteMatrixPresentation.universalUnit (D.edgeCircuit P).equation e

abbrev VertexEntry := (v : V) × (D.vertexComparison (D.universalEdge P) v).Entry

def vertexEquation (j : D.VertexEntry P) : D.EdgeCoordinate P :=
  (D.vertexComparison (D.universalEdge P) j.1).equation j.2

/-- All permitted vertex conditions on the matrix system. -/
def VertexHolds
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) : Prop :=
  ∀ v, (D.vertexComparison g v).Holds

/-- The finite coordinate algebra, retaining all surface relations, all regular seam identifications and all vertex refinements/complements. -/
abbrev Coordinate := EquationQuotient.Coordinate (D.vertexEquation P)

/-- The split-frame solution functor of the incidence diagram. -/
abbrev Solution (A : Type*) [CommRing A] [Algebra R A] :=
  {g : (D.edgeCircuit P).Solution A // D.VertexHolds g.val}

/-- Specialization of the universal vertex equations is precisely the stated geometric vertex condition, including the natural maps at a swap. -/
theorem vertex_equations_iff (φ : D.EdgeCoordinate P →ₐ[R] A) :
    (∀ j, φ (D.vertexEquation P j)=0) ↔
      D.VertexHolds ((D.edgePointsEquiv P).symm φ).val := by
  have hv (v : V) :
      D.vertexComparison ((D.edgePointsEquiv P).symm φ).val v =
        (D.vertexComparison (D.universalEdge P) v).map φ.toRingHom := by
    change D.vertexComparison (fun e => MatrixExpression.mapUnit φ.toRingHom (D.universalEdge P e)) v=_
    exact D.vertexComparison_map φ.toRingHom (D.universalEdge P) v
  constructor
  · intro h v
    rw [hv,FlagComparison.holds_iff_equations]
    intro ij
    exact (FlagComparison.equation_map φ.toRingHom (D.vertexComparison (D.universalEdge P) v) ij).trans
      (h ⟨v,ij⟩)
  · intro h ⟨v,ij⟩
    have hh := h v
    rw [hv,FlagComparison.holds_iff_equations] at hh
    change φ ((D.vertexComparison (D.universalEdge P) v).equation ij)=0
    exact (FlagComparison.equation_map φ.toRingHom (D.vertexComparison (D.universalEdge P) v) ij).symm.trans
      (hh ij)

/-- The equivalence works over an arbitrary commutative algebra, in particular the full ring of integers, and retains forward AND inverse entries. -/
def pointsEquiv : D.Solution P A ≃ (D.Coordinate P →ₐ[R] A) :=
  (Equiv.subtypeEquiv (D.edgePointsEquiv P) (fun g => by
    simpa only [Equiv.symm_apply_apply] using
      (D.vertex_equations_iff P (D.edgePointsEquiv P g)).symm)).trans
    (EquationQuotient.pointsEquiv (D.vertexEquation P))

instance finiteVertexEntry [Finite V] : Finite (D.VertexEntry P) := inferInstance
instance finiteType [Finite F] [Finite S] : Algebra.FiniteType R (D.Coordinate P) := inferInstance

end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
