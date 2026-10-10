import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryReordering

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)
variable (G : D.CornerBases (R:=A))
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

@[simp] lemma cornerBasis_start (a : Side S arity) : D.cornerBasis G (start a)=G a := by
  have h := MatrixIso.finite_basis_transport (fun a : Side S arity => D.rank (D.ports.facet a)) G
    a (D.sourceCorner (start a)) (D.rank (D.ports.facet a)) (D.rank (D.ports.facet a))
    rfl (congrArg D.rank (D.sourceCorner_facet (start a))).symm
    (D.sourceCorner_start a).symm rfl
  unfold cornerBasis
  erw [MatrixIso.reindex_refl_eq] at h
  simp only [finCongr_refl,MatrixIso.reindex_refl_eq] at h
  convert! h using 1

def boundaryCornerBasis (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) : MatrixIso A (Fin (D.rank f)) (Fin (D.rank f)) :=
  (G (D.boundarySide ⟨f,b,i⟩)).reindex
    (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)
    (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)

lemma cornerFinish_boundary (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.cornerBasis G (finish (D.boundarySide ⟨f,b,i⟩))).reindex
      (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)
      (finCongr (congrArg D.rank (D.boundaryFacet f b i)).symm)=
      D.boundaryCornerBasis G f b ⟨(i.val+1)%D.boundaryLength f b,Nat.mod_lt _ (D.boundaryPositive f b)⟩ := by
  exact MatrixIso.finite_basis_transport (fun a : Side S arity => D.rank (D.ports.facet a)) G
    _ _ _ _ _ _ ((D.boundaryNext f b i).symm.trans
      (D.sourceCorner_finish (D.boundarySide ⟨f,b,i⟩)).symm) _

lemma boundaryEdge_cornerGauge (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.boundaryEdgeWord f b i).eval φ (D.cornerGaugeGenerators G g)=
      (D.boundaryCornerBasis G f b ⟨(i.val+1)%D.boundaryLength f b,Nat.mod_lt _ (D.boundaryPositive f b)⟩).toUnit*
        (D.boundaryEdgeWord f b i).eval φ g*(D.boundaryCornerBasis G f b i).toUnit⁻¹ := by
  have h := D.boundaryEdge_iso φ (D.cornerGaugeGenerators G g) f b i
  rw [show MatrixIso.unit ((D.cornerGaugeGenerators G g) (.side (D.boundarySide ⟨f,b,i⟩)))=
      (((D.cornerBasis G (start (D.boundarySide ⟨f,b,i⟩))).symm.trans
        (MatrixIso.unit (g (.side (D.boundarySide ⟨f,b,i⟩))))).trans
        (D.cornerBasis G (finish (D.boundarySide ⟨f,b,i⟩)))) by
          unfold cornerGaugeGenerators
          erw [MatrixIso.unit_toUnit]] at h
  erw [MatrixIso.bases_reindex,D.cornerFinish_boundary,← D.boundaryEdge_iso φ g] at h
  simp only [D.cornerBasis_start] at h
  apply Units.ext
  have hh := congrArg MatrixIso.val h
  change _=(D.boundaryCornerBasis G f b ⟨(i.val+1)%D.boundaryLength f b,Nat.mod_lt _ (D.boundaryPositive f b)⟩).val*
    (((D.boundaryEdgeWord f b i).eval φ g) : Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)*
      (D.boundaryCornerBasis G f b i).inv
  simp only [boundaryCornerBasis,MatrixIso.unit,MatrixIso.trans,MatrixIso.symm,
    Matrix.mul_assoc] at hh ⊢
  convert! hh using 1

/-- Based boundary holonomy telescopes at every interior corner; only the independent chosen base
corner remains. -/
lemma boundaryWord_cornerGauge (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord f b).eval φ (D.cornerGaugeGenerators G g)=
      (D.boundaryCornerBasis G f b ⟨0,D.boundaryPositive f b⟩).toUnit*
        (D.boundaryWord f b).eval φ g*
          (D.boundaryCornerBasis G f b ⟨0,D.boundaryPositive f b⟩).toUnit⁻¹ := by
  rw [D.boundaryWord_eval_raw,D.boundaryWord_eval_raw]
  simp_rw [D.boundaryEdge_cornerGauge]
  exact SurfaceSurgery.cyclic_reverse_product_gauge _ (D.boundaryPositive f b)
    (fun i => (D.boundaryCornerBasis G f b i).toUnit)
    (fun i => (D.boundaryEdgeWord f b i).eval φ g)

/-- Fix the selected base corner of every boundary. These are coordinate gauges, not extra equations
on an old local system. -/
def CornerBases.Based (G : D.CornerBases (R:=A)) : Prop :=
  ∀ f b,D.boundaryCornerBasis G f b ⟨0,D.boundaryPositive f b⟩=MatrixIso.refl

lemma basedCorner_boundaryWord (hG : CornerBases.Based D G) (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord f b).eval φ (D.cornerGaugeGenerators G g)=
      (D.boundaryWord f b).eval φ g := by
  rw [D.boundaryWord_cornerGauge,hG f b]
  have hh : (MatrixIso.refl : MatrixIso A (Fin (D.rank f)) (Fin (D.rank f))).toUnit=1 := by
    apply Units.ext
    ext i j
    simp [MatrixIso.toUnit,MatrixIso.refl,Matrix.one_apply]
  rw [hh]
  simp

lemma basedCorner_surfaceWord (hG : CornerBases.Based D G) (f : F) :
    (D.surfaceWord f).eval φ (D.cornerGaugeGenerators G g)=(D.surfaceWord f).eval φ g := by
  simp only [surfaceWord,Term.eval,wordProduct_eval_raw,List.map_ofFn,Function.comp_def,
    D.basedCorner_boundaryWord φ G g hG]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity)
variable (G : D.CornerBases (R:=A)) (hG : CornerBases.Based D G)

/-- Arbitrary independent internal corner gauges act on the full solution, not just on boundary
holonomies or its regular seam equations. The original scalar punctures and handles are
unchanged. -/
def basedCornerSolution (P : D.Punctures R) (x : D.Solution P A) : D.Solution P A := by
  refine ⟨⟨D.cornerGaugeGenerators G x.val.val,?_⟩,?_⟩
  · intro j
    cases j with
    | inl f =>
      change SameFramedFlag (fun _ => 0)
        (matrixUnitEquiv ((D.surfaceWord f).eval (algebraMap R A) (D.cornerGaugeGenerators G x.val.val)))
        (matrixUnitEquiv ((D.surfaceTarget P f).eval (algebraMap R A) (D.cornerGaugeGenerators G x.val.val)))
      rw [D.basedCorner_surfaceWord (algebraMap R A) G x.val.val hG]
      exact x.val.property (.inl f)
    | inr s =>
      exact D.seamHolds_cornerGauge (algebraMap R A) G x.val.val s (x.val.property (.inr s))
  · exact D.vertexHolds_cornerGauge G x.val.val x.property
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity)

abbrev BoundaryBases := (f : F) → (b : Fin (D.boundaryCount f)) →
  (i : Fin (D.boundaryLength f b)) → MatrixIso A (Fin (D.rank f)) (Fin (D.rank f))

/-- Transport the exhaustively indexed boundary bases to the side occurrences, including every
repeated facet and every cyclic base position. -/
def cornerBasesOfBoundary (B : D.BoundaryBases (A:=A)) : D.CornerBases (R:=A) := fun a =>
  let z := D.boundarySide.symm a
  (B z.1 z.2.1 z.2.2).reindex
    (finCongr (congrArg D.rank (D.sideCircle_facet a)).symm)
    (finCongr (congrArg D.rank (D.sideCircle_facet a)).symm)

lemma boundaryBasis_ofBoundary (B : D.BoundaryBases (A:=A))
    (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    D.boundaryCornerBasis (D.cornerBasesOfBoundary B) f b i=B f b i := by
  have hh := MatrixIso.finite_basis_transport
    (fun z : (f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b) => D.rank z.1)
    (fun z => B z.1 z.2.1 z.2.2)
    ⟨f,b,i⟩ (D.boundarySide.symm (D.boundarySide ⟨f,b,i⟩))
    (D.rank f) (D.rank (D.ports.facet (D.boundarySide ⟨f,b,i⟩)))
    rfl (congrArg D.rank (D.sideCircle_facet (D.boundarySide ⟨f,b,i⟩))).symm
    (D.boundarySide.symm_apply_apply ⟨f,b,i⟩).symm
    (congrArg D.rank (D.boundaryFacet f b i)).symm
  simpa only [boundaryCornerBasis,cornerBasesOfBoundary,finCongr_refl,
    MatrixIso.reindex_refl_eq] using hh


lemma cornerBasesOfBoundary_based (B : D.BoundaryBases (A:=A))
    (hB : ∀ f b,B f b ⟨0,D.boundaryPositive f b⟩=MatrixIso.refl) :
    CornerBases.Based D (D.cornerBasesOfBoundary B) := by
  intro f b
  rw [D.boundaryBasis_ofBoundary,hB]
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*} [Group G]

/-- Chronological prefix products: the first edge acts first. -/
def prefixProduct (e : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => e n*prefixProduct e n

@[simp] lemma prefixProduct_zero (e : ℕ → G) : prefixProduct e 0=1 := rfl
@[simp] lemma prefixProduct_succ (e : ℕ → G) (n : ℕ) :
    prefixProduct e (n+1)=e n*prefixProduct e n := rfl

lemma prefixProduct_eq_reverse (e : ℕ → G) (n : ℕ) :
    prefixProduct e n=(List.ofFn (fun i : Fin n => e i.val)).reverse.prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixProduct_succ,List.ofFn_succ',List.concat_eq_append,List.reverse_concat,List.prod_cons,ih]
    rfl

/-- Extension by 1 is solely for evaluating the finite prefix; no selected path ever encounters an
extended edge. -/
def cycleEdge {n : ℕ} (e : Fin n → G) (i : ℕ) : G :=
  if h : i<n then e ⟨i,h⟩ else 1

@[simp] lemma cycleEdge_at {n : ℕ} (e : Fin n → G) (i : Fin n) :
    cycleEdge e i.val=e i := by simp [cycleEdge,i.isLt]

def prefixBasis {n : ℕ} (e : Fin n → G) (i : Fin n) : G :=
  (prefixProduct (cycleEdge e) i.val)⁻¹

@[simp] lemma prefixBasis_zero {n : ℕ} (hn : 0<n) (e : Fin n → G) :
    prefixBasis e ⟨0,hn⟩=1 := by simp [prefixBasis]

lemma prefixProduct_cycle {n : ℕ} (e : Fin n → G) :
    prefixProduct (cycleEdge e) n=(List.ofFn e).reverse.prod := by
  rw [prefixProduct_eq_reverse]
  simp only [cycleEdge_at]

/-- All interior edges become 1; the FINAL side retains precisely the original based holonomy, not a
merely conjugate matrix. -/
theorem prefix_gauge {n : ℕ} (hn : 0<n) (e : Fin n → G) (i : Fin n) :
    prefixBasis e ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩*e i*(prefixBasis e i)⁻¹=
      if i.val+1<n then 1 else (List.ofFn e).reverse.prod := by
  by_cases hi : i.val+1<n
  · rw [ite_eq_left hi]
    simp only [prefixBasis,Nat.mod_eq_of_lt hi,prefixProduct_succ,cycleEdge_at]
    group
  · rw [ite_eq_right hi]
    have he : i.val+1=n := by omega
    have hm : (i.val+1)%n=0 := by rw [he,Nat.mod_self]
    simp only [prefixBasis,hm,prefixProduct_zero,inv_one,one_mul,inv_inv]
    rw [←cycleEdge_at e i,←prefixProduct_succ,he,prefixProduct_cycle]
end IntegralCharacterVarieties.SurfaceSurgery

end

end OAI
