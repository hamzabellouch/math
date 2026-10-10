import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.DiskGauge

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*} [Group G]

def comm (a b : G) : G := a*b*a⁻¹*b⁻¹

def handleProduct (H : List (G × G)) : G := (H.map (fun p => comm p.1 p.2)).prod

def surfaceProduct (H : List (G × G)) (B : List G) : G := handleProduct H * B.prod

def conjugate (t a : G) : G := t*a*t⁻¹

def conjugateHandles (t : G) (H : List (G × G)) : List (G × G) :=
  H.map (fun p => (conjugate t p.1,conjugate t p.2))

def conjugateBoundaries (t : G) (B : List G) : List G := B.map (conjugate t)

@[simp] theorem handleProduct_nil : handleProduct ([] : List (G × G))=1 := rfl
@[simp] theorem handleProduct_cons (p : G × G) (H : List (G × G)) :
    handleProduct (p::H)=comm p.1 p.2*handleProduct H := rfl
@[simp] theorem handleProduct_append (H J : List (G × G)) :
    handleProduct (H++J)=handleProduct H*handleProduct J := by
  simp [handleProduct]

@[simp] theorem conjugate_one (t : G) : conjugate t 1=1 := by simp [conjugate]
@[simp] theorem conjugate_mul (t a b : G) : conjugate t (a*b)=conjugate t a*conjugate t b := by
  simp [conjugate,mul_assoc]
@[simp] theorem conjugate_inv (t a : G) : conjugate t a⁻¹=(conjugate t a)⁻¹ := by
  simp [conjugate,mul_assoc]
@[simp] theorem conjugate_comm (t a b : G) :
    comm (conjugate t a) (conjugate t b)=conjugate t (comm a b) := by
  simp only [comm,conjugate_mul,conjugate_inv]

@[simp] theorem handleProduct_conjugate (t : G) (H : List (G × G)) :
    handleProduct (conjugateHandles t H)=conjugate t (handleProduct H) := by
  induction H with
  | nil => simp [conjugateHandles]
  | cons p H ih => simp [conjugateHandles,handleProduct_cons,← ih]

@[simp] theorem boundaryProduct_conjugate (t : G) (B : List G) :
    (conjugateBoundaries t B).prod=conjugate t B.prod := by
  induction B with
  | nil => simp [conjugateBoundaries]
  | cons b B ih => simp [conjugateBoundaries,← ih]

/-- Cutting the boundary at the two band feet results in two positive boundary words. The t and
inverse t are adjacent band transports. -/
theorem split_boundary_word (H : List (G × G)) (C D : List G) (a b t : G) :
    surfaceProduct H (C++[a*t,t⁻¹*b]++D)=surfaceProduct H (C++[a*b]++D) := by
  simp [surfaceProduct,List.prod_append,mul_assoc]

/-- Joining two boundary circles of the same facet creates THIS additional handle. A provisional
unchanged-genus declaration would be incorrect. -/
theorem join_same_boundary_word (H : List (G × G)) (C : List G) (a b t : G) :
    surfaceProduct (conjugateHandles t H++[(t,a)])
      ((a*t*b*t⁻¹)::conjugateBoundaries t C)=
      conjugate t (surfaceProduct H (a::b::C)) := by
  simp only [surfaceProduct,handleProduct_append,handleProduct_conjugate,
    handleProduct_cons,handleProduct_nil,mul_one,List.prod_cons,
    boundaryProduct_conjugate]
  simp only [conjugate,comm]
  group

/-- If the old puncture word is central, no new puncture is introduced. -/
theorem join_same_relation (H : List (G × G)) (C : List G) (a b t z : G)
    (hold : surfaceProduct H (a::b::C)=z) (hz : Commute t z) :
    surfaceProduct (conjugateHandles t H++[(t,a)])
      ((a*t*b*t⁻¹)::conjugateBoundaries t C)=z := by
  rw [join_same_boundary_word,hold,conjugate,hz.eq]
  simp [mul_assoc]

/-- Attachment between different components: choose the first joining circle last on its facet and
the second joining circle first on its facet. Old handles on the second facet are transported
along an explicit based path. -/
theorem join_distinct_boundary_word (H J : List (G × G)) (C D : List G) (a b t : G) :
    surfaceProduct (H++conjugateHandles (C.prod*a*t) J)
      (C++[a*t*b*t⁻¹]++conjugateBoundaries t D)=
      surfaceProduct H (C++[a]) * conjugate t (surfaceProduct J (b::D)) := by
  simp only [surfaceProduct,handleProduct_append,handleProduct_conjugate,
    List.prod_append,List.prod_cons,List.prod_nil,mul_one,boundaryProduct_conjugate,
    conjugate]
  group

/-- Full scalar puncture products of the two old facets multiply. In application these z's are
products of scalar units extracted from Diagram.Solution. -/
theorem join_distinct_relation (H J : List (G × G)) (C D : List G) (a b t z w : G)
    (hH : surfaceProduct H (C++[a])=z) (hJ : surfaceProduct J (b::D)=w)
    (hw : Commute t w) :
    surfaceProduct (H++conjugateHandles (C.prod*a*t) J)
      (C++[a*t*b*t⁻¹]++conjugateBoundaries t D)=z*w := by
  rw [join_distinct_boundary_word,hH,hJ,conjugate,hw.eq]
  simp [mul_assoc]


theorem interchange_boundary_word (H : List (G × G)) (C D : List G) (a b : G) :
    surfaceProduct H (C++[conjugate a b,a]++D)=surfaceProduct H (C++[a,b]++D) := by
  simp [surfaceProduct,List.prod_append,conjugate,mul_assoc]

/-- Exact genus and boundary counts of the self-attachment. -/
theorem join_same_topology (H : List (G × G)) (C : List G) (a b t : G) :
    (conjugateHandles t H++[(t,a)]).length=H.length+1 ∧
    ((a*t*b*t⁻¹)::conjugateBoundaries t C).length+1=(a::b::C).length := by
  simp [conjugateHandles,conjugateBoundaries]

/-- Exact genus and boundary counts for attaching different facets. -/
theorem join_distinct_topology (H J : List (G × G)) (C D : List G) (a b t : G) :
    (H++conjugateHandles (C.prod*a*t) J).length=H.length+J.length ∧
    (C++[a*t*b*t⁻¹]++conjugateBoundaries t D).length+1=
      (C++[a]).length+(b::D).length := by
  simp [conjugateHandles,conjugateBoundaries]
  omega

/-- All formulas use the same full-ring units under base change. Nothing in these word maps inverts
a determinant outside the original general linear group. -/
theorem join_handles_natural {G' : Type*} [Group G'] (φ : G →* G')
    (H : List (G × G)) (t : G) :
    (conjugateHandles t H).map (fun p => (φ p.1,φ p.2))=
      conjugateHandles (φ t) (H.map (fun p => (φ p.1,φ p.2))) := by
  simp [conjugateHandles,List.map_map,Function.comp_def,conjugate]
end IntegralCharacterVarieties.SurfaceSurgery

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression SurfaceSurgery
variable {F S V R A : Type} {arity : S → ℕ}
  [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity) (P : D.Punctures R) (g : D.Solution P A)

def evaluatedHandles (f : F) : List ((Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ ×
    (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :=
  List.ofFn (fun k => (g.val.val (.handle f k false),g.val.val (.handle f k true)))

def evaluatedBoundaries (f : F) : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ :=
  List.ofFn (fun b => (List.ofFn (D.evaluatedBoundaryEdge P g f b)).reverse.prod)

/-- All old handle and boundary transports, extracted from the full original solution, satisfy
precisely the relation used by the surface surgery formulas. -/
theorem actual_word_relation (f : F) :
    surfaceProduct (D.evaluatedHandles P g f) (D.evaluatedBoundaries P g f)=
      scalarUnit (D.rank f) (D.diskScalar P f) := by
  have hh := D.actual_surface_relation P g f
  rw [D.surfaceWord_eval P g,D.surfaceTarget_eval P g] at hh
  convert hh using 1
  simp [surfaceProduct,handleProduct,evaluatedHandles,evaluatedBoundaries,
    List.map_ofFn,Function.comp_def,SurfaceSurgery.comm,commutatorWord,Term.eval]

lemma scalarUnit_mul (n : ℕ) (u v : Aˣ) :
    scalarUnit n (u*v)=scalarUnit n u*scalarUnit n v := map_mul _ _ _

lemma scalarUnit_commute {n : ℕ} (a : (Matrix (Fin n) (Fin n) A)ˣ) (u : Aˣ) :
    Commute a (scalarUnit n u) := by
  show a*scalarUnit n u=scalarUnit n u*a
  apply Units.ext
  exact (Algebra.commutes (u:A) a.val).symm

/-- Splitting a circle of an old full solution preserves its prescribed puncture product with the
two explicitly constructed band transports. -/
theorem actual_split_boundary (f : F)
    (C E : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (a b t : (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (hB : D.evaluatedBoundaries P g f=C++[a*b]++E) :
    surfaceProduct (D.evaluatedHandles P g f) (C++[a*t,t⁻¹*b]++E)=
      scalarUnit (D.rank f) (D.diskScalar P f) := by
  rw [split_boundary_word,←hB]
  exact D.actual_word_relation P g f

/-- The handle appearing when TWO old boundary circles are joined is produced from g and t. -/
theorem actual_join_same (f : F)
    (C : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (a b t : (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (hB : D.evaluatedBoundaries P g f=a::b::C) :
    surfaceProduct (conjugateHandles t (D.evaluatedHandles P g f)++[(t,a)])
      ((a*t*b*t⁻¹)::conjugateBoundaries t C)=
      scalarUnit (D.rank f) (D.diskScalar P f) := by
  apply join_same_relation
  · rw [←hB]
    exact D.actual_word_relation P g f
  · exact scalarUnit_commute _ _

/-- Equal-rank fibers may be based on different original facets. -/
def rebaseUnit {m n : ℕ} (h : m=n) :
    (Matrix (Fin m) (Fin m) A)ˣ ≃* (Matrix (Fin n) (Fin n) A)ˣ := by
  subst n
  exact MulEquiv.refl _

@[simp] theorem rebaseUnit_scalar {m n : ℕ} (h : m=n) (u : Aˣ) :
    rebaseUnit h (scalarUnit m u)=scalarUnit n u := by subst n; rfl

/-- Direct two-facet attachment uses all handles of both old facets and the product of their
COMPLETE prescribed puncture scalars. This works in the original base ring A, in particular a
full integer ring. -/
theorem actual_join_distinct (f k : F) (h : D.rank k=D.rank f)
    (C E : List (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (a b t : (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
    (hF : D.evaluatedBoundaries P g f=C++[a])
    (hK : (D.evaluatedBoundaries P g k).map (rebaseUnit h)=b::E) :
    surfaceProduct (D.evaluatedHandles P g f++conjugateHandles (C.prod*a*t)
        ((D.evaluatedHandles P g k).map (fun p => (rebaseUnit h p.1,rebaseUnit h p.2))))
      (C++[a*t*b*t⁻¹]++conjugateBoundaries t E)=
      scalarUnit (D.rank f) (D.diskScalar P f * D.diskScalar P k) := by
  have hmap : surfaceProduct
      ((D.evaluatedHandles P g k).map (fun p => (rebaseUnit h p.1,rebaseUnit h p.2))) (b::E)=
      scalarUnit (D.rank f) (D.diskScalar P k) := by
    rw [←hK,←rebaseUnit_scalar h]
    have hk := congrArg (rebaseUnit h) (D.actual_word_relation P g k)
    convert hk using 1;
      simp [surfaceProduct,handleProduct,List.map_map,Function.comp_def,SurfaceSurgery.comm,
        map_list_prod]
  rw [scalarUnit_mul]
  apply join_distinct_relation
  · rw [←hF]
    exact D.actual_word_relation P g f
  · exact hmap
  · exact scalarUnit_commute _ _
end IntegralCharacterVarieties.SurfacePresentation.Diagram

/- Exact oriented boundary surgery, retaining side occurrence labels. -/

end

end OAI
