import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SurfacePresentation

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.FlagCircuit.Data
open scoped Classical Matrix
open MatrixExpression HomTransport
variable {R A E J : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {rank : E → ℕ} (D : FlagCircuit.Data R E rank J)

/-- A surface equation is exact matrix equality: its single grade is zero. -/
theorem eq_of_constant_grade (g : D.Solution A) (j : J)
    (h : ∀ i,D.grade j i=0) :
    (D.left j).eval (algebraMap R A) g.val=(D.right j).eval (algebraMap R A) g.val := by
  have hg := (sameFramedFlag_matrix_iff _ _ _).mp (g.property j)
  have hh : ((D.right j).eval (algebraMap R A) g.val)⁻¹ *
      (D.left j).eval (algebraMap R A) g.val=1 := by
    apply Units.ext
    ext i k
    exact hg i k (by rw [h,h])
  exact (inv_mul_eq_one.mp hh).symm
end IntegralCharacterVarieties.FlagCircuit.Data

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression OccurrenceIncidence
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity) (P : D.Punctures R)
variable (g : D.Solution P A)

def evaluatedBoundaryEdge (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ :=
  (D.boundaryEdgeWord (R:=R) f b i).eval (algebraMap R A) g.val.val

lemma wordProduct_eval {n : ℕ} (L : List (D.Word R n)) :
    (D.wordProduct L).eval (algebraMap R A) g.val.val=
      (L.map (fun t => t.eval (algebraMap R A) g.val.val)).prod := by
  induction L with
  | nil => simp [wordProduct,Term.eval,mapUnit]
  | cons x xs ih =>
      simpa only [wordProduct,List.foldr_cons,Term.eval,List.map_cons,List.prod_cons] using
        congrArg (fun z => x.eval (algebraMap R A) g.val.val*z) ih

lemma boundaryWord_eval (f : F) (b : Fin (D.boundaryCount f)) :
    (D.boundaryWord (R:=R) f b).eval (algebraMap R A) g.val.val=
      ((List.ofFn (D.evaluatedBoundaryEdge P g f b)).reverse).prod := by
  rw [boundaryWord,D.wordProduct_eval P g,List.map_reverse,List.map_ofFn]
  rfl


theorem actual_surface_relation (f : F) :
    (D.surfaceWord (R:=R) f).eval (algebraMap R A) g.val.val=
      (D.surfaceTarget P f).eval (algebraMap R A) g.val.val :=
  (D.edgeCircuit P).eq_of_constant_grade g.val (.inl f) (fun _ => rfl)

lemma surfaceWord_eval (f : F) :
    (D.surfaceWord (R:=R) f).eval (algebraMap R A) g.val.val=
      (List.ofFn (fun k => (D.commutatorWord (R:=R) f k).eval (algebraMap R A) g.val.val)).prod *
      (List.ofFn (fun b => ((List.ofFn (D.evaluatedBoundaryEdge P g f b)).reverse).prod)).prod := by
  simp only [surfaceWord,Term.eval,D.wordProduct_eval P g,List.map_ofFn,Function.comp_def]
  simp_rw [D.boundaryWord_eval P g]

/-- The exact rank-n disk step: genus zero and one boundary circle. All original punctures, full-ring units, side occurrences and their orientations are kept. -/
theorem actual_disk_relation (f : F) (hg : D.genus f=0) (hb : D.boundaryCount f=1) :
    ((List.ofFn (D.evaluatedBoundaryEdge P g f ⟨0,by omega⟩)).reverse).prod=
      (D.surfaceTarget P f).eval (algebraMap R A) g.val.val := by
  have hh := D.actual_surface_relation P g f
  rw [D.surfaceWord_eval P g] at hh
  have hnil (v : Fin (D.genus f) → (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :
      List.ofFn v=[] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simpa using hg
  rw [hnil,List.prod_nil,one_mul] at hh
  have hone (v : Fin (D.boundaryCount f) → (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :
      List.ofFn v=[v ⟨0,by omega⟩] := by
    apply List.ext_getElem
    · simp [hb]
    · intro i hi hj
      have hi0 : i=0 := by simp only [List.length_ofFn] at hi; omega
      subst i
      simp
  rw [hone,List.prod_singleton] at hh
  exact hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.DiskGauge
variable {G : Type*} [Group G] {n : ℕ} (h : Fin n → G)

/-- Parallel transport from the distinguished starting fiber. The first edge acts first, matching Diagram.boundaryWord exactly. -/
def prefixTransport (i : ℕ) : G := ((List.ofFn h).take i).reverse.prod

def next (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ (by have := i.isLt; omega)⟩

@[simp] theorem prefix_zero : prefixTransport h 0=1 := by simp [prefixTransport]
@[simp] theorem prefix_full : prefixTransport h n=(List.ofFn h).reverse.prod := by
  unfold prefixTransport
  rw [List.take_of_length_le (by simp)]

theorem prefix_step (i : Fin n) : prefixTransport h (i.val+1)=h i*prefixTransport h i.val := by
  unfold prefixTransport
  rw [List.take_succ_eq_append_getElem (by simp),List.reverse_append]
  simp

lemma next_within (i : Fin n) (hi : i.val+1<n) : (next i).val=i.val+1 :=
  Nat.mod_eq_of_lt hi
lemma next_last (i : Fin n) (hi : ¬i.val+1<n) : (next i).val=0 := by
  have hlast : i.val+1=n := by omega
  change (i.val+1)%n=0
  rw [hlast,Nat.mod_self]

/-- Exact normal form of the old cyclic transport. All gauges are units in the original base ring when G is GL, not merely rationally invertible matrices. -/
theorem normalized_edge (i : Fin n) :
    (prefixTransport h (next i).val)⁻¹*h i*prefixTransport h i.val=
      if i.val+1<n then 1 else (List.ofFn h).reverse.prod := by
  by_cases hi : i.val+1<n
  · rw [ite_eq_left hi,next_within i hi,mul_assoc,← prefix_step h i]
    exact inv_mul_cancel _
  · rw [ite_eq_right hi,next_last i hi,prefix_zero,inv_one,one_mul,← prefix_step h i]
    have hlast : i.val+1=n := by omega
    rw [hlast,prefix_full]

/-- This is a factorization of every old edge, not replacement of it by an independent block diagonal edge. -/
theorem edge_factorization (i : Fin n) :
    h i*prefixTransport h i.val=prefixTransport h (next i).val *
      (if i.val+1<n then 1 else (List.ofFn h).reverse.prod) := by
  have hh := normalized_edge h i
  rw [← hh]
  group
end IntegralCharacterVarieties.DiskGauge

namespace IntegralCharacterVarieties.HomTransport
open scoped Matrix
variable {R : Type*} [CommRing R] {n : ℕ}
theorem matrixUnitEquiv_mul_apply (a b : (Matrix (Fin n) (Fin n) R)ˣ) (v : Fin n → R) :
    matrixUnitEquiv (a*b) v=matrixUnitEquiv a (matrixUnitEquiv b v) := by
  change (a.val*b.val)*ᵥv=a.val*ᵥ(b.val*ᵥv)
  exact (Matrix.mulVec_mulVec _ _ _).symm
end IntegralCharacterVarieties.HomTransport

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression HomTransport
variable {R A : Type} [CommRing R] [CommRing A]

theorem scalarUnit_one (n : ℕ) : scalarUnit (R:=R) n 1=1 := map_one _

theorem map_scalarUnit (φ : R →+* A) (n : ℕ) (u : Rˣ) :
    mapUnit φ (scalarUnit n u)=scalarUnit n (Units.map φ.toMonoidHom u) := by
  apply Units.ext
  ext i j
  by_cases hij : i=j <;> simp [mapUnit,scalarUnit,Matrix.algebraMap_eq_diagonal,Matrix.diagonal,Matrix.map_apply,hij]

theorem scalarUnit_apply (n : ℕ) (u : Rˣ) (v : Fin n → R) :
    matrixUnitEquiv (scalarUnit n u) v=(u:R) • v := by
  change (algebraMap R (Matrix (Fin n) (Fin n) R) (u:R))*ᵥv=_
  ext i
  simp [Matrix.algebraMap_eq_diagonal,Matrix.mulVec_diagonal]

variable {F S V : Type} {arity : S → ℕ} [Algebra R A]
variable (D : Diagram F S V arity) (P : D.Punctures R) (g : D.Solution P A)

def diskScalar (f : F) : Aˣ :=
  Units.map (algebraMap R A).toMonoidHom (∏ j,P.scalar f j)⁻¹

theorem surfaceTarget_eval (f : F) :
    (D.surfaceTarget P f).eval (algebraMap R A) g.val.val=
      scalarUnit (D.rank f) (D.diskScalar P f) :=
  map_scalarUnit _ _ _

theorem actual_disk_scalar (f : F) (hg : D.genus f=0) (hb : D.boundaryCount f=1) :
    (List.ofFn (D.evaluatedBoundaryEdge P g f ⟨0,by omega⟩)).reverse.prod=
      scalarUnit (D.rank f) (D.diskScalar P f) :=
  (D.actual_disk_relation P g f hg hb).trans (D.surfaceTarget_eval P g f)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.DiskGauge
open scoped Classical Matrix
open HomTransport SurfacePresentation.Diagram
variable {R : Type} [CommRing R] {m n : ℕ}
variable (h : Fin m → (Matrix (Fin n) (Fin n) R)ˣ) (u : Rˣ)
variable (hcycle : (List.ofFn h).reverse.prod=scalarUnit n u)

/-- Changing frames never alters the old edge transport. -/
def frame (i : Fin m) : (Fin n → R) ≃ₗ[R] (Fin n → R) :=
  matrixUnitEquiv (prefixTransport h i.val)

def scalarAt (i : Fin m) : Rˣ := if i.val+1 < m then 1 else u

include hcycle
lemma scalarAt_factorization (i : Fin m) :
    h i*prefixTransport h i.val=prefixTransport h (next i).val * scalarUnit n (scalarAt u i) := by
  rw [edge_factorization h i,hcycle]
  by_cases hi : i.val+1 < m <;> simp [scalarAt,hi,scalarUnit_one]

/-- The diagram edge preserves the transported U and induces the same scalar on U and V/U in their transported frames. -/
theorem edge_frame (i : Fin m) (v : Fin n → R) :
    matrixUnitEquiv (h i) (frame h i v)=frame h (next i) ((scalarAt u i:R) • v) := by
  change matrixUnitEquiv (h i) (matrixUnitEquiv (prefixTransport h i.val) v)=_
  rw [← matrixUnitEquiv_mul_apply,scalarAt_factorization h u hcycle i,
    matrixUnitEquiv_mul_apply,scalarUnit_apply]
  rfl

variable (U : Submodule R (Fin n → R))
def parallelSubspace (i : Fin m) : Submodule R (Fin n → R) := U.map (frame h i).toLinearMap

def subFrame (i : Fin m) : U ≃ₗ[R] parallelSubspace h U i :=
  (frame h i).submoduleMap U

def quotientFrame (i : Fin m) : ((Fin n → R) ⧸ U) ≃ₗ[R] ((Fin n → R) ⧸ parallelSubspace h U i) :=
  Submodule.Quotient.equiv U _ (frame h i) rfl

theorem edge_subspace (i : Fin m) :
    (parallelSubspace h U i).map (matrixUnitEquiv (h i)).toLinearMap=parallelSubspace h U (next i) := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨(scalarAt u i:R) • z,U.smul_mem _ hz,?_⟩
    exact (edge_frame h u hcycle i z).symm
  · rintro ⟨z,hz,rfl⟩
    refine ⟨frame h i ((↑((scalarAt u i)⁻¹):R) • z),?_,?_⟩
    · exact ⟨(↑((scalarAt u i)⁻¹):R) • z,U.smul_mem _ hz,rfl⟩
    · change matrixUnitEquiv (h i) (frame h i ((↑((scalarAt u i)⁻¹):R) • z))=frame h (next i) z
      rw [edge_frame h u hcycle,smul_smul,Units.mul_inv,one_smul]

def subEdge (i : Fin m) : parallelSubspace h U i ≃ₗ[R] parallelSubspace h U (next i) :=
  (matrixUnitEquiv (h i)).ofSubmodules _ _ (edge_subspace h u hcycle U i)

def quotientEdge (i : Fin m) : ((Fin n → R) ⧸ parallelSubspace h U i) ≃ₗ[R]
    ((Fin n → R) ⧸ parallelSubspace h U (next i)) :=
  Submodule.Quotient.equiv _ _ (matrixUnitEquiv (h i)) (edge_subspace h u hcycle U i)

theorem subEdge_frame (i : Fin m) (v : U) :
    subEdge h u hcycle U i (subFrame h U i v)=
      subFrame h U (next i) ((scalarAt u i:R) • v) := by
  apply Subtype.ext
  exact edge_frame h u hcycle i v.val

theorem quotientEdge_frame (i : Fin m) (v : (Fin n → R) ⧸ U) :
    quotientEdge h u hcycle U i (quotientFrame h U i v)=
      quotientFrame h U (next i) ((scalarAt u i:R) • v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
      change Submodule.Quotient.mk (matrixUnitEquiv (h i) (frame h i v))=
        Submodule.Quotient.mk (frame h (next i) ((scalarAt u i:R) • v))
      rw [edge_frame h u hcycle]
end IntegralCharacterVarieties.DiskGauge

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open DiskGauge HomTransport
variable {F S V R A : Type} {arity : S → ℕ}
  [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity) (P : D.Punctures R) (g : D.Solution P A)
variable (f : F) (hg : D.genus f=0) (hb : D.boundaryCount f=1)
variable (U : Submodule A (Fin (D.rank f) → A))

abbrev diskBoundaryEdge := D.evaluatedBoundaryEdge P g f ⟨0,by omega⟩

/-- Lower U fibers, read from the old solution, including the initial fiber and last-to-first edge. -/
def diskSubspace (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :=
  parallelSubspace (D.diskBoundaryEdge P g f hb) U i

def diskSubFrame (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :
    U ≃ₗ[A] D.diskSubspace P g f hb U i :=
  subFrame (D.diskBoundaryEdge P g f hb) U i

def diskQuotientFrame (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :
    ((Fin (D.rank f) → A) ⧸ U) ≃ₗ[A] ((Fin (D.rank f) → A) ⧸ D.diskSubspace P g f hb U i) :=
  quotientFrame (D.diskBoundaryEdge P g f hb) U i

def diskSubEdge (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :
    D.diskSubspace P g f hb U i ≃ₗ[A] D.diskSubspace P g f hb U (next i) :=
  subEdge (D.diskBoundaryEdge P g f hb) (D.diskScalar P f) (D.actual_disk_scalar P g f hg hb) U i

def diskQuotientEdge (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :
    ((Fin (D.rank f) → A) ⧸ D.diskSubspace P g f hb U i) ≃ₗ[A]
      ((Fin (D.rank f) → A) ⧸ D.diskSubspace P g f hb U (next i)) :=
  quotientEdge (D.diskBoundaryEdge P g f hb) (D.diskScalar P f) (D.actual_disk_scalar P g f hg hb) U i

/-- Every old rank-n scalar disk has the required parallel subspace and quotient. Both are restrictions/quotients of the old transports. -/
theorem actual_disk_forward (i : Fin (D.boundaryLength f ⟨0,by omega⟩)) :
    ((D.diskSubspace P g f hb U i).map
      (matrixUnitEquiv (D.diskBoundaryEdge P g f hb i)).toLinearMap =
      D.diskSubspace P g f hb U (next i)) ∧
    (∀ v : U, D.diskSubEdge P g f hg hb U i (D.diskSubFrame P g f hb U i v)=
      D.diskSubFrame P g f hb U (next i) ((scalarAt (D.diskScalar (A:=A) P f) i:A) • v)) ∧
    (∀ v : (Fin (D.rank f) → A) ⧸ U,
      D.diskQuotientEdge P g f hg hb U i (D.diskQuotientFrame P g f hb U i v)=
      D.diskQuotientFrame P g f hb U (next i) ((scalarAt (D.diskScalar (A:=A) P f) i:A) • v)) :=
  ⟨edge_subspace _ _ (D.actual_disk_scalar P g f hg hb) _ _,
    subEdge_frame _ _ (D.actual_disk_scalar P g f hg hb) _ _,
    quotientEdge_frame _ _ (D.actual_disk_scalar P g f hg hb) _ _⟩
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
