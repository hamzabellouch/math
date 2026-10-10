import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.GaugeEquivalences

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression SurfaceSurgery
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

/-- The explicit inverse prefix product at every boundary corner. -/
def normalizingBoundaryBases : D.BoundaryBases (A:=A) := fun f b i =>
  MatrixIso.unit (prefixBasis (fun j => (D.boundaryEdgeWord f b j).eval φ g) i)

def normalizingCorners : D.CornerBases (R:=A) :=
  D.cornerBasesOfBoundary (D.normalizingBoundaryBases φ g)

lemma normalizingCorners_based : CornerBases.Based D (D.normalizingCorners φ g) := by
  apply D.cornerBasesOfBoundary_based
  intro f b
  dsimp only [normalizingBoundaryBases]
  rw [prefixBasis_zero]
  apply MatrixIso.ext <;> ext i j <;> simp [MatrixIso.unit,MatrixIso.refl,Matrix.one_apply]

/-- This changes all side and frame coordinates, so it respects every named quotient at every
vertex, not just a list of boundary conjugacy classes. -/
def normalizeBoundaryGenerators := D.cornerGaugeGenerators (D.normalizingCorners φ g) g

lemma normalized_boundaryEdge (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) :
    (D.boundaryEdgeWord f b i).eval φ (D.normalizeBoundaryGenerators φ g)=
      if i.val+1<D.boundaryLength f b then 1 else (D.boundaryWord f b).eval φ g := by
  unfold normalizeBoundaryGenerators
  rw [D.boundaryEdge_cornerGauge]
  simp only [normalizingCorners,D.boundaryBasis_ofBoundary,normalizingBoundaryBases,
    MatrixIso.toUnit_unit]
  rw [prefix_gauge (D.boundaryPositive f b)]
  rw [D.boundaryWord_eval_raw]

variable [Algebra R A]
/-- A full solution in canonical boundary path coordinates. It is constructed from any old solution,
uniformly over the full coefficient ring. -/
def normalizeBoundarySolution (P : D.Punctures R) (x : D.Solution P A) : D.Solution P A :=
  D.basedCornerSolution (D.normalizingCorners (algebraMap R A) x.val.val)
    (D.normalizingCorners_based (algebraMap R A) x.val.val) P x

/-- Exact forward coverage in the original full solution variety. -/
theorem normalizeBoundary_reconstruct (P : D.Punctures R) (x : D.Solution P A) :
    D.basedCornerSolution (fun a => (D.normalizingCorners (algebraMap R A) x.val.val a).symm)
      (D.basedCorner_inverse _ (D.normalizingCorners_based (algebraMap R A) x.val.val)) P
      (D.normalizeBoundarySolution P x)=x := by
  apply Subtype.ext
  apply Subtype.ext
  exact D.cornerGaugeGenerators_inverse _ x.val.val

theorem normalizeBoundarySolution_edge (P : D.Punctures R) (x : D.Solution P A)
    (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    (D.boundaryEdgeWord f b i).eval (algebraMap R A) (D.normalizeBoundarySolution P x).val.val=
      if i.val+1<D.boundaryLength f b then 1 else (D.boundaryWord f b).eval (algebraMap R A) x.val.val :=
  D.normalized_boundaryEdge (algebraMap R A) x.val.val f b i
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfaceSurgery
variable {G : Type*} [Group G]
/-- The based normalization matrices are FORCED by the edge maps. There is no extra monodromy
equation hidden in the last interval. -/
lemma prefixBasis_unique {n : ℕ} (hn : 0<n) (e C : Fin n → G)
    (h0 : C ⟨0,hn⟩=1)
    (hC : ∀ i : Fin n,i.val+1<n →
      C ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩*e i*(C i)⁻¹=1) :
    C=prefixBasis e := by
  have hh : ∀ k : ℕ,∀ hk : k<n,C ⟨k,hk⟩=(prefixProduct (cycleEdge e) k)⁻¹ := by
    intro k
    induction k with
    | zero => intro hk; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k<n := by omega
      have hc := hC ⟨k,hk'⟩ hk
      simp only [Nat.mod_eq_of_lt hk] at hc
      have hd : C ⟨k+1,hk⟩*e ⟨k,hk'⟩=C ⟨k,hk'⟩ := mul_inv_eq_one.mp hc
      calc
        C ⟨k+1,hk⟩=(C ⟨k+1,hk⟩*e ⟨k,hk'⟩)*(e ⟨k,hk'⟩)⁻¹ := by simp [mul_assoc]
        _=C ⟨k,hk'⟩*(e ⟨k,hk'⟩)⁻¹ := by rw [hd]
        _=(prefixProduct (cycleEdge e) (k+1))⁻¹ := by
          rw [ih hk',prefixProduct_succ,←cycleEdge_at e ⟨k,hk'⟩,mul_inv_rev]
  funext i
  exact hh i.val i.isLt
end IntegralCharacterVarieties.SurfaceSurgery

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma reindex_injective (e : γ ≃ α) (f : δ ≃ β) :
    Function.Injective (fun x : MatrixIso R α β => x.reindex e f) := by
  intro x y h
  apply ext
  · ext i j
    simpa only [reindex,Matrix.submatrix_apply,Equiv.apply_symm_apply] using
      congrArg (fun z => z.val (f.symm i) (e.symm j)) h
  · ext i j
    simpa only [reindex,Matrix.submatrix_apply,Equiv.apply_symm_apply] using
      congrArg (fun z => z.inv (e.symm i) (f.symm j)) h
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression SurfaceSurgery
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)

lemma boundaryCornerBasis_injective :
    Function.Injective (fun G : D.CornerBases (R:=A) => D.boundaryCornerBasis G) := by
  intro G H h
  funext a
  obtain ⟨⟨f,b,i⟩,rfl⟩ := D.boundarySide.surjective a
  have hh := congrFun (congrFun (congrFun h f) b) i
  exact MatrixIso.reindex_injective _ _ hh

def IsBoundaryNormalized
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) : Prop :=
  ∀ f b (i : Fin (D.boundaryLength f b)),i.val+1<D.boundaryLength f b →
    (D.boundaryEdgeWord f b i).eval φ g=1

lemma normalize_isBoundaryNormalized
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) :
    D.IsBoundaryNormalized φ (D.normalizeBoundaryGenerators φ g) := by
  intro f b i hi
  rw [D.normalized_boundaryEdge,ite_eq_left hi]

lemma normalizingCorners_unique
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (G : D.CornerBases (R:=A)) (hG : CornerBases.Based D G)
    (hC : D.IsBoundaryNormalized φ (D.cornerGaugeGenerators G g)) :
    D.normalizingCorners φ g=G := by
  apply D.boundaryCornerBasis_injective
  funext f b i
  have hh := prefixBasis_unique (D.boundaryPositive f b)
    (fun j => (D.boundaryEdgeWord f b j).eval φ g)
    (fun j => (D.boundaryCornerBasis G f b j).toUnit)
    (by rw [hG f b]; apply Units.ext; ext j k; simp [MatrixIso.toUnit,MatrixIso.refl,Matrix.one_apply])
    (by intro j hj; rw [←D.boundaryEdge_cornerGauge]; exact hC f b j hj)
  have hi := congrArg MatrixIso.unit (congrFun hh i)
  erw [MatrixIso.unit_toUnit] at hi
  simp only [normalizingCorners,D.boundaryBasis_ofBoundary,normalizingBoundaryBases]
  exact hi.symm

variable [Algebra R A]
/-- The canonical locus is a subtype of the full solution, retaining all old equations, all ordered
vertices and all quotient identifications. -/
abbrev NormalizedSolution (P : D.Punctures R) (A : Type) [CommRing A] [Algebra R A] :=
  {x : D.Solution P A // D.IsBoundaryNormalized (algebraMap R A) x.val.val}
abbrev BasedCorners (A : Type) [CommRing A] :=
  {G : D.CornerBases (R:=A) // CornerBases.Based D G}

/-- Unique normalized full solution plus all independent based corner matrices. This is one global
path-coordinate chart, not the missing cutting map. -/
def boundaryChart (P : D.Punctures R) :
    D.Solution P A ≃ D.NormalizedSolution P A × D.BasedCorners A where
  toFun x := (⟨D.normalizeBoundarySolution P x,
    D.normalize_isBoundaryNormalized (algebraMap R A) x.val.val⟩,
    ⟨D.normalizingCorners (algebraMap R A) x.val.val,
      D.normalizingCorners_based (algebraMap R A) x.val.val⟩)
  invFun z := D.basedCornerSolution (fun a => (z.2.val a).symm)
    (D.basedCorner_inverse z.2.val z.2.property) P z.1.val
  left_inv x := D.normalizeBoundary_reconstruct P x
  right_inv z := by
    let x := D.basedCornerSolution (fun a => (z.2.val a).symm)
      (D.basedCorner_inverse z.2.val z.2.property) P z.1.val
    have hx : D.basedCornerSolution z.2.val z.2.property P x=z.1.val := by
      apply Subtype.ext
      apply Subtype.ext
      change D.cornerGaugeGenerators z.2.val
        (D.cornerGaugeGenerators (fun a => (z.2.val a).symm) z.1.val.val.val)=_
      have hh := D.cornerGaugeGenerators_inverse (fun a => (z.2.val a).symm) z.1.val.val.val
      simpa only [MatrixIso.symm_symm_eq] using hh
    have hc : D.normalizingCorners (algebraMap R A) x.val.val=z.2.val := by
      apply D.normalizingCorners_unique (algebraMap R A) x.val.val z.2.val z.2.property
      change D.IsBoundaryNormalized (algebraMap R A)
        (D.basedCornerSolution z.2.val z.2.property P x).val.val
      rw [hx]
      exact z.1.property
    apply Prod.ext
    · apply Subtype.ext
      change D.normalizeBoundarySolution P x=z.1.val
      apply Subtype.ext
      apply Subtype.ext
      change D.cornerGaugeGenerators (D.normalizingCorners (algebraMap R A) x.val.val) x.val.val=_
      rw [hc]
      exact congrArg (fun y : D.Solution P A => y.val.val) hx
    · apply Subtype.ext
      exact hc
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
