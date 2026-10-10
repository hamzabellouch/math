import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.Flags
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace OAI

noncomputable section
open scoped Classical Matrix

open scoped Classical
namespace IntegralCharacterVarieties.ExactSequenceChart

variable {R : Type*} [CommRing R]
variable {U V Q : Type*} [AddCommGroup U] [Module R U]
  [AddCommGroup V] [Module R V] [AddCommGroup Q] [Module R Q]

/-- Concrete frame equations defining one splitting chart. The domains are free modules in the matrix instantiation below; no affine-bundle hypothesis. -/
structure Chart (f : U →ₗ[R] V) (g : V →ₗ[R] Q) where
  j : Q →ₗ[R] V
  t : (U × Q) ≃ₗ[R] V
  t_eq : ∀ uq, t uq = f uq.1 + j uq.2
  d : Q ≃ₗ[R] Q
  d_eq : ∀ q, d q = g (j q)
  gf : ∀ u, g (f u) = 0

namespace Chart
variable {f : U →ₗ[R] V} {g : V →ₗ[R] Q} (C : Chart f g)

def left : V →ₗ[R] U := (LinearMap.fst R U Q).comp C.t.symm.toLinearMap

def sectionMap : Q →ₗ[R] V := C.j.comp C.d.symm.toLinearMap

lemma g_t (u : U) (q : Q) : g (C.t (u,q)) = C.d q := by
  rw [C.t_eq,map_add,C.gf,zero_add,C.d_eq]

lemma g_eq (v : V) : g v = C.d (C.t.symm v).2 := by
  simpa using C.g_t (C.t.symm v).1 (C.t.symm v).2

@[simp] lemma g_section (q : Q) : g (C.sectionMap q) = q := by
  change g (C.j (C.d.symm q)) = q
  rw [← C.d_eq,LinearEquiv.apply_symm_apply]

lemma t_inl (u : U) : C.t (u,0) = f u := by
  rw [C.t_eq,map_zero,add_zero]

lemma t_inr (q : Q) : C.t (0,q) = C.j q := by
  rw [C.t_eq,map_zero,zero_add]

@[simp] lemma left_f (u : U) : C.left (f u) = u := by
  change (C.t.symm (f u)).1 = u
  rw [← C.t_inl,LinearEquiv.symm_apply_apply]

@[simp] lemma left_section (q : Q) : C.left (C.sectionMap q) = 0 := by
  change (C.t.symm (C.j (C.d.symm q))).1 = 0
  rw [← C.t_inr,LinearEquiv.symm_apply_apply]

lemma decompose (v : V) : f (C.left v) + C.sectionMap (g v) = v := by
  change f (C.t.symm v).1 + C.j (C.d.symm (g v)) = v
  rw [C.g_eq,LinearEquiv.symm_apply_apply,← C.t_eq,LinearEquiv.apply_symm_apply]

lemma f_left_of_g_zero (v : V) (hv : g v = 0) : f (C.left v) = v := by
  simpa only [hv,map_zero,add_zero] using C.decompose v

abbrev RightInverse := { s : Q →ₗ[R] V // ∀ q, g (s q) = q }

def fromParameter (h : Q →ₗ[R] U) : RightInverse (g := g) :=
  ⟨C.sectionMap + f.comp h,by intro q; simp only [LinearMap.add_apply,
    LinearMap.comp_apply,map_add,C.g_section,C.gf,add_zero]⟩

def toParameter (s : RightInverse (g := g)) : Q →ₗ[R] U :=
  C.left.comp (s.val - C.sectionMap)

lemma to_from (h : Q →ₗ[R] U) : C.toParameter (C.fromParameter h) = h := by
  ext q
  change C.left (C.sectionMap q + f (h q) - C.sectionMap q) = h q
  rw [add_sub_cancel_left,C.left_f]

lemma from_to (s : RightInverse (g := g)) : C.fromParameter (C.toParameter s) = s := by
  apply Subtype.ext
  ext q
  have hk : g (s.val q - C.sectionMap q) = 0 := by
    rw [map_sub,s.property,C.g_section,sub_self]
  change C.sectionMap q + f (C.left (s.val q - C.sectionMap q)) = s.val q
  rw [C.f_left_of_g_zero _ hk,add_sub_cancel]

/-- All solutions of GS=1 on this matrix chart, with no missing rank-open constraints on S, form exactly the free affine parameter space. -/
def parameterEquiv : (Q →ₗ[R] U) ≃ RightInverse (g := g) where
  toFun := C.fromParameter
  invFun := C.toParameter
  left_inv := C.to_from
  right_inv := C.from_to

lemma overlap_formula (C' : Chart f g) (h : Q →ₗ[R] U) :
    C'.toParameter (C.fromParameter h) =
      C'.left.comp (C.sectionMap - C'.sectionMap) + h := by
  ext q
  change C'.left (C.sectionMap q + f (h q) - C'.sectionMap q) =
    C'.left (C.sectionMap q - C'.sectionMap q) + h q
  rw [add_sub_right_comm,map_add,C'.left_f]

end Chart
/-- Every short exact sequence with projective (in particular free) quotient lies in one of the concrete charts. This includes integral lower solutions, with no inversion of a nonunit of the full integer ring. -/
theorem chart_nonempty [Module.Projective R Q]
    (f : U →ₗ[R] V) (g : V →ₗ[R] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.ker g = LinearMap.range f) : Nonempty (Chart f g) := by
  obtain ⟨j,hj⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have gj : ∀ q, g (j q) = q := fun q => LinearMap.congr_fun hj q
  have gf : ∀ u, g (f u) = 0 := by
    intro u
    have hu : f u ∈ LinearMap.range f := ⟨u,rfl⟩
    rw [← hex] at hu
    exact hu
  let t : (U × Q) →ₗ[R] V := f.coprod j
  have ht : Function.Bijective t := by
    constructor
    · intro uq uq' h
      have hq : uq.2 = uq'.2 := by
        have e := congrArg g h
        simpa only [t,LinearMap.coprod_apply,map_add,gf,zero_add,gj] using e
      have hu : uq.1 = uq'.1 := by
        apply hf
        change f uq.1 + j uq.2 = f uq'.1 + j uq'.2 at h
        rw [hq] at h
        exact add_right_cancel h
      exact Prod.ext hu hq
    · intro v
      have hv : v - j (g v) ∈ LinearMap.ker g := by
        change g (v - j (g v)) = 0
        rw [map_sub,gj,sub_self]
      rw [hex] at hv
      obtain ⟨u,hu⟩ := hv
      refine ⟨(u,g v),?_⟩
      change f u + j (g v) = v
      rw [hu,sub_add_cancel]
  exact ⟨{
    j := j
    t := LinearEquiv.ofBijective t ht
    t_eq := fun _ => rfl
    d := LinearEquiv.refl R Q
    d_eq := fun q => (gj q).symm
    gf := gf }⟩

end IntegralCharacterVarieties.ExactSequenceChart

namespace IntegralCharacterVarieties.ExactSequenceChart
open Matrix
variable {R : Type*} [CommRing R]
variable {υ κ : Type*} [Fintype υ] [Fintype κ] [DecidableEq υ] [DecidableEq κ]


def matrixChart (F : Matrix (υ ⊕ κ) υ R) (G : Matrix κ (υ ⊕ κ) R)
    (J : Matrix (υ ⊕ κ) κ R) (hgf : G * F = 0)
    (ht : IsUnit (Matrix.fromCols F J).det) (hd : IsUnit (G * J).det) :
    Chart (Matrix.toLin' F) (Matrix.toLin' G) where
  j := Matrix.toLin' J
  t := (LinearEquiv.sumArrowLequivProdArrow υ κ R R).symm.trans
    (Matrix.toLinearEquiv (Pi.basisFun R (υ ⊕ κ)) (Matrix.fromCols F J) ht)
  t_eq uq := by
    change Matrix.toLin (Pi.basisFun R (υ ⊕ κ)) (Pi.basisFun R (υ ⊕ κ)) (Matrix.fromCols F J) (Sum.elim uq.1 uq.2) = _
    rw [Matrix.toLin_eq_toLin']
    exact Matrix.fromCols_mulVec_sumElim _ _ _ _
  d := Matrix.toLinearEquiv (Pi.basisFun R κ) (G * J) hd
  d_eq q := by
    change Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R κ) (G * J) q = G *ᵥ (J *ᵥ q)
    rw [Matrix.toLin_eq_toLin']
    exact (Matrix.mulVec_mulVec q G J).symm
  gf u := by
    change G *ᵥ (F *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec,hgf,Matrix.zero_mulVec]

end IntegralCharacterVarieties.ExactSequenceChart

namespace IntegralCharacterVarieties.ExactSequenceChart
open Matrix
variable {R : Type*} [CommRing R]
variable {υ ν κ : Type*} [Fintype υ] [Fintype ν] [Fintype κ]
  [DecidableEq υ] [DecidableEq ν] [DecidableEq κ]

/-- The five split-sequence identities, proved from each principal matrix chart below. They are preserved under arbitrary base change. -/
structure MatrixSplitData (R : Type*) [CommRing R] (υ ν κ : Type*)
    [Fintype υ] [Fintype ν] [Fintype κ] [DecidableEq υ] [DecidableEq ν] [DecidableEq κ] where
  f : Matrix ν υ R
  g : Matrix κ ν R
  l : Matrix υ ν R
  s : Matrix ν κ R
  gf : g * f = 0
  gs : g * s = 1
  lf : l * f = 1
  ls : l * s = 0
  decomposition : f * l + s * g = 1

namespace MatrixSplitData

/-- Taking coordinates of the explicitly constructed linear chart. -/
def ofChart {f : (υ → R) →ₗ[R] (ν → R)} {g : (ν → R) →ₗ[R] (κ → R)}
    (C : Chart f g) : MatrixSplitData R υ ν κ where
  f := LinearMap.toMatrix' f
  g := LinearMap.toMatrix' g
  l := LinearMap.toMatrix' C.left
  s := LinearMap.toMatrix' C.sectionMap
  gf := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro u
    exact C.gf u
  gs := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro q
    exact C.g_section q
  lf := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro u
    exact C.left_f u
  ls := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro q
    exact C.left_section q
  decomposition := by
    apply Matrix.toLin'.injective
    simp only [map_add,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro v
    exact C.decompose v

variable (D : MatrixSplitData R υ ν κ)

/-- Affine reconstruction and its coordinate readout. -/
def reconstruct (h : Matrix υ κ R) : Matrix ν κ R := D.s + D.f * h

def read (x : Matrix ν κ R) : Matrix υ κ R := D.l * x

def difference (x : Matrix ν κ R) : Matrix κ κ R := D.g * x - 1

lemma read_reconstruct (h : Matrix υ κ R) : D.read (D.reconstruct h) = h := by
  simp only [read,reconstruct,Matrix.mul_add,← Matrix.mul_assoc,D.ls,D.lf,
    Matrix.one_mul,zero_add]

lemma reconstruct_read (x : Matrix ν κ R) (hx : D.g * x = 1) :
    D.reconstruct (D.read x) = x := by
  change D.s + D.f * (D.l * x) = x
  calc
    _ = D.s * (D.g * x) + (D.f * D.l) * x := by rw [hx,Matrix.mul_one,Matrix.mul_assoc]
    _ = (D.f * D.l + D.s * D.g) * x := by
      rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_assoc,add_comm]
    _ = x := by rw [D.decomposition,Matrix.one_mul]

lemma difference_reconstruct (h : Matrix υ κ R) : D.difference (D.reconstruct h) = 0 := by
  simp only [difference,reconstruct,Matrix.mul_add,← Matrix.mul_assoc,D.gs,D.gf,
    Matrix.zero_mul,add_zero,sub_self]

variable {S : Type*} [CommRing S]

def map (φ : R →+* S) : MatrixSplitData S υ ν κ where
  f := D.f.map φ
  g := D.g.map φ
  l := D.l.map φ
  s := D.s.map φ
  gf := by
    simpa only [Matrix.map_mul,Matrix.map_zero φ (map_zero φ)] using
      congrArg (fun M => M.map φ) D.gf
  gs := by
    simpa only [Matrix.map_mul,Matrix.map_one φ (map_zero φ) (map_one φ)] using
      congrArg (fun M => M.map φ) D.gs
  lf := by
    simpa only [Matrix.map_mul,Matrix.map_one φ (map_zero φ) (map_one φ)] using
      congrArg (fun M => M.map φ) D.lf
  ls := by
    simpa only [Matrix.map_mul,Matrix.map_zero φ (map_zero φ)] using
      congrArg (fun M => M.map φ) D.ls
  decomposition := by
    simpa only [Matrix.map_mul,Matrix.map_add φ (map_add φ),
      Matrix.map_one φ (map_zero φ) (map_one φ)] using
      congrArg (fun M => M.map φ) D.decomposition

lemma reconstruct_map (φ : R →+* S) (h : Matrix υ κ R) :
    (D.reconstruct h).map φ = (D.map φ).reconstruct (h.map φ) := by
  simp only [reconstruct,map,Matrix.map_add φ (map_add φ),Matrix.map_mul]

lemma read_map (φ : R →+* S) (x : Matrix ν κ R) :
    (D.read x).map φ = (D.map φ).read (x.map φ) := by
  simp only [read,map,Matrix.map_mul]

lemma difference_map (φ : R →+* S) (x : Matrix ν κ R) :
    (D.difference x).map φ = (D.map φ).difference (x.map φ) := by
  simp only [difference,map,Matrix.map_sub φ (map_sub φ),Matrix.map_mul,
    Matrix.map_one φ (map_zero φ) (map_one φ)]

@[simp] lemma map_map {T : Type*} [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    (D.map φ).map ψ = D.map (ψ.comp φ) := rfl

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

lemma map_algHom (φ : A →ₐ[R] B) :
    (D.map (algebraMap R A)).map φ.toRingHom = D.map (algebraMap R B) := by
  rw [map_map]
  congr 1
  ext r
  exact φ.commutes r

lemma reconstruct_algHom (φ : A →ₐ[R] B) (h : Matrix υ κ A) :
    ((D.map (algebraMap R A)).reconstruct h).map φ =
      (D.map (algebraMap R B)).reconstruct (h.map φ) := by
  have e := (D.map (algebraMap R A)).reconstruct_map φ.toRingHom h
  rw [D.map_algHom φ] at e
  exact e

lemma read_algHom (φ : A →ₐ[R] B) (x : Matrix ν κ A) :
    ((D.map (algebraMap R A)).read x).map φ =
      (D.map (algebraMap R B)).read (x.map φ) := by
  have e := (D.map (algebraMap R A)).read_map φ.toRingHom x
  rw [D.map_algHom φ] at e
  exact e

lemma difference_algHom (φ : A →ₐ[R] B) (x : Matrix ν κ A) :
    ((D.map (algebraMap R A)).difference x).map φ =
      (D.map (algebraMap R B)).difference (x.map φ) := by
  have e := (D.map (algebraMap R A)).difference_map φ.toRingHom x
  rw [D.map_algHom φ] at e
  exact e

end MatrixSplitData
end IntegralCharacterVarieties.ExactSequenceChart

namespace IntegralCharacterVarieties.ExactSequenceChart.MatrixSplitData
open Matrix
variable {R : Type*} [CommRing R]
variable {υ ν κ : Type*} [Fintype υ] [Fintype ν] [Fintype κ]
  [DecidableEq υ] [DecidableEq ν] [DecidableEq κ]
variable (D : MatrixSplitData R υ ν κ)

abbrev AmbientPolynomial := MvPolynomial (ν × κ) R
abbrev FreePolynomial := MvPolynomial (υ × κ) R

def ambientVariables : Matrix ν κ (AmbientPolynomial (R := R) (ν := ν) (κ := κ)) :=
  fun i j => MvPolynomial.X (i,j)

def freeVariables : Matrix υ κ (FreePolynomial (R := R) (υ := υ) (κ := κ)) :=
  fun i j => MvPolynomial.X (i,j)

def relation (i j : κ) : AmbientPolynomial (R := R) (ν := ν) (κ := κ) :=
  (D.map (algebraMap R _)).difference ambientVariables i j

def relationIdeal : Ideal (AmbientPolynomial (R := R) (ν := ν) (κ := κ)) :=
  Ideal.span (Set.range (fun ij : κ × κ => D.relation ij.1 ij.2))

abbrev CoordinateRing := AmbientPolynomial (R := R) (ν := ν) (κ := κ) ⧸ D.relationIdeal

def coordinates : Matrix ν κ D.CoordinateRing :=
  ambientVariables.map (Ideal.Quotient.mkₐ R D.relationIdeal)

lemma coordinates_difference :
    (D.map (algebraMap R D.CoordinateRing)).difference D.coordinates = 0 := by
  have e := D.difference_algHom (Ideal.Quotient.mkₐ R D.relationIdeal) ambientVariables
  change _ = (D.map (algebraMap R D.CoordinateRing)).difference D.coordinates at e
  rw [← e]
  apply Matrix.ext
  intro i j
  change Ideal.Quotient.mkₐ R D.relationIdeal (D.relation i j) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i,j),rfl⟩)

lemma coordinates_solution :
    (D.map (algebraMap R D.CoordinateRing)).g * D.coordinates = 1 :=
  sub_eq_zero.mp D.coordinates_difference

def reconstructionPolynomials : Matrix ν κ (FreePolynomial (R := R) (υ := υ) (κ := κ)) :=
  (D.map (algebraMap R _)).reconstruct freeVariables

def polynomialToFree : AmbientPolynomial (R := R) (ν := ν) (κ := κ) →ₐ[R]
    FreePolynomial (R := R) (υ := υ) (κ := κ) :=
  MvPolynomial.aeval (fun ij => D.reconstructionPolynomials ij.1 ij.2)

@[simp] lemma polynomialToFree_variable (i : ν) (j : κ) :
    D.polynomialToFree (ambientVariables i j) = D.reconstructionPolynomials i j := by
  simp [polynomialToFree,ambientVariables]

lemma polynomialToFree_variables : ambientVariables.map D.polynomialToFree =
    D.reconstructionPolynomials := by
  apply Matrix.ext
  intro i j
  exact D.polynomialToFree_variable i j

lemma polynomialToFree_relation (i j : κ) : D.polynomialToFree (D.relation i j) = 0 := by
  have e := D.difference_algHom D.polynomialToFree ambientVariables
  rw [D.polynomialToFree_variables] at e
  have eh : (D.map (algebraMap R (FreePolynomial (R := R) (υ := υ) (κ := κ)))).difference
      D.reconstructionPolynomials = 0 :=
    (D.map (algebraMap R (FreePolynomial (R := R) (υ := υ) (κ := κ)))).difference_reconstruct
      freeVariables
  rw [eh] at e
  exact congrFun (congrFun e i) j

lemma relationIdeal_le_ker : D.relationIdeal ≤ RingHom.ker D.polynomialToFree.toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨i,j⟩,rfl⟩
  exact D.polynomialToFree_relation i j

/-- The map out of the algebra defined by all entries of GS−I. -/
def toFree : D.CoordinateRing →ₐ[R] FreePolynomial (R := R) (υ := υ) (κ := κ) :=
  Ideal.Quotient.liftₐ D.relationIdeal D.polynomialToFree
    (fun _ hp => D.relationIdeal_le_ker hp)

@[simp] lemma toFree_coordinate (i : ν) (j : κ) :
    D.toFree (D.coordinates i j) = D.reconstructionPolynomials i j :=
  D.polynomialToFree_variable i j

lemma toFree_coordinates : D.coordinates.map D.toFree = D.reconstructionPolynomials := by
  apply Matrix.ext
  intro i j
  exact D.toFree_coordinate i j

def fromFree : FreePolynomial (R := R) (υ := υ) (κ := κ) →ₐ[R] D.CoordinateRing :=
  MvPolynomial.aeval (fun ij => (D.map (algebraMap R D.CoordinateRing)).read D.coordinates ij.1 ij.2)

@[simp] lemma fromFree_variable (i : υ) (j : κ) :
    D.fromFree (freeVariables i j) =
      (D.map (algebraMap R D.CoordinateRing)).read D.coordinates i j := by
  simp [fromFree,freeVariables]

lemma fromFree_variables : freeVariables.map D.fromFree =
    (D.map (algebraMap R D.CoordinateRing)).read D.coordinates := by
  apply Matrix.ext
  intro i j
  exact D.fromFree_variable i j

lemma toFree_comp_fromFree : D.toFree.comp D.fromFree = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  change D.toFree (D.fromFree (freeVariables i j)) = freeVariables i j
  rw [fromFree_variable]
  have e := D.read_algHom D.toFree D.coordinates
  rw [D.toFree_coordinates] at e
  have eh : (D.map (algebraMap R (FreePolynomial (R := R) (υ := υ) (κ := κ)))).read
      D.reconstructionPolynomials = freeVariables :=
    (D.map (algebraMap R (FreePolynomial (R := R) (υ := υ) (κ := κ)))).read_reconstruct freeVariables
  rw [eh] at e
  exact congrFun (congrFun e i) j

lemma fromFree_reconstruction : D.reconstructionPolynomials.map D.fromFree = D.coordinates := by
  have e := D.reconstruct_algHom D.fromFree freeVariables
  rw [D.fromFree_variables] at e
  change D.reconstructionPolynomials.map D.fromFree =
    (D.map (algebraMap R D.CoordinateRing)).reconstruct
      ((D.map (algebraMap R D.CoordinateRing)).read D.coordinates) at e
  rw [e]
  exact (D.map (algebraMap R D.CoordinateRing)).reconstruct_read D.coordinates D.coordinates_solution

lemma fromFree_comp_toFree : D.fromFree.comp D.toFree = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  change D.fromFree (D.toFree (D.coordinates i j)) = D.coordinates i j
  rw [toFree_coordinate]
  exact congrFun (congrFun D.fromFree_reconstruction i) j

/-- The scheme of all right inverses, on each explicit splitting chart, is literally affine space over its base. This is a coefficient-algebra isomorphism, not merely a point-level or generic-fiber parametrization. -/
def coordinateAlgEquiv : D.CoordinateRing ≃ₐ[R] FreePolynomial (R := R) (υ := υ) (κ := κ) :=
  AlgEquiv.ofAlgHom D.toFree D.fromFree D.toFree_comp_fromFree D.fromFree_comp_toFree

end IntegralCharacterVarieties.ExactSequenceChart.MatrixSplitData

namespace IntegralCharacterVarieties.ExactSequenceChart
open Matrix
variable {R : Type*} [CommRing R]
variable {υ κ : Type*} [Fintype υ] [Fintype κ] [DecidableEq υ] [DecidableEq κ]

/-- The principal determinant charts exhaust all short exact sequences on these named free modules, over the full coefficient ring, not just a field. -/
theorem exists_principal_chart
    (F : Matrix (υ ⊕ κ) υ R) (G : Matrix κ (υ ⊕ κ) R)
    (hf : Function.Injective (Matrix.toLin' F))
    (hg : Function.Surjective (Matrix.toLin' G))
    (hex : LinearMap.ker (Matrix.toLin' G) = LinearMap.range (Matrix.toLin' F)) :
    ∃ J : Matrix (υ ⊕ κ) κ R,
      IsUnit (Matrix.fromCols F J).det ∧ IsUnit (G * J).det := by
  obtain ⟨C⟩ := chart_nonempty (Matrix.toLin' F) (Matrix.toLin' G) hf hg hex
  let D := MatrixSplitData.ofChart C
  have df : D.f = F := LinearMap.toMatrix'_toLin' F
  have dg : D.g = G := LinearMap.toMatrix'_toLin' G
  refine ⟨D.s,?_,?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := Matrix.fromRows D.l G)
    rw [Matrix.fromCols_mul_fromRows,← df,← dg]
    exact D.decomposition
  · rw [← dg,D.gs,Matrix.det_one]
    exact isUnit_one

/-- The denominator defining one principal open. -/
def chartDenominator (F : Matrix (υ ⊕ κ) υ R) (G : Matrix κ (υ ⊕ κ) R)
    (J : Matrix (υ ⊕ κ) κ R) : R := (Matrix.fromCols F J).det * (G * J).det

/-- Universal split coefficients over the principal open D(det[F,J]det(GJ)). The only equation required on the base matrices is GF=0. -/
def localizedMatrixChart (F : Matrix (υ ⊕ κ) υ R) (G : Matrix κ (υ ⊕ κ) R)
    (J : Matrix (υ ⊕ κ) κ R) (hgf : G * F = 0) :
    Chart (Matrix.toLin' (F.map (algebraMap R (Localization.Away (chartDenominator F G J)))))
      (Matrix.toLin' (G.map (algebraMap R (Localization.Away (chartDenominator F G J))))) := by
  let S := Localization.Away (chartDenominator F G J)
  let φ : R →+* S := algebraMap R S
  apply matrixChart (F.map φ) (G.map φ) (J.map φ)
  · simpa only [Matrix.map_mul,Matrix.map_zero φ (map_zero φ)] using
      congrArg (fun M => M.map φ) hgf
  · rw [← Matrix.fromCols_map]
    change IsUnit (φ.mapMatrix (Matrix.fromCols F J)).det
    rw [← RingHom.map_det]
    exact IsLocalization.Away.isUnit_of_dvd (chartDenominator F G J)
      (dvd_mul_right _ _)
  · rw [← Matrix.map_mul]
    change IsUnit (φ.mapMatrix (G * J)).det
    rw [← RingHom.map_det]
    exact IsLocalization.Away.isUnit_of_dvd (chartDenominator F G J)
      (dvd_mul_left _ _)

end IntegralCharacterVarieties.ExactSequenceChart

namespace IntegralCharacterVarieties.ExactSequenceChart
open Matrix
variable {R : Type*} [CommRing R]
variable {υ κ : Type*} [Fintype υ] [Fintype κ] [DecidableEq υ] [DecidableEq κ]

/-- Exhaustive principal-open affine-space charts for extension lifts. The equation defining the lift algebra is GS=I, with no equations discarded. -/
theorem exact_sequence_chart_trivialization
    (F : Matrix (υ ⊕ κ) υ R) (G : Matrix κ (υ ⊕ κ) R)
    (hgf : G * F = 0)
    (hf : Function.Injective (Matrix.toLin' F))
    (hg : Function.Surjective (Matrix.toLin' G))
    (hex : LinearMap.ker (Matrix.toLin' G) = LinearMap.range (Matrix.toLin' F)) :
    ∃ (J : Matrix (υ ⊕ κ) κ R) (ht : IsUnit (Matrix.fromCols F J).det)
      (hd : IsUnit (G * J).det),
      Nonempty ((MatrixSplitData.ofChart (matrixChart F G J hgf ht hd)).CoordinateRing ≃ₐ[R]
        MvPolynomial (υ × κ) R) := by
  obtain ⟨J,ht,hd⟩ := exists_principal_chart F G hf hg hex
  exact ⟨J,ht,hd,⟨(MatrixSplitData.ofChart (matrixChart F G J hgf ht hd)).coordinateAlgEquiv⟩⟩

end IntegralCharacterVarieties.ExactSequenceChart

end

end OAI
