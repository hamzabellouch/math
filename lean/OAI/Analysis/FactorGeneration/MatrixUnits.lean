import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

structure MatrixUnitSystem (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Ring A] [StarRing A] [Algebra ℂ A] where
  entry : ι → ι → A
  star_entry : ∀ i j, star (entry i j) = entry j i
  mul_entry : ∀ i j k l, entry i j * entry k l = if j = k then entry i l else 0
  total : ∑ i, entry i i = 1

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

def linearMap : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun a := ∑ i, ∑ j, a i j • E.entry i j
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem linearMap_apply (a : Matrix ι ι ℂ) :
    E.linearMap a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem linearMap_single (i j : ι) (c : ℂ) :
    E.linearMap (Matrix.single i j c) = c • E.entry i j := by
  simp [linearMap_apply, Matrix.single, ite_smul, ite_and]

theorem linearMap_one : E.linearMap 1 = 1 := by
  simpa [linearMap_apply, Matrix.one_apply, ite_smul] using E.total

theorem linearMap_mul (a b : Matrix ι ι ℂ) :
    E.linearMap (a*b) = E.linearMap a * E.linearMap b := by
  simp only [linearMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul, E.mul_entry]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun k i => ∑ l, (a i k * b k l) • E.entry i l)]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

variable [StarModule ℂ A]

theorem linearMap_star (a : Matrix ι ι ℂ) :
    E.linearMap (star a) = star (E.linearMap a) := by
  simp only [linearMap_apply, star_sum, star_smul, E.star_entry]
  rw [Finset.sum_comm]
  rfl

def hom : Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun := E.linearMap
  map_one' := E.linearMap_one
  map_mul' := E.linearMap_mul
  map_zero' := E.linearMap.map_zero
  map_add' := E.linearMap.map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, E.linearMap.map_smul, E.linearMap_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := E.linearMap_star

@[simp] theorem hom_apply (a : Matrix ι ι ℂ) :
    E.hom a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem hom_single (i j : ι) (c : ℂ) :
    E.hom (Matrix.single i j c) = c • E.entry i j := E.linearMap_single i j c

theorem sandwich (a : Matrix ι ι ℂ) (o i j : ι) :
    E.entry o i * E.hom a * E.entry j o = a i j • E.entry o o := by
  simp only [hom_apply, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    E.mul_entry, smul_ite, smul_zero]
  simp [E.mul_entry, smul_ite]

theorem hom_injective (o : ι) (ho : E.entry o o ≠ 0) : Function.Injective E.hom := by
  intro a b hab
  ext i j
  have h := congrArg (fun x => E.entry o i*x*E.entry j o) hab
  rw [E.sandwich, E.sandwich] at h
  exact (smul_left_injective ℂ ho) h

def algebra : StarSubalgebra ℂ A := E.hom.range

theorem mem_algebra (x : A) : x ∈ E.algebra ↔
    ∃ a : Matrix ι ι ℂ, (∑ i, ∑ j, a i j • E.entry i j) = x := Iff.rfl

theorem entry_mem (i j : ι) : E.entry i j ∈ E.algebra := by
  exact ⟨Matrix.single i j 1, (E.hom_single i j 1).trans (one_smul _ _)⟩

def equiv (o : ι) (ho : E.entry o o ≠ 0) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] E.algebra :=
  StarAlgEquiv.ofInjective E.hom (E.hom_injective o ho)

instance algebra_finiteDimensional : FiniteDimensional ℂ E.algebra := by
  change FiniteDimensional ℂ E.hom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.hom.toAlgHom.rangeRestrict.toLinearMap
    E.hom.toAlgHom.rangeRestrict_surjective

theorem algebra_isClosed [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousSMul ℂ A] [T2Space A] : IsClosed (E.algebra : Set A) := by
  let : FiniteDimensional ℂ E.algebra.toSubalgebra.toSubmodule := E.algebra_finiteDimensional
  exact E.algebra.toSubalgebra.toSubmodule.closed_of_finiteDimensional

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_ne_zero [Nontrivial A] (o : ι) : E.entry o o ≠ 0 := by
  intro h
  have hz (i : ι) : E.entry i i = 0 := by
    have hio : E.entry i o = 0 := by
      have hm := E.mul_entry i o o o
      simpa [h] using hm.symm
    have hm := E.mul_entry i o o i
    simpa [hio] using hm.symm
  have ht := E.total
  simp only [hz, Finset.sum_const_zero] at ht
  exact zero_ne_one ht

theorem injective [Nontrivial A] [Nonempty ι] : Function.Injective E.hom :=
  E.hom_injective (Classical.arbitrary ι) (E.diagonal_ne_zero _)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

theorem commute_algebra_iff (x : A) :
    (∀ a ∈ E.algebra, Commute a x) ↔ ∀ i j, Commute (E.entry i j) x := by
  constructor
  · exact fun h i j => h _ (E.entry_mem i j)
  · intro h a ha
    obtain ⟨b,rfl⟩ := (E.mem_algebra a).mp ha
    show (∑ i, ∑ j, b i j • E.entry i j)*x=x*(∑ i, ∑ j, b i j • E.entry i j)
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      (h _ _).eq]

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

def product : MatrixUnitSystem (ι × κ) A where
  entry a b := E.entry a.1 b.1 * F.entry a.2 b.2
  star_entry a b := by
    rw [star_mul,E.star_entry,F.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry a b c d := by
    have hr : (E.entry a.1 b.1*F.entry a.2 b.2)*(E.entry c.1 d.1*F.entry c.2 d.2)=
        (E.entry a.1 b.1*E.entry c.1 d.1)*(F.entry a.2 b.2*F.entry c.2 d.2) := by
      calc _ = E.entry a.1 b.1*(F.entry a.2 b.2*E.entry c.1 d.1)*F.entry c.2 d.2 := by
              simp only [mul_assoc]
           _ = _ := by rw [(hc c.1 d.1 a.2 b.2).eq.symm]; simp only [mul_assoc]
    rw [hr,E.mul_entry,F.mul_entry]
    by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2 <;>
      simp [h1,h2,Prod.ext_iff]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,F.total,mul_one,E.total]

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

omit [StarModule ℂ A] in
theorem product_sum_right (k l : κ) :
    (∑ i, (E.product F hc).entry (i,k) (i,l)) = F.entry k l := by
  simp only [product_entry, ← Finset.sum_mul, E.total, one_mul]

theorem algebra_le_product_left : E.algebra ≤ (E.product F hc).algebra := by
  apply (E.algebra_le_iff _).mpr
  intro i j
  rw [← E.product_sum_left F hc i j]
  exact (E.product F hc).algebra.sum_mem fun k _ => (E.product F hc).entry_mem _ _

theorem algebra_le_product_right : F.algebra ≤ (E.product F hc).algebra := by
  apply (F.algebra_le_iff _).mpr
  intro k l
  rw [← E.product_sum_right F hc k l]
  exact (E.product F hc).algebra.sum_mem fun i _ => (E.product F hc).entry_mem _ _

theorem product_algebra_eq_sup : (E.product F hc).algebra = E.algebra ⊔ F.algebra := by
  apply le_antisymm
  · apply ((E.product F hc).algebra_le_iff _).mpr
    intro a b
    exact (E.algebra ⊔ F.algebra).mul_mem ((show E.algebra ≤ E.algebra ⊔ F.algebra from le_sup_left) (E.entry_mem a.1 b.1))
      ((show F.algebra ≤ E.algebra ⊔ F.algebra from le_sup_right) (F.entry_mem a.2 b.2))
  · exact sup_le (E.algebra_le_product_left F hc) (E.algebra_le_product_right F hc)

omit [StarModule ℂ A] in
theorem diagonal_sum_retained (c : ι → ℂ) :
    (∑ a : ι × κ, c a.1 • (E.product F hc).entry a a) = ∑ i, c i • E.entry i i := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ k, c i • (E.product F hc).entry (i,k) (i,k)) = _
  rw [← Finset.smul_sum, E.product_sum_left]

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def commutant : StarSubalgebra ℂ A where
  carrier := {x | ∀ i j, Commute (E.entry i j) x}
  zero_mem' := by intro i j; exact Commute.zero_right _
  one_mem' := by intro i j; exact Commute.one_right _
  add_mem' hx hy := fun i j => (hx i j).add_right (hy i j)
  mul_mem' hx hy := fun i j => (hx i j).mul_right (hy i j)
  algebraMap_mem' c := fun i j => (Algebra.commutes c _).symm
  star_mem' hx := by
    intro i j
    show E.entry i j*star _=star _*E.entry i j
    simpa only [star_mul,E.star_entry] using (congrArg star (hx j i).eq).symm

theorem mem_commutant (x : A) : x ∈ E.commutant ↔ ∀ i j, Commute (E.entry i j) x := Iff.rfl

def amplify (o : ι) (x : A) : A := ∑ i, E.entry i o*x*E.entry o i

omit [StarModule ℂ A] in
theorem entry_mul_amplify (o i j : ι) (x : A) :
    E.entry i j * E.amplify o x = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.mul_sum,← mul_assoc,E.mul_entry]
  simp [ite_mul]

omit [StarModule ℂ A] in
theorem amplify_mul_entry (o i j : ι) (x : A) :
    E.amplify o x * E.entry i j = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.sum_mul,mul_assoc,E.mul_entry]
  simp [mul_ite]

theorem amplify_mem (o : ι) (x : A) : E.amplify o x ∈ E.commutant := by
  intro i j
  show E.entry i j * E.amplify o x = E.amplify o x * E.entry i j
  rw [E.entry_mul_amplify,E.amplify_mul_entry]

omit [StarModule ℂ A] in
theorem amplify_star (o : ι) (x : A) : star (E.amplify o x)=E.amplify o (star x) := by
  simp only [amplify,star_sum,star_mul,E.star_entry,mul_assoc]

omit [StarModule ℂ A] in
theorem amplify_zero (o : ι) : E.amplify o 0=0 := by simp [amplify]

omit [StarModule ℂ A] in
theorem amplify_corner (o i j : ι) (x : A) :
    E.entry i o*E.amplify o x*E.entry o j = E.entry i o*x*E.entry o j := by
  rw [E.entry_mul_amplify]
  simp only [mul_assoc,E.mul_entry,ite_true]

omit [StarModule ℂ A] in
theorem amplify_mul (o : ι) (x y : A) :
    E.amplify o x*E.amplify o y=E.amplify o (x*E.entry o o*y) := by
  simp only [amplify,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (E.entry i o*x*E.entry o i)*E.amplify o y = _
  rw [mul_assoc,E.entry_mul_amplify]
  simp only [mul_assoc]

theorem amplify_compression (o : ι) (x : A) (hx : x ∈ E.commutant) :
    E.amplify o (E.entry o o*x)=x := by
  simp only [amplify]
  calc _ = ∑ i, E.entry i i*x := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [← mul_assoc,E.mul_entry,ite_eq_left rfl,mul_assoc,← (hx o i).eq,
               ← mul_assoc,E.mul_entry,ite_eq_left rfl]
       _ = x := by rw [← Finset.sum_mul,E.total,one_mul]

omit [StarModule ℂ A] in
theorem reconstruct (o : ι) (x : A) :
    (∑ i, ∑ j, E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j)=x := by
  simp only [E.amplify_corner]
  have h (i j : ι) : E.entry i o*(E.entry o i*x*E.entry j o)*E.entry o j=
      E.entry i i*x*E.entry j j := by
    calc _ = (E.entry i o*E.entry o i)*x*(E.entry j o*E.entry o j) := by
               simp only [mul_assoc]
         _ = _ := by simp only [E.mul_entry,ite_true]
  simp only [h,← Finset.mul_sum,E.total,mul_one,← Finset.sum_mul,one_mul]

/-- The commutant of a full unital matrix algebra in a scalar-center algebra
has scalar center. The finite matrix decomposition is constructed above. -/
theorem commutant_scalar_center (o : ι)
    (hfactor : ∀ c : A, (∀ a : A,a*c=c*a) → ∃ z : ℂ,c=z • (1 : A))
    (c : E.commutant) (hc : ∀ a : E.commutant,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.commutant) := by
  obtain ⟨z,hz⟩ := hfactor c.val (by
    intro x
    have h (i j : ι) : Commute
        (E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j) c.val := by
      have hm : Commute (E.amplify o (E.entry o i*x*E.entry j o)) c.val :=
        congrArg Subtype.val (hc ⟨_,E.amplify_mem o _⟩)
      exact ((c.property i o).mul_left hm).mul_left (c.property o j)
    rw [← E.reconstruct o x]
    simp only [Finset.sum_mul,Finset.mul_sum,(h _ _).eq])
  exact ⟨z,Subtype.ext hz⟩

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

omit [StarModule ℂ A] in
theorem amplify_projection (o : ι) (q : A) (hq : IsStarProjection q)
    (hs : q*E.entry o o=q) : IsStarProjection (E.amplify o q) := by
  constructor
  · show E.amplify o q*E.amplify o q=E.amplify o q
    rw [E.amplify_mul,hs,hq.isIdempotentElem.eq]
  · show star (E.amplify o q)=E.amplify o q
    rw [E.amplify_star,hq.isSelfAdjoint.star_eq]

theorem commutant_diffuse (o : ι)
    (hdiff : ∀ p : A,IsStarProjection p → p ≠ 0 →
      ∃ q : A,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.commutant) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.commutant,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  have hpA : IsStarProjection p.val := hp.map E.commutant.subtype
  let r : A := E.entry o o*p.val
  have hr : IsStarProjection r := (E.diagonal_projection o).mul hpA (p.property o o)
  have hr0 : r ≠ 0 := by
    intro h
    have he := E.amplify_compression o p.val p.property
    rw [show E.entry o o*p.val=0 from h,E.amplify_zero] at he
    exact hp0 (Subtype.ext he.symm)
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff r hr hr0
  have hqs : q*E.entry o o=q := by
    have hre : r*E.entry o o=r := by
      dsimp [r]
      rw [mul_assoc,← (p.property o o).eq,← mul_assoc,
        (E.diagonal_projection o).isIdempotentElem.eq]
    calc q*E.entry o o = (q*r)*E.entry o o := by rw [hqr']
         _ = q*r := by rw [mul_assoc,hre]
         _ = q := hqr'
  have hsq : E.entry o o*q=q := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,E.star_entry] using congrArg star hqs
  let Q : E.commutant := ⟨E.amplify o q,E.amplify_mem o q⟩
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isIdempotentElem.eq
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isSelfAdjoint.star_eq
  have hrec : E.entry o o*Q.val*E.entry o o=q := by
    change E.entry o o*E.amplify o q*E.entry o o=q
    rw [E.amplify_corner,hsq,hqs]
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro h
    have hz : Q.val=0 := congrArg Subtype.val h
    rw [hz,mul_zero,zero_mul] at hrec
    exact hq0 hrec.symm
  · intro h
    have hz : Q.val=p.val := congrArg Subtype.val h
    rw [hz,mul_assoc,← (p.property o o).eq,← mul_assoc,
      (E.diagonal_projection o).isIdempotentElem.eq] at hrec
    exact hqr hrec.symm
  · apply Subtype.ext
    change p.val*E.amplify o q=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul]
    congr 1
    rw [mul_assoc,hsq]
    exact hrq
  · apply Subtype.ext
    change E.amplify o q*p.val=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul,hqs]
    exact congrArg (E.amplify o) hqr'

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

def map (f : A →⋆ₐ[ℂ] B) : MatrixUnitSystem ι B where
  entry i j := f (E.entry i j)
  star_entry i j := by rw [← map_star,E.star_entry]
  mul_entry i j k l := by
    rw [← map_mul,E.mul_entry]
    split <;> simp_all
  total := by rw [← map_sum,E.total,map_one]

theorem map_entry (f : A →⋆ₐ[ℂ] B) (i j : ι) : (E.map f).entry i j=f (E.entry i j) := rfl

theorem diagonal_sum_retained_right (F : MatrixUnitSystem κ A)
    (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l)) (d : κ → ℂ) :
    (∑ a : ι × κ,d a.2 • (E.product F hc).entry a a)=∑ k,d k • F.entry k k := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  change (∑ i, d k • (E.product F hc).entry (i,k) (i,k)) = _
  rw [← Finset.smul_sum,E.product_sum_right]

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def coefficientEval (a : Matrix ι ι E.commutant) : A :=
  ∑ i,∑ j,E.commutant.subtype (a i j)*E.entry i j

theorem coefficientEval_mul (a b : Matrix ι ι E.commutant) :
    E.coefficientEval (a*b)=E.coefficientEval a*E.coefficientEval b := by
  simp only [coefficientEval,Matrix.mul_apply,map_sum,map_mul,
    Finset.sum_mul,Finset.mul_sum]
  have he (i j k l : ι) :
      ((a i j).val*E.entry i j)*((b k l).val*E.entry k l)=
        (a i j).val*(b k l).val*(E.entry i j*E.entry k l) := by
    rw [mul_assoc,← mul_assoc (E.entry i j),((b k l).property i j).eq]
    simp only [mul_assoc]
  change (∑ i,∑ j,∑ k,(a i k).val*(b k j).val*E.entry i j) =
    ∑ k,∑ l,∑ i,∑ j,((a i j).val*E.entry i j)*((b k l).val*E.entry k l)
  simp only [he,E.mul_entry,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem coefficientEval_star (a : Matrix ι ι E.commutant) :
    E.coefficientEval (star a)=star (E.coefficientEval a) := by
  simp only [coefficientEval,star_sum,star_mul,E.star_entry,Matrix.star_apply,
    map_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact ((star (a i j)).property j i).eq.symm

theorem coefficientEval_one : E.coefficientEval 1=1 := by
  simpa [coefficientEval,Matrix.one_apply,apply_ite,ite_mul] using E.total

def coefficientHom : Matrix ι ι E.commutant →⋆ₐ[ℂ] A where
  toFun := E.coefficientEval
  map_one' := E.coefficientEval_one
  map_mul' := E.coefficientEval_mul
  map_zero' := by simp [coefficientEval]
  map_add' a b := by simp [coefficientEval,add_mul,Finset.sum_add_distrib]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    change E.coefficientEval (c • 1)=algebraMap ℂ A c
    simp only [coefficientEval,Matrix.smul_apply,map_smul,smul_mul_assoc,
      ← Finset.smul_sum]
    change c • E.coefficientEval 1=algebraMap ℂ A c
    rw [E.coefficientEval_one,Algebra.algebraMap_eq_smul_one]
  map_star' := E.coefficientEval_star

theorem coefficientHom_single (i j : ι) (a : E.commutant) :
    E.coefficientHom (Matrix.single i j a)=a.val*E.entry i j := by
  change E.coefficientEval (Matrix.single i j a)=_
  simp [coefficientEval,Matrix.single,apply_ite,ite_mul,ite_and]

theorem coefficientHom_surjective (o : ι) : Function.Surjective E.coefficientHom := by
  intro x
  let a : Matrix ι ι E.commutant := fun i j =>
    ⟨E.amplify o (E.entry o i*x*E.entry j o),E.amplify_mem o _⟩
  refine ⟨a,?_⟩
  change (∑ i,∑ j,E.amplify o (E.entry o i*x*E.entry j o)*E.entry i j)=x
  calc (∑ i,∑ j,E.amplify o (E.entry o i*x*E.entry j o)*E.entry i j) =
      ∑ i,∑ j,E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (a i j).val*E.entry i j=E.entry i o*(a i j).val*E.entry o j
        rw [((a i j).property i o).eq,mul_assoc,E.mul_entry,ite_eq_left rfl]
    _ = x := E.reconstruct o x

end MatrixUnitSystem

end Generator

end

end OAI
