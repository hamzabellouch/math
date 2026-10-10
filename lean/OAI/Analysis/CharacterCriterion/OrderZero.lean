import OAI.Analysis.CharacterCriterion.FlipPath

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


structure WeightedUnits (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] [PartialOrder A] where
  h : A
  x : ι → ι → A
  nonneg : 0 ≤ h
  norm_le : ‖h‖ ≤ 1
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j * x k l = if j = k then h * x i l else 0
  diagonal : ∑ i, x i i = h

namespace WeightedUnits
variable (W : WeightedUnits ι A)
omit [StarOrderedRing A] in
omit instSize in
lemma commute_h.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i j : ι) : Commute (W.x i j) W.h := by
  change W.x i j * W.h = W.h * W.x i j
  conv_lhs => rw [← W.diagonal, Finset.mul_sum]
  simp only [W.mul_x]
  simp

omit instSize in
lemma column_sum.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i : ι) : ∑ j, star (W.x i j) * W.x i j = star W.h * W.h := by
  simp only [W.star_x, W.mul_x, ite_true, ← Finset.mul_sum, W.diagonal,
    (IsSelfAdjoint.of_nonneg W.nonneg).star_eq]

lemma norm_mul_le (i j : ι) (z : A) : ‖W.x i j * z‖ ≤ ‖W.h * z‖ := by
  have he : ∑ k, star (W.x i k * z) * (W.x i k * z) = star (W.h * z) * (W.h * z) := by
    simp only [star_mul]
    calc
      _ = star z * (∑ k, star (W.x i k) * W.x i k) * z := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = _ := by rw [W.column_sum]; noncomm_ring
  have hl : star (W.x i j * z) * (W.x i j * z) ≤ star (W.h * z) * (W.h * z) := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (W.x i k * z)) (Finset.mem_univ j)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hl (star_mul_self_nonneg _)
  simp only [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (W.x i j * z), norm_nonneg (W.h * z)]


def linear : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun m := ∑ i, ∑ j, m i j • W.x i j
  map_add' m n := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum, smul_smul]

omit [StarOrderedRing A] in
omit instSize in
@[simp] lemma linear_single.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i j : ι) (z : ℂ) :
    W.linear (Matrix.single i j z) = z • W.x i j := by
  simp [linear, Matrix.single, ite_and]

omit [StarOrderedRing A] in
omit instSize in
lemma linear_one.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    : W.linear 1 = W.h := by
  simpa [linear, Matrix.one_apply] using W.diagonal

omit [StarOrderedRing A] in
omit instSize in
lemma linear_star.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (m : Matrix ι ι ℂ) : W.linear (star m) = star (W.linear m) := by
  simp only [linear, LinearMap.coe_mk, AddHom.coe_mk, star_sum, star_smul, W.star_x]
  exact Finset.sum_comm

omit [StarOrderedRing A] in
lemma linear_mul (m n : Matrix ι ι ℂ) :
    W.linear m * W.linear n = W.h * W.linear (m*n) := by
  induction m using Matrix.induction_on' with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [add_mul,map_add,mul_add,hm,hm']
  | h_std_basis i j z =>
    induction n using Matrix.induction_on' with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [mul_add,map_add,hn,hn']
    | h_std_basis k l w =>
      by_cases hjk : j=k
      · subst k
        rw [Matrix.single_mul_single_same,W.linear_single,W.linear_single,W.linear_single]
        simp [smul_smul,W.mul_x,mul_comm]
      · rw [Matrix.single_mul_single_of_ne (h := hjk)]
        simp [hjk,W.mul_x]

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)

omit [Fintype ι] in
omit hs in
omit instSize in
lemma copy_norm.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {ι : Type contextLevel2}
    [DecidableEq ι]
    {a : A}
    (s : ι → A)
    (hs : ∀ (i j : ι), Star.star (s i) * s j = if i = j then Star.star a * a else 0)
    (i : ι) : star a*a=star (s i)*s i := by rw [hs]; simp

def copy (i : ι) : corner a ha →⋆ₙₐ[ℂ] A := hom ha (copy_norm s hs i)

omit [Fintype ι] in
lemma copy_embed (i : ι) (x : A) : copy ha s hs i (embed a ha x)=s i*x*star (s i) :=
  conjugate_embed ha (copy_norm s hs i) x

omit [Fintype ι] in
lemma continuous_copy (i : ι) : Continuous (copy ha s hs i) :=
  continuous_conjugate ha (copy_norm s hs i)

omit [Fintype ι] in
lemma copy_orthogonal {i j : ι} (hij : i≠j) (x y : corner a ha) :
    copy ha s hs i x*copy ha s hs j y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_copy ha s hs i).comp continuous_fst).mul
      ((continuous_copy ha s hs j).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [copy_embed,copy_embed]
  calc
    _=s i*x*(star (s i)*s j)*y*star (s j) := by noncomm_ring
    _=0 := by simp [hs,hij]


def copies : corner a ha →⋆ₙₐ[ℂ] A where
  toFun x := ∑ i,copy ha s hs i x
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]
  map_star' x := by simp only [map_star,star_sum]
  map_mul' x y := by
    simp only [map_mul,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_eq_single i
    · intro j _ hij
      exact copy_orthogonal ha s hs hij x y
    · simp

lemma continuous_copies : Continuous (copies ha s hs) :=
  continuous_finsetSum _ fun i _ => continuous_copy ha s hs i

lemma copies_orthogonal (hz : ∀ i, a*s i=0) (x y : corner a ha) :
    (x : A)*copies ha s hs y=0 := by
  change (x:A)*(∑ i,copy ha s hs i y)=0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  refine (dense a ha).induction_on₂ (isClosed_eq
    (continuous_subtype_val.comp continuous_fst |>.mul
      ((continuous_copy ha s hs i).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [copy_embed]
  change (a*x*a)*(s i*y*star (s i))=0
  calc
    _=a*x*(a*s i)*y*star (s i) := by noncomm_ring
    _=0 := by rw [hz]; simp


lemma copies_commute (m : ι → ι → A) (hm : ∀ i j, star (m i j)=m j i)
    (hms : ∀ j k i, m j k*s i=if k=i then s j else 0)
    (j k : ι) (x : corner a ha) : Commute (m j k) (copies ha s hs x) := by
  change m j k*copies ha s hs x=copies ha s hs x*m j k
  refine (dense a ha).induction_on x (isClosed_eq
    (continuous_const.mul (continuous_copies ha s hs))
    ((continuous_copies ha s hs).mul continuous_const)) ?_
  intro x
  have hr (i : ι) : star (s i)*m j k=if j=i then star (s k) else 0 := by
    calc
      _=star (m k j*s i) := by rw [star_mul,hm]
      _=_ := by rw [hms]; split_ifs <;> simp
  change m j k*(∑ i,copy ha s hs i (embed a ha x))=
    (∑ i,copy ha s hs i (embed a ha x))*m j k
  simp only [copy_embed,Finset.mul_sum,Finset.sum_mul]
  calc
    _=∑ i,(m j k*s i)*x*star (s i) := by
      apply Finset.sum_congr rfl; intro i _; noncomm_ring
    _=s j*x*star (s k) := by simp [hms]
    _=∑ i,s i*x*(star (s i)*m j k) := by simp [hr]
    _=_ := by apply Finset.sum_congr rfl; intro i _; noncomm_ring

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


def leftLinear (i : ι) : corner a ha →ₗ[ℂ] A where
  toFun := left (v := s i) ha
  map_add' x y := by
    change transport a (s i) ((⟨(x:A),in_space x.property⟩ : space a)+(⟨(y:A),in_space y.property⟩ : space a)) = transport a (s i) _ + transport a (s i) _
    exact map_add (transport a (s i)) _ _
  map_smul' c x := by
    change transport a (s i) (c • (⟨(x:A),in_space x.property⟩ : space a)) = c • transport a (s i) _
    exact map_smul (transport a (s i)) c _

include hs in
lemma left_cross_inner (i j : ι) (x y : corner a ha) :
    star (left (v := s i) ha x)*left (v := s j) ha y=
      if i=j then star (x:A)*(y:A) else 0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_left ha).comp continuous_fst).star.mul
      ((continuous_left ha).comp continuous_snd))
    (by split_ifs <;> fun_prop)) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j),star_mul,star_mul,ha.star_eq]
  change (a*(star x*star (s i)))*(s j*y*a)=if i=j then star (a*x*a)*(a*y*a) else 0
  calc
    _=a*star x*(star (s i)*s j)*y*a := by noncomm_ring
    _=_ := by
      rw [hs]
      split_ifs
      · simp only [ha.star_eq,star_mul]
        noncomm_ring
      · simp


def cross (i j : ι) (x : corner a ha) : A :=
  star (transport a (s j) ⟨star (left (v := s i) ha x),
    star_left_mem ha (copy_norm s hs i) x⟩)

lemma continuous_cross (i j : ι) : Continuous (cross ha s hs i j) :=
  ((transport a (s j)).continuous.comp ((continuous_left ha).star.subtype_mk _)).star

lemma cross_embed (i j : ι) (x : A) : cross ha s hs i j (embed a ha x)=s i*x*star (s j) := by
  unfold cross
  have he : star (left (v := s i) ha (embed a ha x))=a*(star x*star (s i)) := by
    rw [left_embed ha (copy_norm s hs i),star_mul,star_mul,ha.star_eq]
  change star (transport a (s j) ⟨_,_⟩)=_
  rw [show (⟨star (left (v := s i) ha (embed a ha x)),_⟩ : space a)=
    ClosedRightRange.embed a (star x*star (s i)) from Subtype.ext he]
  rw [transport_embed (copy_norm s hs j),star_mul,star_mul,star_star,star_star]

lemma cross_zero (i j : ι) : cross ha s hs i j 0=0 := by
  have hz : embed a ha (0:A)=0 := by ext; simp [HereditaryTransport.embed]
  rw [← hz,cross_embed]; simp

lemma cross_add (i j : ι) (x y : corner a ha) :
    cross ha s hs i j (x+y)=cross ha s hs i j x+cross ha s hs i j y := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_fst.add continuous_snd))
    (((continuous_cross ha s hs i j).comp continuous_fst).add
      ((continuous_cross ha s hs i j).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x+embed a ha y=embed a ha (x+y) := by
    ext; change a*x*a+a*y*a=a*(x+y)*a; noncomm_ring
  rw [he,cross_embed,cross_embed,cross_embed]
  noncomm_ring

lemma cross_smul (i j : ι) (c : ℂ) (x : corner a ha) :
    cross ha s hs i j (c • x)=c • cross ha s hs i j x := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_const_smul c))
    ((continuous_cross ha s hs i j).const_smul c)) ?_
  intro x
  have he : c • embed a ha x=embed a ha (c • x) := by
    ext; change c • (a*x*a)=a*(c • x)*a; simp only [mul_smul_comm,smul_mul_assoc]
  rw [he,cross_embed,cross_embed]
  simp only [mul_smul_comm,smul_mul_assoc]

def crossLinear (i j : ι) : corner a ha →ₗ[ℂ] A where
  toFun := cross ha s hs i j
  map_add' := cross_add ha s hs i j
  map_smul' := cross_smul ha s hs i j

lemma cross_star (i j : ι) (x : corner a ha) :
    cross ha s hs i j (star x)=star (cross ha s hs j i x) := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_cross ha s hs i j).comp continuous_star) (continuous_cross ha s hs j i).star) ?_
  intro x
  have he : star (embed a ha x)=embed a ha (star x) := by
    ext; change star (a*x*a)=a*star x*a; rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  rw [he,cross_embed,cross_embed,star_mul,star_mul,star_star]
  noncomm_ring

lemma cross_inner (i j : ι) (x y : corner a ha) :
    cross ha s hs i j (x*star y)=left (v := s i) ha x*star (left (v := s j) ha y) := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_fst.mul continuous_snd.star))
    (((continuous_left ha).comp continuous_fst).mul ((continuous_left ha).comp continuous_snd).star)) ?_ x y
  intro x y
  have he : embed a ha x*star (embed a ha y)=embed a ha (x*a*a*star y) := by
    ext; change (a*x*a)*star (a*y*a)=a*(x*a*a*star y)*a
    rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  rw [he,cross_embed,left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j),star_mul,star_mul,ha.star_eq]
  noncomm_ring

lemma cross_diagonal (i : ι) (x : corner a ha) : cross ha s hs i i x=copy ha s hs i x := rfl

include hs in
lemma left_mul (i : ι) (x y : corner a ha) :
    left (v := s i) ha (x*y)=left (v := s i) ha x*(y:A) := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_left ha).comp (continuous_fst.mul continuous_snd))
    (((continuous_left ha).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x*embed a ha y=embed a ha (x*a*a*y) := by
    ext; change (a*x*a)*(a*y*a)=a*(x*a*a*y)*a; noncomm_ring
  rw [he,left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs i)]
  change s i*(x*a*a*y)*a=(s i*x*a)*(a*y*a)
  noncomm_ring

include hs in
lemma corner_mul_left (hz : ∀ i, a*s i=0) (i : ι) (x y : corner a ha) :
    (x:A)*left (v := s i) ha y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_subtype_val.comp continuous_fst).mul ((continuous_left ha).comp continuous_snd))
    continuous_const) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i)]
  change (a*x*a)*(s i*y*a)=0
  calc
    _=a*x*(a*s i)*y*a := by noncomm_ring
    _=0 := by rw [hz]; simp

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.ClosedRightRange
variable {A : Type*} [CStarAlgebra A]
lemma transport_right {a b : A} (h : star a*a=star b*b) (x : space a) (y : A) :
    transport a b ⟨(x:A)*y,mul_right_mem x.property y⟩=transport a b x*y := by
  refine (dense a).induction_on x (isClosed_eq
    ((transport a b).continuous.comp ((continuous_subtype_val.mul continuous_const).subtype_mk _))
    ((transport a b).continuous.mul continuous_const)) ?_
  intro x
  have he : (⟨(embed a x:A)*y,mul_right_mem (embed a x).property y⟩ : space a)=embed a (x*y) :=
    Subtype.ext (mul_assoc a x y)
  rw [he,transport_embed h,transport_embed h,mul_assoc]
end KirchbergRordam.GenericRW.ClosedRightRange

namespace KirchbergRordam.GenericRW.HereditaryTransport
section
variable {A : Type*} [CStarAlgebra A] {a v : A}
variable (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)
include hv in
lemma left_mul_of_eq (x z : corner a ha) (y : A) (he : (z:A)=(x:A)*y) :
    left (v := v) ha z=left (v := v) ha x*y := by
  unfold left
  rw [show (⟨(z:A),in_space z.property⟩ : ClosedRightRange.space a)=
    ⟨(x:A)*y,ClosedRightRange.mul_right_mem (in_space x.property) y⟩ from Subtype.ext he]
  exact ClosedRightRange.transport_right hv ⟨(x:A),in_space x.property⟩ y
end

open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)

omit [Fintype ι] in
lemma copy_mul_left (j i : ι) (x y : corner a ha) :
    copy ha s hs j x*left (v := s i) ha y=
      if j=i then left (v := s i) ha (x*y) else 0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_copy ha s hs j).comp continuous_fst).mul
      ((continuous_left ha).comp continuous_snd))
    (by split_ifs; exact (continuous_left ha).comp (continuous_fst.mul continuous_snd); exact continuous_const)) ?_ x y
  intro x y
  have he : embed a ha x*embed a ha y=embed a ha (x*a*a*y) := by
    ext; change (a*x*a)*(a*y*a)=a*(x*a*a*y)*a; noncomm_ring
  rw [copy_embed,left_embed ha (copy_norm s hs i),he,left_embed ha (copy_norm s hs i)]
  calc
    _=s j*x*(star (s j)*s i)*y*a := by noncomm_ring
    _=_ := by
      rw [hs]
      split_ifs with h
      · subst j; rw [ha.star_eq]; noncomm_ring
      · simp

lemma copies_mul_left (i : ι) (x y : corner a ha) :
    copies ha s hs x*left (v := s i) ha y=left (v := s i) ha (x*y) := by
  change (∑ j,copy ha s hs j x)*left (v := s i) ha y=_
  simp only [Finset.sum_mul,copy_mul_left]
  simp

omit [Fintype ι] in
include hs in
lemma units_mul_left (m : ι → ι → A)
    (hms : ∀ j k i,m j k*s i=if k=i then s j else 0)
    (j k i : ι) (x : corner a ha) :
    m j k*left (v := s i) ha x=if k=i then left (v := s j) ha x else 0 := by
  refine (dense a ha).induction_on x (isClosed_eq
    (continuous_const.mul (continuous_left ha)) (by split_ifs; exact continuous_left ha; exact continuous_const)) ?_
  intro x
  rw [left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j)]
  calc
    _=(m j k*s i)*x*a := by noncomm_ring
    _=_ := by rw [hms]; split_ifs <;> simp

lemma left_mul_copies (hz : ∀ i,a*s i=0) (i : ι) (x y : corner a ha) :
    left (v := s i) ha x*copies ha s hs y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_left ha).comp continuous_fst).mul
      ((continuous_copies ha s hs).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i)]
  change (s i*x*a)*(∑ j,copy ha s hs j (embed a ha y))=0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero; intro j _
  rw [copy_embed]
  calc
    _=s i*x*(a*s j)*y*star (s j) := by noncomm_ring
    _=0 := by rw [hz]; simp

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


def frame (K : Matrix ι ι (corner a ha)) (i : ι) : A :=
  ∑ j,left (v := s j) ha (K j i)

include hs in
lemma frame_inner (K : Matrix ι ι (corner a ha)) (i j : ι) :
    star (frame ha s K i)*frame ha s K j=((star K*K) i j : A) := by
  unfold frame
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum,left_cross_inner ha s hs]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ r,star (K r i : A)*(K r j : A))=↑(∑ r,star (K r i)*K r j)
  exact (map_sum (corner a ha).toSubmodule.subtype (fun r => star (K r i)*K r j) Finset.univ).symm

lemma frame_total (K : Matrix ι ι (corner a ha)) :
    ∑ i,frame ha s K i*star (frame ha s K i)=
      ∑ j,∑ k,cross ha s hs j k ((K*star K) j k) := by
  unfold frame
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  calc
    _=∑ i,∑ j,∑ k,crossLinear ha s hs j k (K j i*star (K k i)) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      exact (cross_inner ha s hs j k _ _).symm
    _=∑ j,∑ k,crossLinear ha s hs j k (∑ i,K j i*star (K k i)) := by
      simp only [map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
    _=_ := rfl

lemma frame_total_diagonal (K : Matrix ι ι (corner a ha)) (h : corner a ha)
    (hK : K*star K=Matrix.diagonal (fun _ => h)) :
    ∑ i,frame ha s K i*star (frame ha s K i)=copies ha s hs h := by
  rw [frame_total ha s hs,hK]
  change (∑ j,∑ k,cross ha s hs j k (Matrix.diagonal (fun _ => h) j k))=∑ j,copy ha s hs j h
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq,cross_diagonal]
  · intro k _ hkj
    rw [Matrix.diagonal_apply_ne _ hkj.symm,cross_zero]
  · simp

include hs in
lemma corner_mul_frame (hz : ∀ i,a*s i=0) (K : Matrix ι ι (corner a ha))
    (x : corner a ha) (i : ι) : (x:A)*frame ha s K i=0 := by
  unfold frame
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => corner_mul_left ha s hs hz j x (K j i)

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def gram (s : ι → A) (h : A)
    (hs : ∀ i j, s i*star (s j)=if i=j then h else 0)
    (hn : ‖∑ i,star (s i)*s i‖ ≤ 1) : WeightedUnits ι A where
  h := ∑ i,star (s i)*s i
  x i j := star (s i)*s j
  nonneg := Finset.sum_nonneg fun i _ => star_mul_self_nonneg (s i)
  norm_le := hn
  star_x i j := by simp only [star_mul,star_star]
  mul_x i j k l := by
    have hd : (∑ r,star (s r)*s r)*(star (s i)*s l)=star (s i)*h*s l := by
      rw [Finset.sum_mul]
      calc
        _=∑ r,star (s r)*(s r*star (s i))*s l := by apply Finset.sum_congr rfl; intro r _; noncomm_ring
        _=star (s i)*h*s l := by simp [hs]
    rw [hd]
    calc
      _=star (s i)*(s j*star (s k))*s l := by noncomm_ring
      _=_ := by by_cases hjk : j=k <;> simp [hs,hjk]
  diagonal := rfl

namespace WeightedUnits

def toWeightedMatrix (W : WeightedUnits (Fin rankNum) A) : SquareZeroCone.WeightedMatrix A where
  h := W.h
  x := W.x
  h_nonneg := W.nonneg
  norm_h_le := W.norm_le
  star_x := W.star_x
  mul_x := W.mul_x
  diagonal := W.diagonal

variable [Nontrivial A]

abbrev coneHom (W : WeightedUnits (Fin rankNum) A) : ConeModel.Cone →⋆ₐ[ℂ] A := W.toWeightedMatrix.coneHom

lemma coneHom_corner (W : WeightedUnits (Fin rankNum) A) (i j : Fin rankNum) :
    W.coneHom (ConeModel.corner i j)=W.x i j := W.toWeightedMatrix.coneHom_corner i j

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {a : A} (ha : IsSelfAdjoint a) (s : Fin rankNum → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)
variable (hz : ∀ i,a*s i=0)
variable (K : Matrix (Fin rankNum) (Fin rankNum) (corner a ha))
variable (h q : corner a ha) (hq : star q=q) (hqq : q*q=h)
variable (hK : star K*K=Matrix.diagonal (fun _ => h))
variable (hK' : K*star K=Matrix.diagonal (fun _ => h))

include hs hK in
lemma frame_inner_diagonal (i j : Fin rankNum) :
    star (frame ha s K i)*frame ha s K j=if i=j then (h:A) else 0 := by
  rw [frame_inner ha s hs,hK,Matrix.diagonal_apply]
  split_ifs <;> rfl

def triple : Fin (rankNum+1) → A := Fin.lastCases (q:A) (fun i => star (frame ha s K i))

@[simp] lemma triple_last : triple ha s K q (Fin.last rankNum) = (q:A) := by simp [triple]
@[simp] lemma triple_castSucc (i : Fin rankNum) : triple ha s K q i.castSucc = star (frame ha s K i) := by simp [triple]

include hs hz hq hqq hK in
lemma triple_relations (i j : Fin (rankNum+1)) : triple ha s K q i*star (triple ha s K q j)=if i=j then (h:A) else 0 := by
  have hval : star (q:A)=(q:A) := congrArg Subtype.val hq
  have hvalq : (q:A)*(q:A)=(h:A) := congrArg Subtype.val hqq
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp [hval, hvalq]
  · simp [corner_mul_frame ha s hs hz, Ne.symm (Fin.castSucc_ne_last _)]
  · simpa only [triple_castSucc, triple_last, Fin.castSucc_ne_last, ↓reduceIte, star_mul,
      star_star, star_zero] using congrArg star (corner_mul_frame ha s hs hz K q _)
  · simp [frame_inner_diagonal ha s hs K h hK]

include hs hq hqq hK' in
lemma triple_total : ∑ i,star (triple ha s K q i)*triple ha s K q i=copies ha s hs h+(h:A) := by
  have hval : star (q:A)=(q:A) := congrArg Subtype.val hq
  have hvalq : (q:A)*(q:A)=(h:A) := congrArg Subtype.val hqq
  rw [Fin.sum_univ_castSucc]
  simp only [triple_castSucc,triple_last,star_star,hval,hvalq]
  rw [frame_total_diagonal ha s hs K h hK']


include hs hz hq hqq hK' in
lemma triple_norm (hn : ‖(h:A)‖≤1) : ‖∑ i,star (triple ha s K q i)*triple ha s K q i‖≤1 := by
  have hh : IsSelfAdjoint h := by
    rw [← hqq]
    change star (q*q)=q*q
    rw [star_mul,hq]
  have hhA : IsSelfAdjoint (h:A) := hh.map (NonUnitalStarSubalgebraClass.subtype (corner a ha))
  have hhB : IsSelfAdjoint (copies ha s hs h) := hh.map (copies ha s hs)
  rw [triple_total ha s hs K h q hq hqq hK',add_comm,
    hhA.norm_add_eq_max hhB (copies_orthogonal ha s hs hz h h)]
  apply max_le hn
  exact (NonUnitalStarAlgHom.norm_apply_le (copies ha s hs) h).trans hn

variable [PartialOrder A] [StarOrderedRing A]


def tripleUnits (hn : ‖(h:A)‖≤1) : OrderZero.WeightedUnits (Fin (rankNum+1)) A :=
  OrderZero.gram (triple ha s K q) (h:A)
    (triple_relations ha s hs hz K h q hq hqq hK)
    (triple_norm ha s hs hz K h q hq hqq hK' hn)

end KirchbergRordam.GenericRW.HereditaryTransport
end

end OAI
