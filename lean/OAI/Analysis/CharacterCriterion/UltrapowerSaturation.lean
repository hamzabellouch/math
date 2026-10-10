import OAI.Analysis.CharacterCriterion.DiagonalIteration

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
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.NormUltrapower
open Filter Topology BoundedContinuousFunction
open scoped CStarAlgebra
lemma map_positive {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have he : a = star (CFC.sqrt a)*CFC.sqrt a := by rw [hs,CFC.sqrt_mul_sqrt_self a ha]
  rw [he,map_mul,map_star]
  exact star_mul_self_nonneg (φ (CFC.sqrt a))
lemma unitary_lift_of_isUnit {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : IsUnit a) (u : unitary B)
    (he : φ a = (u : B)) : ∃ v : unitary A, φ (v : A) = (u : B) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hg : IsStrictlyPositive (star a*a) := ⟨star_mul_self_nonneg _,ha.star.mul ha⟩
  let r := (star a*a) ^ (-(1/2):ℝ)
  have hr : 0 ≤ r := CFC.rpow_nonneg
  have hrs : star r=r := (IsSelfAdjoint.of_nonneg hr).star_eq
  have hrunit : IsUnit r := hg.isUnit.cfcRpow _
  have hnorm : r*(star a*a)*r=1 := CFC.conjugate_rpow_neg_one_half _ hg
  have hv : a*r ∈ unitary A := (ha.mul hrunit).mem_unitary_of_star_mul_self (by
    rw [star_mul,hrs]
    calc r*star a*(a*r) = r*(star a*a)*r := by noncomm_ring
         _ = 1 := hnorm)
  have hφg : φ (star a*a)=1 := by rw [map_mul,map_star,he]; exact u.property.1
  have hφrnonneg : 0≤φ r := map_positive φ hr
  have hφr2 : (φ r)^2=1 := by
    have h := congrArg φ hnorm
    simpa only [map_mul,hφg,mul_one,map_one,pow_two] using h
  have hφr : φ r=1 := by
    calc
      φ r = CFC.sqrt ((φ r)^2) := (CFC.sqrt_sq (φ r) hφrnonneg).symm
      _ = 1 := by rw [hφr2,CFC.sqrt_one]
  exact ⟨⟨a*r,hv⟩,by change φ (a*r)=_; rw [map_mul,he,hφr,mul_one]⟩
lemma isUnit_of_two_grams {A : Type*} [CStarAlgebra A] (a : A)
    (hleft : IsUnit (star a*a)) (hright : IsUnit (a*star a)) : IsUnit a := by
  let l := Ring.inverse (star a*a)*star a
  let r := star a*Ring.inverse (a*star a)
  have hl : l*a=1 := by dsimp [l]; rw [mul_assoc,Ring.inverse_mul_cancel _ hleft]
  have hr : a*r=1 := by dsimp [r]; rw [← mul_assoc,Ring.mul_inverse_cancel _ hright]
  have he : l=r := by calc l=l*(a*r) := by rw [hr,mul_one]
                         _=(l*a)*r := (mul_assoc l a r).symm
                         _=r := by rw [hl,one_mul]
  exact ⟨⟨a,l,by rwa [he],hl⟩,rfl⟩


theorem unitary_lift {A : Type*} [CStarAlgebra A] (ω : Ultrafilter ℕ)
    (u : unitary (Algebra A ω)) :
    ∃ v : unitary (BoundedSeq A), quotientMap ω (v : BoundedSeq A) = (u : Algebra A ω) := by
  classical
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Algebra A ω)
  change quotientMap ω x=(u : Algebra A ω) at hx
  have hleft : star x*x-1 ∈ nullIdeal ω := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotientMap ω (star x*x-1)=0
    rw [map_sub,map_mul,map_star,map_one,hx,u.property.1,sub_self]
  have hright : x*star x-1 ∈ nullIdeal ω := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotientMap ω (x*star x-1)=0
    rw [map_sub,map_mul,map_star,map_one,hx,u.property.2,sub_self]
  have hl := (mem_nullIdeal ω _).mp hleft
  have hr := (mem_nullIdeal ω _).mp hright
  let good : ℕ → Prop := fun n => ‖star (x n)*x n-1‖ < 1/2 ∧ ‖x n*star (x n)-1‖ < 1/2
  have hg : ∀ᶠ n in (ω : Filter ℕ), good n := by
    exact (hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and
      (hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  let y : BoundedSeq A := ofNormedAddCommGroupDiscrete (fun n => if good n then x n else 1)
    (‖x‖+‖(1:A)‖) (fun n => by
      split_ifs
      · exact (x.norm_coe_le_norm n).trans (by linarith [norm_nonneg (1:A)])
      · exact by linarith [norm_nonneg x])
  have hxy : quotientMap ω y = quotientMap ω x := by
    apply Ideal.Quotient.eq.mpr
    apply (mem_nullIdeal ω _).mpr
    apply (tendsto_const_nhds (x := (0:ℝ))).congr'
    filter_upwards [hg] with n hn
    change (0:ℝ)=‖(if good n then x n else 1)-x n‖
    simp only [ite_eq_left hn,sub_self,norm_zero]
  have hnleft : ‖star y*y-1‖ ≤ (1/2 : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro n
    change ‖star (if good n then x n else 1)*(if good n then x n else 1)-1‖ ≤ 1/2
    split_ifs with hn
    · exact hn.1.le
    · simp
  have hnright : ‖y*star y-1‖ ≤ (1/2 : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro n
    change ‖(if good n then x n else 1)*star (if good n then x n else 1)-1‖ ≤ 1/2
    split_ifs with hn
    · exact hn.2.le
    · simp
  have hy : IsUnit y := by
    apply isUnit_of_two_grams
    · have h := isUnit_one_sub_of_norm_lt_one (x := 1-star y*y)
        (by rw [norm_sub_rev]; linarith)
      simpa only [sub_sub_cancel] using h
    · have h := isUnit_one_sub_of_norm_lt_one (x := 1-y*star y)
        (by rw [norm_sub_rev]; linarith)
      simpa only [sub_sub_cancel] using h
  exact unitary_lift_of_isUnit (quotientMap ω) y hy u (hxy.trans hx)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam.NormUltrapower
open Filter Topology BoundedContinuousFunction
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def sequenceMap (φ : A →⋆ₐ[ℂ] B) : BoundedSeq A →⋆ₐ[ℂ] BoundedSeq B where
  toFun x := ofNormedAddCommGroupDiscrete (fun n => φ (x n)) ‖x‖ (fun n =>
    (NonUnitalStarAlgHom.norm_apply_le φ (x n)).trans (x.norm_coe_le_norm n))
  map_zero' := by ext n; exact map_zero φ
  map_one' := by ext n; exact map_one φ
  map_add' x y := by ext n; exact map_add φ (x n) (y n)
  map_mul' x y := by ext n; exact map_mul φ (x n) (y n)
  commutes' r := by ext n; exact φ.commutes r
  map_star' x := by ext n; exact map_star φ (x n)
@[simp] lemma sequenceMap_apply (φ : A →⋆ₐ[ℂ] B) (x : BoundedSeq A) (n : ℕ) :
    sequenceMap φ x n = φ (x n) := rfl
lemma sequenceMap_null (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ)
    {x : BoundedSeq A} (hx : x ∈ nullIdeal ω) : sequenceMap φ x ∈ nullIdeal ω := by
  apply (mem_nullIdeal ω _).mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => NonUnitalStarAlgHom.norm_apply_le φ (x n))
  exact (mem_nullIdeal ω x).mp hx

def map (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) : Algebra A ω →⋆ₐ[ℂ] Algebra B ω where
  __ := Ideal.Quotient.liftₐ (nullIdeal ω)
    ((quotientMap ω).comp (sequenceMap φ)).toAlgHom (fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (sequenceMap_null φ ω hx))
  map_star' := by
    intro x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
    change quotientMap ω (sequenceMap φ (star y))=star (quotientMap ω (sequenceMap φ y))
    rw [map_star,map_star]
@[simp] lemma map_mk (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    map φ ω (quotientMap ω x)=quotientMap ω (sequenceMap φ x) := rfl
@[simp] lemma map_diagonal (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) (a : A) :
    map φ ω (NormUltrapower.diagonal ω a)=NormUltrapower.diagonal ω (φ a) := by
  change quotientMap ω (sequenceMap φ (constantSeq a))=quotientMap ω (constantSeq (φ a))
  congr 1

lemma eventually_norm_lt (ω : Ultrafilter ℕ) (x : BoundedSeq A) (c : ℝ)
    (h : ‖quotientMap ω x‖ < c) : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c := by
  change ‖Ideal.Quotient.mk (nullIdeal ω) x‖ < c at h
  rw [norm_mk_eq] at h
  exact (tendsto_norm ω x).eventually (gt_mem_nhds h)
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam
open Filter
open scoped Topology CStarAlgebra
namespace Intertwining
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def limitHom (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hφ : ∀ a, CauchySeq (fun n => φ n a)) : A →⋆ₐ[ℂ] B where
  toFun a := limUnder atTop (fun n => φ n a)
  map_zero' := by
    apply tendsto_nhds_unique (hφ 0).tendsto_limUnder
    simpa only [map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : B)) atTop (𝓝 0))
  map_one' := by
    apply tendsto_nhds_unique (hφ 1).tendsto_limUnder
    simpa only [map_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : B)) atTop (𝓝 1))
  map_add' a b := by
    apply tendsto_nhds_unique (hφ (a+b)).tendsto_limUnder
    simpa only [map_add] using ((hφ a).tendsto_limUnder.add (hφ b).tendsto_limUnder)
  map_mul' a b := by
    apply tendsto_nhds_unique (hφ (a*b)).tendsto_limUnder
    simpa only [map_mul] using ((hφ a).tendsto_limUnder.mul (hφ b).tendsto_limUnder)
  commutes' z := by
    apply tendsto_nhds_unique (hφ (algebraMap ℂ A z)).tendsto_limUnder
    have he : (fun n => φ n (algebraMap ℂ A z)) =
        (fun _ : ℕ => algebraMap ℂ B z) := funext (fun n => (φ n).commutes z)
    rw [he]
    exact tendsto_const_nhds
  map_star' a := by
    apply tendsto_nhds_unique (hφ (star a)).tendsto_limUnder
    simpa only [map_star] using (hφ a).tendsto_limUnder.star
lemma tendsto_limitHom (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hφ : ∀ a, CauchySeq (fun n => φ n a)) (a : A) :
    Tendsto (fun n => φ n a) atTop (𝓝 (limitHom φ hφ a)) :=
  (hφ a).tendsto_limUnder

lemma diagonal_tendsto (φ : ℕ → A →⋆ₐ[ℂ] B) {x : ℕ → A} {a : A} {b : B}
    (hx : Tendsto x atTop (𝓝 a)) (hφ : Tendsto (fun n => φ n a) atTop (𝓝 b)) :
    Tendsto (fun n => φ n (x n)) atTop (𝓝 b) := by
  have h1 : Tendsto (fun n => dist (x n) a) atTop (𝓝 0) := by
    simpa using hx.dist (tendsto_const_nhds (x := a))
  have h2 : Tendsto (fun n => dist (φ n a) b) atTop (𝓝 0) := by
    simpa using hφ.dist (tendsto_const_nhds (x := b))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    (by simpa using h1.add h2)
  apply (dist_triangle (φ n (x n)) (φ n a) b).trans
  apply add_le_add _ le_rfl
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (φ n) (x n-a)
end Intertwining


theorem approximate_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : ℕ → A →⋆ₐ[ℂ] B) (ψ : ℕ → B →⋆ₐ[ℂ] A)
    (hφ : ∀ a, CauchySeq (fun n => φ n a))
    (hψ : ∀ b, CauchySeq (fun n => ψ n b))
    (hA : ∀ a, Tendsto (fun n => ψ n (φ n a)) atTop (𝓝 a))
    (hB : ∀ b, Tendsto (fun n => φ n (ψ n b)) atTop (𝓝 b)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  let f := Intertwining.limitHom φ hφ
  let g := Intertwining.limitHom ψ hψ
  have hgf : Function.LeftInverse g f := fun a =>
    tendsto_nhds_unique (Intertwining.diagonal_tendsto ψ
      (Intertwining.tendsto_limitHom φ hφ a)
      (Intertwining.tendsto_limitHom ψ hψ (f a))) (hA a)
  have hfg : Function.RightInverse g f := fun b =>
    tendsto_nhds_unique (Intertwining.diagonal_tendsto φ
      (Intertwining.tendsto_limitHom ψ hψ b)
      (Intertwining.tendsto_limitHom φ hφ (g b))) (hB b)
  exact ⟨StarAlgEquiv.ofBijective f ⟨hgf.injective,hfg.surjective⟩⟩
end KirchbergRordam
end

end OAI
