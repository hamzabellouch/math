import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
open Filter Metric
open scoped Topology ENNReal

namespace NonunitalClosedIdeal

structure Ideal (D : Type*) [NonUnitalCStarAlgebra D] where
  module : Submodule ℂ D
  mul_left : ∀ a b, b ∈ module → a*b ∈ module
  mul_right : ∀ a b, a ∈ module → a*b ∈ module
  star_mem : ∀ a, a ∈ module → star a ∈ module
  closed : IsClosed (module : Set D)

variable {D : Type*} [NonUnitalCStarAlgebra D] (J : Ideal D)
instance : IsClosed (J.module : Set D) := J.closed

def ringCon : RingCon D where
  toSetoid := J.module.quotientRel
  add' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    convert J.module.add_mem hxy huv using 1; abel
  mul' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    have h := J.module.add_mem (J.mul_right _ u hxy)
      (J.mul_left y _ huv)
    convert h using 1; noncomm_ring

def QuotientAlgebra := (ringCon J).Quotient
namespace QuotientAlgebra
instance : NonUnitalRing (QuotientAlgebra J) :=
  inferInstanceAs (NonUnitalRing (ringCon J).Quotient)
instance : NormedAddCommGroup (QuotientAlgebra J) :=
  inferInstanceAs (NormedAddCommGroup (D ⧸ J.module))
instance : Module ℂ (QuotientAlgebra J) :=
  inferInstanceAs (Module ℂ (D ⧸ J.module))
instance : NormedSpace ℂ (QuotientAlgebra J) :=
  inferInstanceAs (NormedSpace ℂ (D ⧸ J.module))
instance : CompleteSpace (QuotientAlgebra J) :=
  inferInstanceAs (CompleteSpace (D ⧸ J.module))

def mk (x : D) : QuotientAlgebra J := Submodule.Quotient.mk x
@[simp] lemma mk_add (x y : D) : mk J (x+y) = mk J x+mk J y := rfl
@[simp] lemma mk_mul (x y : D) : mk J (x*y) = mk J x*mk J y := rfl
@[simp] lemma mk_sub (x y : D) : mk J (x-y) = mk J x-mk J y := rfl
@[simp] lemma mk_smul (c : ℂ) (x : D) : mk J (c • x) = c • mk J x := rfl
@[simp] lemma mk_zero : mk J (0 : D) = 0 := rfl
lemma mk_surjective : Function.Surjective (mk J) := Quotient.mk_surjective
lemma mk_eq_mk_iff (x y : D) : mk J x = mk J y ↔ x-y ∈ J.module :=
  Submodule.Quotient.eq _
lemma norm_mk_le (x : D) : ‖mk J x‖ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le _ _
lemma exists_norm_mk_lt (x : QuotientAlgebra J) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D, mk J a = x ∧ ‖a‖ < ‖x‖+ε := Submodule.Quotient.norm_mk_lt x hε

instance : NonUnitalNormedRing (QuotientAlgebra J) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have h := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at h
    obtain ⟨ε₁, ε₂, ⟨h₁,h₂⟩, h⟩ := h
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt J x h₁
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt J y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le J a]⟩
      ⟨by linarith, by linarith [norm_mk_le J b]⟩
    exact ((norm_mk_le J (a*b)).trans (norm_mul_le a b)).trans (sub_lt_iff_lt_add'.mp h.1).le

instance : Star (QuotientAlgebra J) := ⟨Quotient.map' star (by
  intro x y h
  change (J.module).quotientRel x y at h
  change (J.module).quotientRel (star x) (star y)
  rw [Submodule.quotientRel_def] at h ⊢
  simpa only [star_sub] using J.star_mem _ h)⟩
@[simp] lemma mk_star (x : D) : mk J (star x) = star (mk J x) := rfl
instance : StarRing (QuotientAlgebra J) where
  star_involutive := by
    intro x
    obtain ⟨x,rfl⟩ := mk_surjective J x
    exact congrArg (mk J) (star_star x)
  star_mul := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective J x
    obtain ⟨y,rfl⟩ := mk_surjective J y
    exact congrArg (mk J) (star_mul x y)
  star_add := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective J x
    obtain ⟨y,rfl⟩ := mk_surjective J y
    exact congrArg (mk J) (star_add x y)
instance : StarModule ℂ (QuotientAlgebra J) where
  star_smul := by
    intro c x
    obtain ⟨x,rfl⟩ := mk_surjective J x
    exact congrArg (mk J) (star_smul c x)
instance : IsScalarTower ℂ (QuotientAlgebra J) (QuotientAlgebra J) where
  smul_assoc := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective J x
    obtain ⟨y,rfl⟩ := mk_surjective J y
    exact congrArg (mk J) (smul_mul_assoc c x y)
instance : SMulCommClass ℂ (QuotientAlgebra J) (QuotientAlgebra J) where
  smul_comm := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective J x
    obtain ⟨y,rfl⟩ := mk_surjective J y
    exact congrArg (mk J) (smul_comm c x y)

def mkHom : D →⋆ₙₐ[ℂ] QuotientAlgebra J where
  toFun := mk J
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end QuotientAlgebra
end NonunitalClosedIdeal

end
end

section

noncomputable section
namespace NonunitalClosedIdeal
open Filter Topology
open scoped ComplexOrder

variable {D : Type*} [NonUnitalCStarAlgebra D] (J : Ideal D)

def idealStarAlgebra : NonUnitalStarSubalgebra ℂ D where
  carrier := J.module
  zero_mem' := J.module.zero_mem
  add_mem' := J.module.add_mem
  mul_mem' {x y} _ hy := J.mul_left x y hy
  smul_mem' c _ hx := J.module.smul_mem c hx
  star_mem' := J.star_mem _

instance : CompleteSpace (idealStarAlgebra J) := J.closed.completeSpace_coe
instance : NonUnitalCStarAlgebra (idealStarAlgebra J) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.1
instance : PartialOrder (idealStarAlgebra J) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (idealStarAlgebra J) := CStarAlgebra.spectralOrderedRing _

def idealInclusion : idealStarAlgebra J →⋆ₙₐ[ℂ] D where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma exists_ideal_contraction {w : D} (hw : w ∈ J.module) {ε : ℝ} (hε : 0<ε) :
    ∃ e : D, e ∈ J.module ∧ IsSelfAdjoint e ∧
      ‖(1:Unitization ℂ D)-Unitization.inr e‖≤1 ∧ ‖w-w*e‖<ε := by
  let W : idealStarAlgebra J := ⟨w,hw⟩
  let hl := CStarAlgebra.increasingApproximateUnit (idealStarAlgebra J)
  have heps := Metric.tendsto_nhds.mp (hl.tendsto_mul_left W) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  let f := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp (idealInclusion J)
  have hE : 0≤f e := map_nonneg f hp
  have hEn : ‖f e‖≤1 := by
    change ‖(Unitization.inr e.1 : Unitization ℂ D)‖≤1
    rw [Unitization.norm_inr]
    exact hn
  have hE1 : f e≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hE).mp hEn
  refine ⟨e.1,e.2,congrArg Subtype.val hp.isSelfAdjoint,?_,?_⟩
  · exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1-f e) (sub_nonneg.mpr hE1)).mpr (sub_le_self _ hE)
  · change dist (W*e) W<ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖<ε at hm
    rwa [norm_sub_rev] at hm

namespace QuotientAlgebra
lemma quotient_norm_square_le (x : QuotientAlgebra J) : ‖x‖*‖x‖≤‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := mk_surjective J x
  obtain ⟨v,hv,hvn⟩ := exists_norm_mk_lt J (star (mk J u)*mk J u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.module := by
    have h : mk J w=mk J 0 := by simp only [w,mk_sub,mk_mul,mk_star,hv,mk_zero,sub_self]
    simpa only [sub_zero] using (mk_eq_mk_iff J w 0).mp h
  obtain ⟨e,he,hes,hen,hwe⟩ := exists_ideal_contraction J hw (half_pos hε)
  have heq : mk J e=0 := by
    change mk J e=mk J 0
    exact (mk_eq_mk_iff J e 0).mpr (by simpa using he)
  have hmap : mk J (u-u*e)=mk J u := by simp only [mk_sub,mk_mul,heq,mul_zero,sub_zero]
  have hun := norm_mk_le J (u-u*e)
  rw [hmap] at hun
  let E : Unitization ℂ D := 1-Unitization.inr e
  let U : Unitization ℂ D := Unitization.inr u
  let V : Unitization ℂ D := Unitization.inr v
  let W : Unitization ℂ D := Unitization.inr w
  have hestar : star E=E := by simp only [E,star_sub,star_one,←Unitization.inr_star,hes.star_eq]
  have hU : U*E=Unitization.inr (u-u*e) := by
    simp only [U,E,mul_sub,mul_one,Unitization.inr_sub,Unitization.inr_mul]
  have hW : W*E=Unitization.inr (w-w*e) := by
    simp only [W,E,mul_sub,mul_one,Unitization.inr_sub,Unitization.inr_mul]
  have hidentity : star (U*E)*(U*E)=E*V*E+E*(W*E) := by
    simp only [star_mul,hestar,V,W,w,Unitization.inr_sub,Unitization.inr_mul,Unitization.inr_star]
    change E*star U*(U*E)=E*Unitization.inr v*E+E*((star U*U-Unitization.inr v)*E)
    noncomm_ring
  have hterm1 : ‖E*V*E‖≤‖v‖ := by
    calc
      _ ≤ ‖E‖*‖V‖*‖E‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖V‖*1 := by gcongr
      _ = ‖v‖ := by simp only [one_mul,mul_one,V,Unitization.norm_inr]
  have hterm2 : ‖E*(W*E)‖<ε/2 := calc
    _ ≤ ‖E‖*‖W*E‖ := norm_mul_le _ _
    _ ≤ 1*‖W*E‖ := by gcongr
    _ < ε/2 := by simpa only [one_mul,hW,Unitization.norm_inr] using hwe
  calc
    _ ≤ ‖u-u*e‖*‖u-u*e‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖U*E‖*‖U*E‖ := by rw [hU,Unitization.norm_inr]
    _ = ‖star (U*E)*(U*E)‖ := (CStarRing.norm_star_mul_self (x := U*E)).symm
    _ ≤ ‖E*V*E‖+‖E*(W*E)‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (mk J u)*mk J u‖+ε := by linarith

instance : NonUnitalCStarAlgebra (QuotientAlgebra J) where
  norm_mul_self_le := quotient_norm_square_le J

end QuotientAlgebra
end NonunitalClosedIdeal

end
end

end OAI
