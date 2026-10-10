import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

namespace OAI

section

noncomputable section
namespace KaplanskyConsequences
open scoped ComplexOrder
open Metric Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace ClosedStarIdeal
variable {A : Type*} [CStarAlgebra A] (I : ClosedStarIdeal A)

abbrev submodule : Submodule ℂ A := I.toNonUnitalStarSubalgebra.toSubmodule
instance : IsClosed (I.submodule : Set A) := I.closed
instance : IsClosed (I.toNonUnitalStarSubalgebra : Set A) := I.closed

def ringCon : RingCon A where
  toSetoid := I.submodule.quotientRel
  add' := by
    intro a b c d hab hcd
    rw [Submodule.quotientRel_def] at *
    simpa only [add_sub_add_comm] using I.submodule.add_mem hab hcd
  mul' := by
    intro a b c d hab hcd
    rw [Submodule.quotientRel_def] at *
    have h := I.submodule.add_mem (I.mul_mem_right (a-b) c hab) (I.mul_mem_left b (c-d) hcd)
    convert h using 1; noncomm_ring

abbrev Quotient := A ⧸ I.submodule

instance : Ring I.Quotient := inferInstanceAs (Ring I.ringCon.Quotient)

def quotientMap : A →+* I.Quotient := I.ringCon.mk'

@[simp] lemma mk_apply (a : A) : I.quotientMap a = I.submodule.mkQ a := rfl
lemma mk_surjective : Function.Surjective I.quotientMap := RingCon.mk'_surjective I.ringCon
@[simp] lemma mk_eq_zero (a : A) : I.quotientMap a = 0 ↔ a ∈ I.submodule :=
  Submodule.Quotient.mk_eq_zero I.submodule

instance : Algebra ℂ I.Quotient := Algebra.ofModule
  (fun r x y => by
    induction x using Submodule.Quotient.induction_on with | H a =>
      induction y using Submodule.Quotient.induction_on with | H b =>
        exact congrArg (Submodule.Quotient.mk (p := I.submodule)) (smul_mul_assoc r a b))
  (fun r x y => by
    induction x using Submodule.Quotient.induction_on with | H a =>
      induction y using Submodule.Quotient.induction_on with | H b =>
        exact congrArg (Submodule.Quotient.mk (p := I.submodule)) (mul_smul_comm r a b))

instance : Star I.Quotient where
  star := Quotient.map' star fun a b h => by
    rw [Submodule.quotientRel_def] at *
    change star a - star b ∈ I.toNonUnitalStarSubalgebra
    rw [← star_sub]
    exact I.toNonUnitalStarSubalgebra.star_mem' h

@[simp] lemma mk_star (a : A) : I.quotientMap (star a) = star (I.quotientMap a) := rfl

instance : StarRing I.Quotient where
  star_involutive := by
    intro x; obtain ⟨a, rfl⟩ := I.mk_surjective x
    exact congrArg I.quotientMap (star_star a)
  star_mul := by
    intro x y; obtain ⟨a, rfl⟩ := I.mk_surjective x; obtain ⟨b, rfl⟩ := I.mk_surjective y
    change I.quotientMap (star (a*b)) = I.quotientMap (star b * star a)
    rw [star_mul]
  star_add := by
    intro x y; obtain ⟨a, rfl⟩ := I.mk_surjective x; obtain ⟨b, rfl⟩ := I.mk_surjective y
    change I.quotientMap (star (a+b)) = I.quotientMap (star a + star b)
    rw [star_add]

instance : StarModule ℂ I.Quotient where
  star_smul := by
    intro r x; obtain ⟨a, rfl⟩ := I.mk_surjective x
    exact congrArg I.quotientMap (star_smul r a)

def mkStarAlgHom : A →⋆ₐ[ℂ] I.Quotient where
  __ := I.quotientMap
  commutes' r := by
    change I.quotientMap (algebraMap ℂ A r) = I.quotientMap (r • (1 : A))
    rw [Algebra.algebraMap_eq_smul_one]
  map_star' := I.mk_star

lemma norm_mk_le (a : A) : ‖I.quotientMap a‖ ≤ ‖a‖ := Submodule.Quotient.norm_mk_le I.submodule a

lemma norm_mk_lt (x : I.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, I.quotientMap a = x ∧ ‖a‖ < ‖x‖ + ε := Submodule.Quotient.norm_mk_lt x hε

instance : NormedRing I.Quotient where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨a, rfl, ha⟩ := I.norm_mk_lt x h₁
    obtain ⟨b, rfl, hb⟩ := I.norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [I.norm_mk_le a]⟩
      ⟨by linarith, by linarith [I.norm_mk_le b]⟩
    calc
      _ = ‖I.quotientMap (a*b)‖ := by rw [map_mul]
      _ ≤ ‖a‖ * ‖b‖ := (I.norm_mk_le (a*b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance : NormedAlgebra ℂ I.Quotient :=
  { Submodule.Quotient.normedSpace I.submodule ℂ, (inferInstance : Algebra ℂ I.Quotient) with }

instance : NormedStarGroup I.Quotient where
  norm_star_le x := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨a, rfl, ha⟩ := I.norm_mk_lt x hε
    calc
      ‖star (I.quotientMap a)‖ = ‖I.quotientMap (star a)‖ := rfl
      _ ≤ ‖star a‖ := I.norm_mk_le (star a)
      _ = ‖a‖ := norm_star a
      _ ≤ _ := ha.le

lemma approximate_unit_mem [Nontrivial A] (j : A) (hj : j ∈ I.submodule) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, e ∈ I.submodule ∧ 0 ≤ e ∧ ‖1-e‖ ≤ 1 ∧ ‖j*(1-e)‖ < ε := by
  let J := I.toNonUnitalStarSubalgebra
  let j' : J := ⟨j, hj⟩
  let : PartialOrder J := CStarAlgebra.spectralOrder J
  let : StarOrderedRing J := CStarAlgebra.spectralOrderedRing J
  have hu := CStarAlgebra.increasingApproximateUnit (A := J)
  have ht := hu.tendsto_mul_left j'
  have he := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e, he₀, he₁, hej⟩ := (hu.eventually_nonneg.and (hu.eventually_norm.and he)).exists
  have heA : (0 : A) ≤ (e : A) := by
    have h := @NonUnitalStarRingHom.map_le_map_of_map_star J A _
      (CStarAlgebra.spectralOrder J) _ (CStarAlgebra.spectralOrderedRing J) _ _ _ _
      (NonUnitalStarRingHom.ofClass (NonUnitalStarSubalgebraClass.subtype J)) 0 e he₀
    exact h
  have he_le : (e : A) ≤ 1 := by
    apply (IsSelfAdjoint.of_nonneg heA).le_algebraMap_norm_self.trans
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using smul_le_smul_of_nonneg_right he₁ (show (0 : A) ≤ 1 from zero_le_one)
  refine ⟨e, e.property, heA, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self (1 : A) heA)
      (sub_nonneg.mpr he_le)).trans (by rw [norm_one])
  · have hx : ‖j * (e : A) - j‖ < ε := by
      rw [dist_eq_norm] at hej
      exact hej
    simpa only [mul_sub, mul_one, norm_sub_rev] using hx

lemma norm_sq_mk_le_add [Nontrivial A] (x j : A) (hj : j ∈ I.submodule) :
    ‖I.quotientMap x‖ * ‖I.quotientMap x‖ ≤ ‖star x*x+j‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he, he₀, he₁, hej⟩ := I.approximate_unit_mem j hj hε
  let w := 1-e
  have hw : star w = w := (IsSelfAdjoint.one A |>.sub he₀.isSelfAdjoint).star_eq
  have heq : I.quotientMap (x*w) = I.quotientMap x := by
    simp only [w, map_mul, map_sub, map_one, (I.mk_eq_zero e).mpr he, sub_zero, mul_one]
  have hnorm : ‖I.quotientMap x‖ * ‖I.quotientMap x‖ ≤ ‖x*w‖ * ‖x*w‖ := by
    rw [← heq]
    exact mul_self_le_mul_self (norm_nonneg _) (I.norm_mk_le _)
  have hC : ‖x*w‖ * ‖x*w‖ = ‖w * (star x*x) * w‖ := by
    rw [← CStarRing.norm_star_mul_self, star_mul, hw]
    congr 1; noncomm_ring
  have hnorm₁ : ‖w * (star x*x+j) * w‖ ≤ ‖star x*x+j‖ := by
    calc
      _ ≤ ‖w‖ * ‖star x*x+j‖ * ‖w‖ :=
        (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _))
      _ ≤ 1 * ‖star x*x+j‖ * 1 := by gcongr
      _ = _ := by ring
  have hnorm₂ : ‖w*j*w‖ ≤ ‖j*w‖ := by
    rw [mul_assoc]
    exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) he₁)
  calc
    _ ≤ ‖w * (star x*x) * w‖ := hnorm.trans_eq hC
    _ = ‖w * (star x*x+j) * w - w*j*w‖ := by congr 1; noncomm_ring
    _ ≤ ‖w * (star x*x+j) * w‖ + ‖w*j*w‖ := norm_sub_le ..
    _ ≤ ‖star x*x+j‖ + ε := add_le_add hnorm₁ (hnorm₂.trans hej.le)

instance [Nontrivial A] : CStarRing I.Quotient where
  norm_mul_self_le x := by
    obtain ⟨a, rfl⟩ := I.mk_surjective x
    rw [← I.mk_star, ← map_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hnorm⟩ := I.norm_mk_lt (I.quotientMap (star a*a)) hε
    have hj : b - star a*a ∈ I.submodule := by
      apply (I.mk_eq_zero _).mp
      rw [map_sub, hb, sub_self]
    have h := I.norm_sq_mk_le_add a (b-star a*a) hj
    have he : star a*a + (b-star a*a) = b := by abel
    rw [he] at h
    exact h.trans hnorm.le

instance quotientCStarAlgebra [Nontrivial A] : CStarAlgebra I.Quotient where

example : CompleteSpace I.Quotient := inferInstance

end ClosedStarIdeal
end KaplanskyConsequences
end
end

end OAI
