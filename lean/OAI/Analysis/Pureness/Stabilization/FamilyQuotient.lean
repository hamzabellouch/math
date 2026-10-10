import OAI.Analysis.Pureness.Stabilization.BoundedFamilies
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI
noncomputable section
open scoped ENNReal Topology
open Filter Metric
namespace CuntzTrace
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]

def FamilyQuotient := (BoundedFamilies.vanishingCon (A := A)).Quotient
namespace FamilyQuotient
open BoundedFamilies
variable {A}
instance : NonUnitalRing (FamilyQuotient A) :=
  inferInstanceAs (NonUnitalRing (vanishingCon (A := A)).Quotient)
instance : NormedAddCommGroup (FamilyQuotient A) :=
  inferInstanceAs (NormedAddCommGroup (BoundedFamilies A ⧸ vanishing (A := A)))
instance : Module ℂ (FamilyQuotient A) :=
  inferInstanceAs (Module ℂ (BoundedFamilies A ⧸ vanishing (A := A)))
instance : NormedSpace ℂ (FamilyQuotient A) :=
  inferInstanceAs (NormedSpace ℂ (BoundedFamilies A ⧸ vanishing (A := A)))
instance : CompleteSpace (FamilyQuotient A) :=
  inferInstanceAs (CompleteSpace (BoundedFamilies A ⧸ vanishing (A := A)))

def mk (x : BoundedFamilies A) : FamilyQuotient A := Submodule.Quotient.mk x
@[simp] lemma mk_add (x y : BoundedFamilies A) : mk (x+y) = mk x+mk y := rfl
@[simp] lemma mk_mul (x y : BoundedFamilies A) : mk (x*y) = mk x*mk y := rfl
@[simp] lemma mk_sub (x y : BoundedFamilies A) : mk (x-y) = mk x-mk y := rfl
@[simp] lemma mk_smul (c : ℂ) (x : BoundedFamilies A) : mk (c • x) = c • mk x := rfl
@[simp] lemma mk_zero : mk (0 : BoundedFamilies A) = 0 := rfl
lemma mk_surjective : Function.Surjective (mk (A := A)) := Quotient.mk_surjective
lemma mk_eq_mk_iff (x y : BoundedFamilies A) : mk x = mk y ↔ x-y ∈ vanishing (A := A) :=
  Submodule.Quotient.eq _
lemma norm_mk_le (x : BoundedFamilies A) : ‖mk x‖ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le _ _
lemma exists_norm_mk_lt (x : FamilyQuotient A) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedFamilies A, mk a = x ∧ ‖a‖ < ‖x‖+ε := Submodule.Quotient.norm_mk_lt x hε

instance : NonUnitalNormedRing (FamilyQuotient A) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have h := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at h
    obtain ⟨ε₁, ε₂, ⟨h₁,h₂⟩, h⟩ := h
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x h₁
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le a]⟩
      ⟨by linarith, by linarith [norm_mk_le b]⟩
    exact ((norm_mk_le (a*b)).trans (norm_mul_le a b)).trans (sub_lt_iff_lt_add'.mp h.1).le

instance : Star (FamilyQuotient A) := ⟨Quotient.map' star (by
  intro x y h
  change (vanishing (A := A)).quotientRel x y at h
  change (vanishing (A := A)).quotientRel (star x) (star y)
  rw [Submodule.quotientRel_def] at h ⊢
  simpa only [star_sub] using star_mem_vanishing h)⟩
@[simp] lemma mk_star (x : BoundedFamilies A) : mk (star x) = star (mk x) := rfl
instance : StarRing (FamilyQuotient A) where
  star_involutive := by
    intro x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg mk (star_star x)
  star_mul := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (star_mul x y)
  star_add := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (star_add x y)
instance : StarModule ℂ (FamilyQuotient A) where
  star_smul := by
    intro c x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg mk (star_smul c x)
instance : IsScalarTower ℂ (FamilyQuotient A) (FamilyQuotient A) where
  smul_assoc := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (smul_mul_assoc c x y)
instance : SMulCommClass ℂ (FamilyQuotient A) (FamilyQuotient A) where
  smul_comm := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (smul_comm c x y)
end FamilyQuotient
end CuntzTrace

end

end OAI
