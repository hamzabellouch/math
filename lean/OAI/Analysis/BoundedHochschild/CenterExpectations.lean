import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CentralQuantization

namespace OAI

/-! The center-valued conditional expectation and its normality. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildDixmier HochschildSakai HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include hfaith in
omit [StarOrderedRing M] in
lemma central_trace_unique {b c : M}
    (hb : ∀ x : M, Commute b x) (hc : ∀ x : M, Commute c x)
    (hbc : ∀ z : M, (∀ x : M, Commute z x) → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,hbc (star (b-c)) (central_star (fun x => (hb x).sub_left (hc x))),sub_self]

include e hτ htr hfaith in
lemma exists_unique_center_part (a : M) :
    ∃ b : M, ‖b‖≤‖a‖ ∧ (∀ x : M, Commute b x) ∧
      ∀ z : M, (∀ x : M, Commute z x) → τ (z*b)=τ (z*a) := by
  obtain ⟨b,hbn,hbc,hb⟩ := exists_central_average e τ (mul_hasPreadjoint e) hτ htr hfaith a
  exact ⟨b,hbn,hbc,fun z hz => trace_weighted_orbit_closure e τ hτ htr hfaith a b z hz hb⟩

def centerPart (a : M) : M := (exists_unique_center_part e τ hτ htr hfaith a).choose

lemma centerPart_norm (a : M) : ‖centerPart e τ hτ htr hfaith a‖≤‖a‖ :=
  (exists_unique_center_part e τ hτ htr hfaith a).choose_spec.1

lemma centerPart_central (a x : M) : Commute (centerPart e τ hτ htr hfaith a) x :=
  (exists_unique_center_part e τ hτ htr hfaith a).choose_spec.2.1 x

lemma centerPart_trace (a z : M) (hz : ∀ x : M, Commute z x) :
    τ (z*centerPart e τ hτ htr hfaith a)=τ (z*a) :=
  (exists_unique_center_part e τ hτ htr hfaith a).choose_spec.2.2 z hz

lemma centerPart_add (a b : M) : centerPart e τ hτ htr hfaith (a+b)=
    centerPart e τ hτ htr hfaith a+centerPart e τ hτ htr hfaith b := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith (a+b))
    (fun x => (centerPart_central e τ hτ htr hfaith a x).add_left
      (centerPart_central e τ hτ htr hfaith b x))
  intro z hz
  rw [centerPart_trace e τ hτ htr hfaith _ z hz,mul_add,map_add,mul_add,map_add,
    centerPart_trace e τ hτ htr hfaith _ z hz,centerPart_trace e τ hτ htr hfaith _ z hz]

lemma centerPart_smul (t : ℂ) (a : M) : centerPart e τ hτ htr hfaith (t • a)=
    t • centerPart e τ hτ htr hfaith a := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith (t • a))
    (fun x => (centerPart_central e τ hτ htr hfaith a x).smul_left t)
  intro z hz
  rw [centerPart_trace e τ hτ htr hfaith _ z hz,mul_smul_comm,map_smul,mul_smul_comm,map_smul,
    centerPart_trace e τ hτ htr hfaith _ z hz]

def centerExpectation : M →L[ℂ] M :=
  LinearMap.mkContinuous
    { toFun := centerPart e τ hτ htr hfaith
      map_add' := centerPart_add e τ hτ htr hfaith
      map_smul' := centerPart_smul e τ hτ htr hfaith }
    1 (fun a => by
      change ‖centerPart e τ hτ htr hfaith a‖≤1*‖a‖
      simpa only [one_mul] using centerPart_norm e τ hτ htr hfaith a)

@[simp] lemma centerExpectation_apply (a : M) :
    centerExpectation e τ hτ htr hfaith a=centerPart e τ hτ htr hfaith a := rfl

lemma centerExpectation_fix {a : M} (ha : ∀ x : M, Commute a x) :
    centerExpectation e τ hτ htr hfaith a=a := by
  apply central_trace_unique τ hfaith (centerPart_central e τ hτ htr hfaith a) ha
  exact centerPart_trace e τ hτ htr hfaith a

lemma centerExpectation_bimodule {z : M} (hz : ∀ x : M, Commute z x) (a : M) :
    centerExpectation e τ hτ htr hfaith (z*a)=z*centerExpectation e τ hτ htr hfaith a := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith (z*a))
    (fun x => (hz x).mul_left (centerPart_central e τ hτ htr hfaith a x))
  intro w hw
  rw [centerPart_trace e τ hτ htr hfaith _ w hw,← mul_assoc,← mul_assoc]
  exact (centerPart_trace e τ hτ htr hfaith a (w*z) (fun x => (hw x).mul_left (hz x))).symm

lemma centered_sub_expectation (a : M) :
    CentrallyCentered τ (a-centerExpectation e τ hτ htr hfaith a) := by
  intro z hz
  rw [mul_sub,map_sub,centerExpectation_apply,centerPart_trace e τ hτ htr hfaith _ z hz,sub_self]

lemma centerExpectation_idempotent (a : M) :
    centerExpectation e τ hτ htr hfaith (centerExpectation e τ hτ htr hfaith a)=
      centerExpectation e τ hτ htr hfaith a :=
  centerExpectation_fix e τ hτ htr hfaith (centerPart_central e τ hτ htr hfaith a)

lemma centerExpectation_zero_iff (a : M) :
    centerExpectation e τ hτ htr hfaith a=0 ↔ CentrallyCentered τ a := by
  constructor
  · intro ha z hz
    have h := centerPart_trace e τ hτ htr hfaith a z hz
    change τ (z*centerExpectation e τ hτ htr hfaith a)=_ at h
    rw [ha,mul_zero,map_zero] at h
    exact h.symm
  · intro ha
    apply central_trace_unique τ hfaith (centerPart_central e τ hτ htr hfaith a)
      (fun x => Commute.zero_left x)
    intro z hz
    rw [mul_zero,map_zero,centerPart_trace e τ hτ htr hfaith _ z hz,ha z hz]

lemma centerExpectation_star (a : M) :
    centerExpectation e τ hτ htr hfaith (star a)=star (centerExpectation e τ hτ htr hfaith a) := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith (star a))
    (central_star (centerPart_central e τ hτ htr hfaith a))
  intro z hz
  rw [centerPart_trace e τ hτ htr hfaith _ z hz]
  have h := congrArg star (centerPart_trace e τ hτ htr hfaith a (star z) (central_star hz))
  rw [← map_star τ,← map_star τ,star_mul,star_mul,star_star] at h
  rw [htr z (star a),htr z (star (centerPart e τ hτ htr hfaith a))]
  exact h.symm

lemma centerExpectation_trace_adjoint (a b : M) :
    τ (star b*centerExpectation e τ hτ htr hfaith a)=
      τ (star (centerExpectation e τ hτ htr hfaith b)*a) := by
  rw [← centerExpectation_star e τ hτ htr hfaith]
  calc
    _ = τ (centerExpectation e τ hτ htr hfaith a*star b) := htr _ _
    _ = τ (centerExpectation e τ hτ htr hfaith a*
        centerExpectation e τ hτ htr hfaith (star b)) :=
      (centerPart_trace e τ hτ htr hfaith (star b) _
        (centerPart_central e τ hτ htr hfaith a)).symm
    _ = τ (centerExpectation e τ hτ htr hfaith (star b)*
        centerExpectation e τ hτ htr hfaith a) := htr _ _
    _ = _ := centerPart_trace e τ hτ htr hfaith a _
      (centerPart_central e τ hτ htr hfaith (star b))

lemma centerExpectation_normal : HasPreadjoint e (centerExpectation e τ hτ htr hfaith) := by
  obtain ⟨P,_hP,hPa⟩ := exists_preadjoint_of_trace_adjoint e e τ τ
    (mul_hasPreadjoint e) (mul_hasPreadjoint e) hτ hτ hfaith
    (centerExpectation e τ hτ htr hfaith) (centerExpectation e τ hτ htr hfaith)
    (centerExpectation_trace_adjoint e τ hτ htr hfaith)
  intro z
  exact ⟨P z,fun a => hPa a z⟩

lemma centerExpectation_norm_le : ‖centerExpectation e τ hτ htr hfaith‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖centerPart e τ hτ htr hfaith a‖≤1*‖a‖
  simpa only [one_mul] using centerPart_norm e τ hτ htr hfaith a

lemma centerExpectation_nonneg {a : M} (ha : 0≤a) :
    0≤centerExpectation e τ hτ htr hfaith a := by
  obtain ⟨b,hbn,hbc,hb⟩ := exists_central_average e τ (mul_hasPreadjoint e) hτ htr hfaith a
  have he : centerExpectation e τ hτ htr hfaith a=b := by
    apply central_trace_unique τ hfaith (centerPart_central e τ hτ htr hfaith a) hbc
    intro z hz
    rw [centerPart_trace e τ hτ htr hfaith _ z hz]
    exact (trace_weighted_orbit_closure e τ hτ htr hfaith a b z hz hb).symm
  rw [he]
  obtain ⟨c,hc,hcn,hct⟩ := HochschildCentralComparison.orbit_sequence τ hb
  have ht := predual_tendsto_of_preGNS e τ (mul_hasPreadjoint e) hτ hfaith ‖a‖ hcn hct
  have hpos : ∀ n, 0≤c n := by
    have hh : convexHull ℝ (Set.range (fun u : unitary M => conjugate u a)) ⊆ {b : M | 0≤b} := by
      apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        exact star_right_conjugate_nonneg ha (u:M)
      · intro x hx y hy r s hr hs _hrs
        exact add_nonneg (smul_nonneg hr hx) (smul_nonneg hs hy)
    exact fun n => hh (hc n)
  exact nonneg_of_bounded_predual_limit e ‖a‖ (norm_nonneg _)
    (Filter.Eventually.of_forall hcn) (Filter.Eventually.of_forall hpos) ht

end HochschildCentralQuantization

end

end OAI
