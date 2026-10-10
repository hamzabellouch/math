import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CentralMatrices

namespace OAI

/-! Central centering and projection displacement. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildComparison HochschildDixmier HochschildRigidity
  HochschildSakai HochschildQuantization HochschildCentralComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def CentrallyCentered (a : M) : Prop := ∀ z : M, (∀ x : M, Commute z x) → τ (z*a)=0

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {b : M} (hb : ∀ x : M, Commute b x) : ∀ x : M, Commute (star b) x := by
  intro x
  have hh := congrArg star (hb (star x)).eq
  change star b*x=x*star b
  simpa only [star_mul,star_star] using hh.symm

include e in
lemma trace_weighted_orbit_closure
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (a b z : M) (hz : ∀ x : M, Commute z x)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun u : unitary M => conjugate u a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨c,hc,hcn,hct⟩ := orbit_sequence τ hb
  have ht := trace_predual_tendsto e τ hτ (predual_tendsto_mul_left e z
    (predual_tendsto_of_preGNS e τ (mul_hasPreadjoint e) hτ hfaith ‖a‖ hcn hct))
  have he : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_trace_orbit τ htr a z hz (hc n)
  apply tendsto_nhds_unique ht
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ (z*a)) atTop (𝓝 _))

include e in
lemma zero_mem_orbit_closure
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : M} (ha : CentrallyCentered τ a) :
    gnsVector τ (0:M) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun u : unitary M => conjugate u a))) := by
  obtain ⟨b,_hbn,hbc,hb⟩ := exists_central_average e τ (mul_hasPreadjoint e) hτ htr hfaith a
  have hb0 : b=0 := by
    apply hfaith
    rw [trace_weighted_orbit_closure e τ hτ htr hfaith a b (star b) (central_star hbc) hb]
    exact ha (star b) (central_star hbc)
  simpa only [hb0] using hb

include e in
lemma norm_le_of_conjugations
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : M} (ha : CentrallyCentered τ a) (ε : ℝ)
    (hu : ∀ u : unitary M, ‖τ.toPreGNS (conjugate u a-a)‖ ≤ ε) :
    ‖τ.toPreGNS a‖ ≤ ε := by
  have hk : gnsVector τ '' convexHull ℝ
      (Set.range (fun u : unitary M => conjugate u a)) ⊆
      Metric.closedBall (gnsVector τ a) ε := by
    rw [LinearMap.image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨_,⟨u,rfl⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hu u
  have hh := closure_minimal hk Metric.isClosed_closedBall
    (zero_mem_orbit_closure e τ hτ htr hfaith ha)
  simpa only [Metric.mem_closedBall,dist_eq_norm,map_zero,zero_sub,norm_neg,gnsVector_norm] using hh

include e in
lemma norm_le_of_projection_commutators
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : M} (ha : CentrallyCentered τ a) (K : ℝ) (hK : 0 ≤ K)
    (hp : ∀ p : M, IsStarProjection p → ‖τ.toPreGNS (p*a-a*p)‖ ≤ K) :
    ‖τ.toPreGNS a‖ ≤ 4*K := by
  apply norm_le_of_conjugations e τ hτ htr hfaith ha (4*K)
  intro u
  have : Nontrivial M := ⟨⟨1,0,by
    intro hz
    have hh : (1:ℂ)=0 := h1.symm.trans ((congrArg τ hz).trans (map_zero τ))
    exact one_ne_zero hh⟩⟩
  have hh := contraction_bound_of_projections e (commutatorGNS τ a) (2*‖a‖) K
    (by positivity) hK (commutatorGNS_bound τ h1 a) hp (u:M)
    (CStarRing.norm_coe_unitary u).le
  have he : conjugate u a-a=((u:M)*a-a*(u:M))*star (u:M) := by
    simp only [conjugate_apply,sub_mul,mul_assoc,Unitary.mul_star_self_of_mem u.prop,mul_one]
  rw [he,show star (u:M)=((star u:unitary M):M) from rfl,preGNS_norm_unitary_right τ htr]
  exact hh

include e in
lemma exists_central_projection_displacement
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : M} (ha : CentrallyCentered τ a) (ha0 : 0<‖τ.toPreGNS a‖) :
    ∃ p : M, IsStarProjection p ∧ ‖τ.toPreGNS a‖/8 < ‖τ.toPreGNS (p*a-a*p)‖ := by
  by_contra hn
  push Not at hn
  have hh := norm_le_of_projection_commutators e τ hτ h1 htr hfaith ha
    (‖τ.toPreGNS a‖/8) (by positivity) hn
  linarith

end HochschildCentralQuantization

end

end OAI
