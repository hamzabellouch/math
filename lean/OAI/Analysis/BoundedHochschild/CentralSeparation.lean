import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.TypeIIDefinitions

namespace OAI

/-! Central separation from tracial conjugacy orbits. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildSakai FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma orbit_sequence {a b : M}
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun u : unitary M => conjugate u a)))) :
    ∃ c : ℕ → M, (∀ n, c n ∈ convexHull ℝ (Set.range (fun u : unitary M => conjugate u a))) ∧
      (∀ n, ‖c n‖ ≤ ‖a‖) ∧ GNSTendsto τ c atTop b := by
  obtain ⟨y,hy,ht⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc he using hy
  refine ⟨c,hc,fun n => ?_,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using orbit_hull_bounded a (hc n)
  · have hh := tendsto_iff_norm_sub_tendsto_zero.mp ht
    simpa only [GNSTendsto,← he,← map_sub,gnsVector_norm] using hh

omit [StarOrderedRing M] in
include htr in
lemma central_trace_orbit (a z : M) (hz : ∀ x : M, Commute z x) :
    convexHull ℝ (Set.range (fun u : unitary M => conjugate u a)) ⊆
      {b : M | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨u,rfl⟩
    change τ (z*((u:M)*a*star (u:M)))=τ (z*a)
    have he : z*((u:M)*a*star (u:M))=(u:M)*(z*a)*star (u:M) := by
      rw [← mul_assoc,← mul_assoc,(hz (u:M)).eq,mul_assoc (u:M) z a]
    rw [he,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,
      τ.map_smul_of_tower,τ.map_smul_of_tower,hx,hy,← add_smul,hrs,one_smul]

include e hτ htr hfaith in

theorem central_separator {p q : M} (hp : IsStarProjection p) (_hq : IsStarProjection q)
    (hpq : ∀ a : M, p*a*q=0) :
    ∃ z : M, CentralProjection z ∧ p ≤ z ∧ z*q=0 := by
  let L := mul_hasPreadjoint e
  obtain ⟨b,_hbn,hbc,hb⟩ := exists_central_average e τ L hτ htr hfaith p
  obtain ⟨c,hc,hcn,hct⟩ := orbit_sequence τ hb
  have hctw := predual_tendsto_of_preGNS e τ L hτ hfaith ‖p‖ hcn hct
  have hpos : ∀ n, 0 ≤ c n := by
    have hh : convexHull ℝ (Set.range (fun u : unitary M => conjugate u p)) ⊆ {a : M | 0 ≤ a} := by
      apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        exact star_right_conjugate_nonneg hp.nonneg (u:M)
      · intro a ha b hb r s hr hs _hrs
        exact add_nonneg (smul_nonneg hr ha) (smul_nonneg hs hb)
    exact fun n => hh (hc n)
  have hbpos : 0 ≤ b := nonneg_of_bounded_predual_limit e ‖p‖ (norm_nonneg _)
    (Eventually.of_forall hcn) (Eventually.of_forall hpos) hctw
  obtain ⟨z,hz⟩ := exists_support_projection e b hbpos
  have hzc : CentralProjection z := ⟨hz.proj,fun a => hz.commute (IsSelfAdjoint.of_nonneg hbpos) (hbc a)⟩
  have hcz : ∀ n, τ ((1-z)*c n)=τ ((1-z)*p) := fun n =>
    central_trace_orbit τ htr p (1-z)
      (fun a => (Commute.one_left a).sub_left (hzc.2 a)) (hc n)
  have htb : τ ((1-z)*b)=τ ((1-z)*p) := by
    have hh := trace_predual_tendsto e τ hτ (predual_tendsto_mul_left e (1-z) hctw)
    apply tendsto_nhds_unique hh
    simpa only [hcz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ ((1-z)*p)) atTop (𝓝 _))
  have hzbp : τ ((1-z)*p)=0 := by
    rw [sub_mul,one_mul,hz.left,sub_self,map_zero] at htb
    exact htb.symm
  have hr : IsStarProjection ((1-z)*p) :=
    hzc.1.one_sub.mul hp ((Commute.one_left p).sub_left (hzc.2 p))
  have hzero : (1-z)*p=0 := by
    apply hfaith
    exact (by simpa only [hr.isSelfAdjoint.star_eq,hr.isIdempotentElem.eq] using hzbp)
  have hpz : p ≤ z := (hp.le_iff_mul_eq_right hzc.1).mpr (by
    rw [sub_mul,one_mul,sub_eq_zero] at hzero; exact hzero.symm)
  have hcbq : ∀ n, c n*q=0 := by
    have hh : convexHull ℝ (Set.range (fun u : unitary M => conjugate u p)) ⊆ {a : M | a*q=0} := by
      apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        change (u:M)*p*star (u:M)*q=0
        rw [mul_assoc,mul_assoc,← mul_assoc p,hpq,mul_zero]
      · intro a ha b hb r s _hr _hs _hrs
        change (r • a+s • b)*q=0
        rw [add_mul,smul_mul_assoc,smul_mul_assoc,ha,hb,smul_zero,smul_zero,add_zero]
    exact fun n => hh (hc n)
  have hbq : b*q=0 := by
    apply predual_tendsto_unique e (predual_tendsto_mul_right e q hctw)
    simpa only [hcbq] using predual_tendsto_const e (0:M) (atTop : Filter ℕ)
  exact ⟨z,hzc,hpz,hz.annihilate q hbq⟩

end HochschildCentralComparison

end

end OAI
