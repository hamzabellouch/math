import Mathlib
import OAI.Analysis.BoundedHochschild.Dixmier
import OAI.Analysis.BoundedHochschild.FiniteConstraints
import OAI.Analysis.BoundedHochschild.RareScales

namespace OAI

/-! Diffuse projections of prescribed trace and conjugation estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)

 

def NoMinimalProjections (M : Type*) [CStarAlgebra M] [PartialOrder M] : Prop :=
  ∀ p : M, IsStarProjection p → p ≠ 0 →
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ q ≠ p

lemma projection_trace_pos (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ p).re := by
  have hpos : 0 ≤ τ p := τ.map_nonneg hp.nonneg
  have hre : 0 ≤ (τ p).re := Complex.nonneg_iff.mp hpos |>.1
  apply lt_of_le_of_ne hre
  intro hz
  have he : τ p=0 := Complex.ext hz.symm (Complex.nonneg_iff.mp hpos).2.symm
  apply hp0
  apply hfaith p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using he

 

theorem exists_half_subprojection (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re ≤ (τ p).re/2 := by
  obtain ⟨q,hq,hqp,hq0,hqne⟩ := hdiff p hp hp0
  by_cases ht : (τ q).re ≤ (τ p).re/2
  · exact ⟨q,hq,hqp,hq0,ht⟩
  · refine ⟨p-q,(hq.le_iff_sub hp).mp hqp,sub_le_self _ hq.nonneg,?_,?_⟩
    · intro he
      exact hqne (sub_eq_zero.mp he).symm
    · rw [map_sub,Complex.sub_re]
      linarith

 

theorem exists_small_subprojection (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re < ε := by
  have hrec : ∀ n : ℕ, ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧
      (τ q).re ≤ (1/2 : ℝ)^n*(τ p).re := by
    intro n
    induction n with
    | zero => exact ⟨p,hp,le_rfl,hp0,by simp only [pow_zero,one_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨q,hq,hqp,hq0,hqn⟩ := ih
      obtain ⟨r,hr,hrq,hr0,hrt⟩ := exists_half_subprojection τ hdiff hq hq0
      refine ⟨r,hr,hrq.trans hqp,hr0,?_⟩
      rw [pow_succ]
      nlinarith
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n*(τ p).re) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_const (τ p).re
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨q,hq,hqp,hq0,hqn⟩ := hrec n
  exact ⟨q,hq,hqp,hq0,hqn.trans_lt hn⟩

lemma projection_le_of_comparable_trace_le
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hcomp : p ≤ q ∨ q ≤ p) (ht : (τ p).re ≤ (τ q).re) : p ≤ q := by
  rcases hcomp with h|h
  · exact h
  · have hz : p-q=0 := by
      by_contra hn
      have hh := projection_trace_pos τ hfaith ((hq.le_iff_sub hp).mp h) hn
      rw [map_sub,Complex.sub_re] at hh
      linarith
    exact (sub_eq_zero.mp hz).le

section Dual
open BoundedHochschild HochschildRigidity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hL hτ htr hfaith in
theorem projection_chain_upper {p : M} (hp : IsStarProjection p) (t : ℝ)
    (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t) :
    ∃ s : M, IsStarProjection s ∧ s ≤ p ∧ (τ s).re ≤ t ∧ ∀ q ∈ c, q ≤ s := by
  classical
  let T : Set ℝ := (fun q : M => (τ q).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨t,by rintro _ ⟨q,hq,rfl⟩; exact (hs q hq).2.2⟩
  obtain ⟨v,hvm,_hvL,hvt,hv⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hav using hv
  change ∀ n, (τ (a n)).re=v n at hav
  have ham : Monotone a := by
    intro m n hmn
    apply projection_le_of_comparable_trace_le τ hfaith (hs _ (ha m)).1 (hs _ (ha n)).1
      (hc.total (ha m) (ha n))
    rw [hav,hav]
    exact hvm hmn
  obtain ⟨s,hsp,ht,hns,hsl⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    a (fun n => (hs _ (ha n)).1) ham
  have htrace : (τ s).re=sSup T := by
    have htd := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (hs _ (ha n)).1.norm_le _) ht)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp htd)
    simpa only [Function.comp_def,hav] using hvt
  refine ⟨s,hsp,hsl p hp (fun n => (hs _ (ha n)).2.1),?_,?_⟩
  · rw [htrace]
    apply csSup_le hTne
    rintro _ ⟨q,hq,rfl⟩
    exact (hs q hq).2.2
  · intro q hq
    by_cases hex : ∃ n, q ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (hns n)
    · have hanq : ∀ n, a n ≤ q := by
        intro n
        exact (hc.total (ha n) hq).resolve_right (fun h => hex ⟨n,h⟩)
      apply projection_le_of_comparable_trace_le τ hfaith (hs q hq).1 hsp
        (Or.inr (hsl q (hs q hq).1 hanq))
      rw [htrace]
      exact le_csSup hTbd ⟨q,hq,rfl⟩
include e hL hτ htr hfaith in
 

theorem exists_projection_of_trace (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (t : ℝ) (ht0 : 0 ≤ t) (htp : t ≤ (τ p).re) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ (τ q).re=t := by
  classical
  let S : Set M := {q | IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t}
  have h0 : (0 : M) ∈ S := ⟨IsStarProjection.zero M,hp.nonneg,by simpa only [map_zero,Complex.zero_re]⟩
  obtain ⟨q,_hq0,hqm⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsp_le,hst,hsup⟩ := projection_chain_upper τ e hL hτ htr hfaith
      hp t c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsp_le,hst⟩,hsup⟩) 0 h0
  have hq : IsStarProjection q := hqm.1.1
  have hqp : q ≤ p := hqm.1.2.1
  have hqt : (τ q).re ≤ t := hqm.1.2.2
  refine ⟨q,hq,hqp,le_antisymm hqt ?_⟩
  by_contra hle
  have hlt : (τ q).re<t := lt_of_not_ge hle
  have hpq : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hqp
  have hpq0 : p-q ≠ 0 := by
    intro he
    have hh := congrArg (fun a : M => (τ a).re) (sub_eq_zero.mp he)
    linarith
  obtain ⟨r,hr,hrpq,hr0,hrt⟩ := exists_small_subprojection τ hdiff hpq hpq0
    (t-(τ q).re) (sub_pos.mpr hlt)
  have hqr : q*r=0 := by
    have hh := (hr.le_iff_mul_eq_right hpq).mp hrpq
    calc
      q*r=q*((p-q)*r) := by rw [hh]
      _=(q*p-q*q)*r := by noncomm_ring
      _=0 := by rw [(hq.le_iff_mul_eq_left hp).mp hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
  have hsum : q+r ∈ S := by
    refine ⟨hq.add hr hqr,?_,?_⟩
    · calc
        q+r ≤ q+(p-q) := add_le_add_right hrpq q
        _=p := by abel
    · rw [map_add,Complex.add_re]
      linarith
  have hback : q+r ≤ q := hqm.2 hsum (le_add_of_nonneg_right hr.nonneg)
  apply hr0
  apply le_antisymm _ hr.nonneg
  apply le_of_add_le_add_left (a := q)
  simpa only [add_zero] using hback

end Dual

end HochschildDiffuse

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

include e hL hτ in
 

theorem norm_sub_trace_le_of_conjugations (h1 : τ 1=1)
    (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (a : M) (ε : ℝ)
    (hu : ∀ u : unitary M, ‖τ.toPreGNS (conjugate u a-a)‖ ≤ ε) :
    ‖τ.toPreGNS (a-(τ a) • (1 : M))‖ ≤ ε := by
  have hk : gnsVector τ '' convexHull ℝ
      (Set.range (fun u : unitary M => conjugate u a)) ⊆
      Metric.closedBall (gnsVector τ a) ε := by
    rw [LinearMap.image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨_,⟨u,rfl⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hu u
  have hh := closure_minimal hk Metric.isClosed_closedBall
    (scalar_mem_orbit_closure e τ hL hτ h1 htr hfaith hfactor a)
  rw [Metric.mem_closedBall,dist_eq_norm] at hh
  rw [← map_sub,gnsVector_norm] at hh
  simpa only [map_sub,norm_sub_rev] using hh

end HochschildDixmier
end

end OAI
