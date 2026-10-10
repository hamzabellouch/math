import Mathlib
import OAI.Analysis.BoundedHochschild.NormalModulus

namespace OAI

/-! Hilbert-space averaging and central elements in unitary orbit closures. -/

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
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

def gnsVector : M →ₗ[ℝ] τ.GNS :=
  (UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp τ.toPreGNS.toLinearMap).restrictScalars ℝ

lemma gnsVector_norm (a : M) : ‖gnsVector τ a‖=‖τ.toPreGNS a‖ :=
  UniformSpace.Completion.norm_coe _

include e hL hτ in
 

theorem isClosed_gns_ball (C : ℝ) :
    IsClosed (gnsVector τ '' Metric.closedBall (0 : M) C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro y z hy hz
  choose a ha hay using hy
  have hnorm : ∀ n, ‖a n‖ ≤ C := fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using ha n
  have hc : CauchySeq (fun n => τ.toPreGNS (a n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq ε hε
    refine ⟨N,fun m hm n hn => ?_⟩
    rw [dist_eq_norm,← map_sub,← gnsVector_norm τ, map_sub,hay m,hay n,← dist_eq_norm]
    exact hN m hm n hn
  obtain ⟨b,hb,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ C hnorm hc
  have ht' : Tendsto (fun n => gnsVector τ (a n)) atTop (𝓝 (gnsVector τ b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [← map_sub,gnsVector_norm] using ht
  have he : gnsVector τ b=z := tendsto_nhds_unique ht' (by simpa only [hay] using hz)
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,he⟩

def conjugate (u : unitary M) : M →ₗ[ℝ] M where
  toFun a := (u : M)*a*star (u : M)
  map_add' := by intro a b; simp only [mul_add,add_mul]
  map_smul' := by intro r a; simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_apply (u : unitary M) (a : M) :
    conjugate u a=(u : M)*a*star (u : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_norm (u : unitary M) (a : M) : ‖conjugate u a‖=‖a‖ := by
  change ‖(u : M)*a*(star u : unitary M)‖=‖a‖
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_mul (u v : unitary M) (a : M) : conjugate u (conjugate v a)=conjugate (u*v) a := by
  simp only [conjugate_apply,Submonoid.coe_mul,star_mul,mul_assoc]

lemma conjugate_gns_norm (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (u : unitary M) (a : M) :
    ‖gnsVector τ (conjugate u a)‖=‖gnsVector τ a‖ := by
  rw [gnsVector_norm,gnsVector_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow,Complex.ofReal_pow,τ.preGNS_norm_sq,τ.preGNS_norm_sq]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,conjugate_apply,star_mul,star_star]
  have he : (u : M)*(star a*star (u : M))*((u : M)*a*star (u : M))=
      (u : M)*(star a*a)*star (u : M) := by
    calc
      _ = (u : M)*(star a*((star (u : M)*(u : M))*a))*star (u : M) := by noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem u.prop,one_mul]
  rw [he,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_hull (a : M) (u : unitary M) :
    conjugate u '' convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) := by
  rw [LinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  exact ⟨u*v,(conjugate_mul u v a).symm⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma orbit_hull_bounded (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      Metric.closedBall (0 : M) ‖a‖ := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨v,rfl⟩
  simp only [Metric.mem_closedBall,dist_zero_right,conjugate_norm,le_refl]

include e hL hτ in
 

theorem orbit_closure_lift (a : M) {z : τ.GNS}
    (hz : z ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ gnsVector τ b=z := by
  have hsub : closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) ⊆
      gnsVector τ '' Metric.closedBall (0 : M) ‖a‖ :=
    closure_minimal (Set.image_mono (orbit_hull_bounded a)) (isClosed_gns_ball e τ hL hτ ‖a‖)
  obtain ⟨b,hb,hbz⟩ := hsub hz
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,hbz⟩

lemma conjugate_mem_orbit_closure (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) (u : unitary M) :
    gnsVector τ (conjugate u b) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have ht : Tendsto (fun n => gnsVector τ (conjugate u (c n))) atTop
      (𝓝 (gnsVector τ (conjugate u b))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [← map_sub,conjugate_gns_norm τ htr]
    have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hyt)
    simpa only [← hcy,← map_sub] using hh
  apply isClosed_closure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => subset_closure
    ⟨conjugate u (c n),conjugate_hull a u ⟨c n,hc n,rfl⟩,rfl⟩

lemma orbit_gns_convex (a : M) :
    Convex ℝ (closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) := by
  exact ((convex_convexHull ℝ _).linear_image (gnsVector τ)).closure

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_min_norm {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hc : Convex ℝ K) :
    ∃ z ∈ K, ∀ w ∈ K, ‖z‖ ≤ ‖w‖ := by
  obtain ⟨z,hz,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc 0
  refine ⟨z,hz,fun w hw => ?_⟩
  simp only [zero_sub,norm_neg] at hmin
  rw [hmin]
  apply ciInf_le (f := fun w : K => ‖(w : H)‖) _ ⟨w,hw⟩
  exact ⟨(0 : ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩

omit [CompleteSpace H] in
lemma min_norm_unique {K : Set H} (hc : Convex ℝ K) {z w : H} (hz : z ∈ K) (hw : w ∈ K)
    (hmin : ∀ y ∈ K, ‖z‖ ≤ ‖y‖) (he : ‖w‖=‖z‖) : w=z := by
  have hm := hmin ((1/2 : ℝ) • z+(1/2 : ℝ) • w)
    (hc hz hw (by norm_num) (by norm_num) (by norm_num))
  rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at hm
  have hsq : (2*‖z‖)^2 ≤ ‖z+w‖^2 := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
    linarith
  have hp := parallelogram_law_with_norm ℝ z w
  rw [he] at hp
  have hz0 : ‖z-w‖=0 := by nlinarith [sq_nonneg ‖z-w‖,norm_nonneg (z-w)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz0)).symm
end Hilbert

include e hL hτ in
 

theorem exists_central_average (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0) (a : M) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ (∀ x : M, Commute b x) ∧
      gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
        (Set.range (fun v : unitary M => conjugate v a))) := by
  let := InnerProductSpace.rclikeToReal ℂ τ.GNS
  let K := closure (gnsVector τ '' convexHull ℝ
    (Set.range (fun v : unitary M => conjugate v a)))
  have hne : K.Nonempty := ⟨gnsVector τ (conjugate 1 a),
    subset_closure ⟨conjugate 1 a,subset_convexHull ℝ _ ⟨1,rfl⟩,rfl⟩⟩
  obtain ⟨z,hz,hmin⟩ := exists_min_norm hne isClosed_closure (orbit_gns_convex τ a)
  obtain ⟨b,hb,hbz⟩ := orbit_closure_lift e τ hL hτ a hz
  have hbmem : gnsVector τ b ∈ K := hbz ▸ hz
  have hfix : ∀ u : unitary M, conjugate u b=b := by
    intro u
    have he : gnsVector τ (conjugate u b)=gnsVector τ b := by
      apply min_norm_unique (orbit_gns_convex τ a) hbmem
        (conjugate_mem_orbit_closure τ htr a b hbmem u)
      · intro y hy; rw [hbz]; exact hmin y hy
      · exact conjugate_gns_norm τ htr u b
    apply sub_eq_zero.mp
    apply (preGNS_norm_eq_zero_iff τ hfaith _).mp
    rw [← gnsVector_norm τ,map_sub,he,sub_self,norm_zero]
  have hucomm : ∀ u : unitary M, Commute b (u : M) := by
    intro u
    have he := congrArg (fun x : M => x*(u : M)) (hfix u)
    simp only [conjugate_apply,mul_assoc,Unitary.star_mul_self_of_mem u.prop,mul_one] at he
    exact he.symm
  refine ⟨b,hb,?_,hbmem⟩
  intro x
  have hx : x ∈ Submodule.span ℂ (unitary M : Set M) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hucomm ⟨y,hy⟩
  | zero => exact Commute.zero_right b
  | add y z hy hz ihy ihz => exact ihy.add_right ihz
  | smul r y hy ih => exact ih.smul_right r

omit [StarOrderedRing M] in
lemma trace_conjugate (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (u : unitary M) (a : M) : τ (conjugate u a)=τ a := by
  rw [conjugate_apply,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]

omit [StarOrderedRing M] in
lemma trace_orbit_hull (htr : ∀ x y : M, τ (x*y)=τ (y*x)) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆ {b : M | τ b=τ a} := by
  apply convexHull_min
  · rintro _ ⟨u,rfl⟩; exact trace_conjugate τ htr u a
  · intro x hx y hy r t _hr _ht hrt
    change τ (r • x+t • y)=τ a
    rw [map_add,τ.map_smul_of_tower,τ.map_smul_of_tower,hx,hy,← add_smul,hrt,one_smul]

lemma trace_orbit_closure (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x)) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ b=τ a := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have hcτ : ∀ n, τ (c n)=τ a := fun n => trace_orbit_hull τ htr a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [← hcy,← map_sub,gnsVector_norm] using hh
  have htτ : Tendsto (fun n => ‖τ (c n-b)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => HochschildUltrapower.norm_trace_le τ h1 (c n-b)) ht
  have hzero : ‖τ a-τ b‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [map_sub,hcτ] using htτ)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

include e hL hτ in
 

theorem scalar_mem_orbit_closure (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M)) (a : M) :
    gnsVector τ ((τ a) • (1 : M)) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) := by
  obtain ⟨b,_hb,hbc,hbK⟩ := exists_central_average e τ hL hτ htr hfaith a
  obtain ⟨c,hc⟩ := hfactor b hbc
  have hbτ := trace_orbit_closure τ h1 htr a b hbK
  have hca : c=τ a := by simpa only [hc,map_smul,h1,smul_eq_mul,mul_one] using hbτ
  simpa only [hc,hca] using hbK

end HochschildDixmier
end

end OAI
