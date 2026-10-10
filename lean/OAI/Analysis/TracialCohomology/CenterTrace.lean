import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerComparison

namespace OAI

/-! Center trace for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def Central (a : M) : Prop := ∀ x : M, Commute a x
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {a : M} (ha : Central a) : Central (star a) := by
  intro x
  change star a*x=x*star a
  have h := congrArg star (ha (star x)).eq
  simpa only [star_mul,star_star] using h.symm
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_sub {a b : M} (ha : Central a) (hb : Central b) : Central (a-b) :=
  fun x => (ha x).sub_left (hb x)
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_mul {a b : M} (ha : Central a) (hb : Central b) : Central (a*b) :=
  fun x => (ha x).mul_left (hb x)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

def average (a : M) : M := (exists_central_average e τ
  (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith a).choose
lemma average_norm (a : M) : ‖average e τ hτ htr hfaith a‖ ≤ ‖a‖ :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.1
lemma average_central (a : M) : Central (average e τ hτ htr hfaith a) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.1
lemma average_orbit (a : M) :
    gnsVector τ (average e τ hτ htr hfaith a) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.2

variable (h1 : τ 1=1)
include htr in
omit [StarOrderedRing M] in
lemma central_pair_hull {z : M} (hz : Central z) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      {b | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨v,rfl⟩
    change τ (z*conjugate v a)=τ (z*a)
    rw [conjugate_apply]
    have he : z*((v:M)*a*star (v:M))=(v:M)*(z*a)*star (v:M) := by
      calc
        _=(z*(v:M))*a*star (v:M) := by simp only [mul_assoc]
        _=((v:M)*z)*a*star (v:M) := by rw [(hz (v:M)).eq]
        _=_ := by simp only [mul_assoc]
    rw [he]
    exact trace_conjugate τ htr v (z*a)
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,τ.map_smul_of_tower,
      τ.map_smul_of_tower,hx,hy,←add_smul,hrs,one_smul]

include htr h1 in
lemma central_pair_closure {z : M} (hz : Central z) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have htc : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_pair_hull τ htr hz a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [←hcy,←map_sub,gnsVector_norm] using hh
  have htt : Tendsto (fun n => ‖τ (z*(c n-b))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (HochschildUltrapower.norm_trace_le τ h1 _).trans
        (preGNS_norm_mul_le τ z _))
    simpa only [mul_zero] using ht.const_mul ‖z‖
  have he : ‖τ (z*a)-τ (z*b)‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [mul_sub,map_sub,htc] using htt)
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

include h1
lemma average_pair {z : M} (hz : Central z) (a : M) :
    τ (z*average e τ hτ htr hfaith a)=τ (z*a) :=
  central_pair_closure τ htr h1 hz a _ (average_orbit e τ hτ htr hfaith a)

omit h1 in
include hfaith in
omit [StarOrderedRing M] in
lemma central_unique {b c : M} (hb : Central b) (hc : Central c)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h _ (central_star (central_sub hb hc)),sub_self]

lemma average_eq (a b : M) (hb : Central b)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*a)) : average e τ hτ htr hfaith a=b := by
  apply central_unique τ hfaith (average_central e τ hτ htr hfaith a) hb
  intro z hz
  rw [average_pair e τ hτ htr hfaith h1 hz,h z hz]

lemma average_id {a : M} (ha : Central a) : average e τ hτ htr hfaith a=a :=
  average_eq e τ hτ htr hfaith h1 a a ha (fun _ _ => rfl)
lemma average_add (a b : M) : average e τ hτ htr hfaith (a+b)=
    average e τ hτ htr hfaith a+average e τ hτ htr hfaith b := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x
    exact (average_central e τ hτ htr hfaith a x).add_left
      (average_central e τ hτ htr hfaith b x)
  · intro z hz
    rw [mul_add,map_add,mul_add,map_add,average_pair e τ hτ htr hfaith h1 hz,
      average_pair e τ hτ htr hfaith h1 hz]
lemma average_smul (r : ℂ) (a : M) : average e τ hτ htr hfaith (r • a)=
    r • average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x; exact (average_central e τ hτ htr hfaith a x).smul_left r
  · intro z hz
    rw [mul_smul_comm,mul_smul_comm,map_smul,map_smul,average_pair e τ hτ htr hfaith h1 hz]

def expectation : M →L[ℂ] M := LinearMap.mkContinuous
  { toFun := average e τ hτ htr hfaith
    map_add' := average_add e τ hτ htr hfaith h1
    map_smul' := average_smul e τ hτ htr hfaith h1 }
  1 (by intro a; simpa using average_norm e τ hτ htr hfaith a)
@[simp] lemma expectation_apply (a : M) :
    expectation e τ hτ htr hfaith h1 a=average e τ hτ htr hfaith a := rfl

lemma average_bimodule {z : M} (hz : Central z) (a : M) :
    average e τ hτ htr hfaith (z*a)=z*average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · exact central_mul hz (average_central e τ hτ htr hfaith a)
  · intro w hw
    simpa only [←mul_assoc] using average_pair e τ hτ htr hfaith h1 (central_mul hw hz) a
lemma average_trace (a b : M) : average e τ hτ htr hfaith (a*b)=
    average e τ hτ htr hfaith (b*a) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz,←mul_assoc,htr,←mul_assoc,
      ←(hz a).eq,mul_assoc]
lemma trace_average (a : M) : τ (average e τ hτ htr hfaith a)=τ a := by
  simpa only [one_mul] using average_pair e τ hτ htr hfaith h1 (z:=1)
    (fun x => Commute.one_left x) a
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma average_nonneg {a : M} (ha : 0 ≤ a) : 0 ≤ average e τ hτ htr hfaith a := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (average_orbit e τ hτ htr hfaith a)
  choose c hc hcy using hy
  have hcp : ∀ n, 0 ≤ c n := by
    intro n
    have hsub : convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
        Set.Ici (0:M) := by
      apply convexHull_min _ (convex_Ici _)
      rintro _ ⟨v,rfl⟩
      exact star_right_conjugate_nonneg ha (v:M)
    exact hsub (hc n)
  have hcn : ∀ n, ‖c n‖ ≤ ‖a‖ := by
    intro n
    simpa only [Metric.mem_closedBall,dist_zero_right] using orbit_hull_bounded a (hc n)
  have ht : GNSTendsto τ c atTop (average e τ hτ htr hfaith a) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [GNSTendsto,←hcy,←map_sub,gnsVector_norm] using hh
  exact HochschildSakai.nonneg_of_bounded_predual_limit e ‖a‖ (norm_nonneg a)
    (Eventually.of_forall hcn) (Eventually.of_forall hcp)
    (ht.predual e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ hfaith ‖a‖ hcn)

lemma average_gns_norm (a : M) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith a)‖ ≤ ‖τ.toPreGNS a‖ := by
  have hsub : gnsVector τ '' convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      Metric.closedBall (0:τ.GNS) ‖τ.toPreGNS a‖ := by
    rw [LinearMap.image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,gnsVector_norm]
    simpa only [gnsVector_norm] using le_of_eq (conjugate_gns_norm τ htr v a)
  have hh := closure_minimal hsub Metric.isClosed_closedBall (average_orbit e τ hτ htr hfaith a)
  simpa only [Metric.mem_closedBall,dist_zero_right,gnsVector_norm] using hh

include h1 in
lemma average_mono : Monotone (average e τ hτ htr hfaith) := by
  intro a b hab
  have hp := average_nonneg e τ hτ htr hfaith (sub_nonneg.mpr hab)
  change 0 ≤ expectation e τ hτ htr hfaith h1 (b-a) at hp
  rw [map_sub] at hp
  exact sub_nonneg.mp hp

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_central {a p : M} (hp : IsSupportProjection a p) (ha : Central a) : Central p := by
  have h (x : M) : p*x*p=p*x := by
    have hz : a*(x*p-p*x)=0 := by
      rw [mul_sub,←mul_assoc,(ha x).eq,mul_assoc,hp.right,←mul_assoc,hp.right,(ha x).eq,sub_self]
    have hh := hp.annihilate _ hz
    simpa only [mul_sub,←mul_assoc,hp.proj.isIdempotentElem.eq,sub_eq_zero] using hh
  intro x
  change p*x=x*p
  have hs := congrArg star (h (star x))
  simp only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,mul_assoc] at hs
  exact (h x).symm.trans ((mul_assoc _ _ _).trans hs)

include hfaith in
omit [StarOrderedRing M] in
lemma projection_zero_of_trace_zero {p : M} (hp : IsStarProjection p) (ht : τ p=0) : p=0 := by
  apply hfaith
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using ht

include h1 in
lemma projection_le_support_average {p c : M} (hp : IsStarProjection p)
    (hc : IsSupportProjection (average e τ hτ htr hfaith p) c) : p ≤ c := by
  have hcc := support_central hc (average_central e τ hτ htr hfaith p)
  have hzc : Central (1-c) := fun x => (Commute.one_left x).sub_left (hcc x)
  have hzproj : IsStarProjection ((1-c)*p) := hc.proj.one_sub.mul hp (hzc p)
  have ht : τ ((1-c)*p)=0 := by
    rw [←average_pair e τ hτ htr hfaith h1 hzc,sub_mul,one_mul,hc.left,sub_self,map_zero]
  have hz := projection_zero_of_trace_zero τ hfaith hzproj ht
  apply (hp.le_iff_mul_eq_right hc.proj).mpr
  exact (sub_eq_zero.mp (by simpa only [sub_mul,one_mul] using hz)).symm

include e hτ htr hfaith h1 in
lemma exists_central_support {p : M} (hp : IsStarProjection p) :
    ∃ c : M, IsStarProjection c ∧ Central c ∧ p ≤ c ∧
      ∀ q : M, (∀ a : M, q*a*p=0) → q*c=0 := by
  obtain ⟨c,hc⟩ := HochschildSakai.exists_support_projection e
    (average e τ hτ htr hfaith p) (average_nonneg e τ hτ htr hfaith hp.nonneg)
  refine ⟨c,hc.proj,support_central hc (average_central e τ hτ htr hfaith p),
    projection_le_support_average e τ hτ htr hfaith h1 hp hc,?_⟩
  intro q hq
  have hker : convexHull ℝ (Set.range (fun v : unitary M => conjugate v p)) ⊆
      {a | q*a=0} := by
    apply convexHull_min
    · rintro _ ⟨v,rfl⟩
      change q*((v:M)*p*star (v:M))=0
      rw [←mul_assoc,←mul_assoc,hq,zero_mul]
    · intro a ha b hb r s _ _ _
      change q*(r • a+s • b)=0
      change q*a=0 at ha
      change q*b=0 at hb
      rw [mul_add,mul_smul_comm,mul_smul_comm,ha,hb,smul_zero,smul_zero,add_zero]
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (average_orbit e τ hτ htr hfaith p)
  choose a ha hay using hy
  have ht : GNSTendsto τ a atTop (average e τ hτ htr hfaith p) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [GNSTendsto,←hay,←map_sub,gnsVector_norm] using hh
  have han (n : ℕ) : q*a n=0 := hker (ha n)
  have ht0 : GNSTendsto τ (fun n : ℕ => q*a n) atTop 0 := by
    simpa only [han] using GNSTendsto.const τ (0:M) (atTop : Filter ℕ)
  have hz : q*average e τ hτ htr hfaith p=0 := GNSTendsto.unique τ hfaith
    ((GNSTendsto.const τ q (atTop : Filter ℕ)).mul τ htr ht ‖q‖ (fun _ => le_rfl)) ht0
  exact HochschildPolar.support_right_annihilate hc
    (IsSelfAdjoint.of_nonneg (average_nonneg e τ hτ htr hfaith hp.nonneg)) hz
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e in
lemma maximal_separates {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (hv : ∀ w : CornerIso p q, v ≤ w → w ≤ v) :
    ∀ a : M, (q-v.final)*a*(p-v.initial)=0 := by
  intro a
  by_contra hh
  have hr := (v.initial_proj.le_iff_sub hp).mp v.init_le
  have hs := (v.final_proj.le_iff_sub hq).mp v.final_le
  let b := (q-v.final)*a*(p-v.initial)
  obtain ⟨t,r,s,htI,htF,hrp,hsq,hti,htf,htrt,_hstt,hb⟩ :=
    corner_polar e hr hs (show b*(p-v.initial)=b by
      dsimp [b]; rw [mul_assoc,hr.isIdempotentElem.eq])
      (show (q-v.final)*b=b by dsimp [b]; rw [←mul_assoc,←mul_assoc,hs.isIdempotentElem.eq])
  let u : CornerIso (p-v.initial) (q-v.final) :=
    ⟨t,by rw [hti]; exact htI,by rw [hti]; exact htrt,
      by rw [hti]; exact hrp,by rw [htf]; exact hsq⟩
  obtain ⟨w,hw,hle⟩ := add_orthogonal hp hq v u
  have he : w=v := le_antisymm (hv w hle) hle
  have hsum : (v:M)+t=(v:M) := by simpa only [he] using hw.symm
  have ht0 : t=0 := add_eq_left.mp hsum
  exact hh (by change b=0; rw [hb,ht0,zero_mul])

include htr in
omit [StarOrderedRing M] in
lemma central_rank_trace {p q z : M} (v : CornerIso p q) (hz : Central z) :
    τ (z*v.initial)=τ (z*v.final) := by
  change τ (z*(star (v:M)*(v:M)))=τ (z*((v:M)*star (v:M)))
  rw [←mul_assoc,(hz (star (v:M))).eq,mul_assoc,htr,←mul_assoc]

include e hτ htr hfaith h1 in

theorem exists_full_initial_of_central_cuts {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ∀ c : M, IsStarProjection c → Central c →
      (τ (c*p)).re ≤ (τ (c*q)).re) :
    ∃ v : CornerIso p q, v.initial=p := by
  obtain ⟨v,hv⟩ := exists_maximal e τ hτ htr hfaith hp hq
  have hr := (v.initial_proj.le_iff_sub hp).mp v.init_le
  have hs := (v.final_proj.le_iff_sub hq).mp v.final_le
  obtain ⟨c,hc,hcc,hrc,hcs⟩ := exists_central_support e τ hτ htr hfaith h1 hr
  have hscr : (q-v.final)*c=0 := hcs _ (maximal_separates e hp hq v hv)
  have hcsr : c*(q-v.final)=0 := (hcc _).eq.trans hscr
  have hcr : c*(p-v.initial)=p-v.initial := (hr.le_iff_mul_eq_right hc).mp hrc
  have hi := central_rank_trace τ htr v hcc
  have hle := hpq c hc hcc
  have hτs : τ (c*q)=τ (c*v.final) := by
    exact sub_eq_zero.mp (by simpa only [mul_sub,map_sub,map_zero] using congrArg τ hcsr)
  have hτr : τ (c*p)-τ (c*v.initial)=τ (p-v.initial) := by
    simpa only [mul_sub,map_sub] using congrArg τ hcr
  have hnr : (τ (p-v.initial)).re ≤ 0 := by
    rw [hτs,←hi] at hle
    have hh := congrArg Complex.re hτr
    simp only [Complex.sub_re] at hh
    linarith
  have hz : p-v.initial=0 := by
    by_contra hh
    exact (not_lt_of_ge hnr) (HochschildDiffuse.projection_trace_pos τ hfaith hr hh)
  exact ⟨v,(sub_eq_zero.mp hz).symm⟩

include e hτ htr hfaith h1 in
theorem exists_full_initial_of_average_le {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : average e τ hτ htr hfaith p ≤ average e τ hτ htr hfaith q) :
    ∃ v : CornerIso p q, v.initial=p := by
  apply exists_full_initial_of_central_cuts e τ hτ htr hfaith h1 hp hq
  intro c hc hcc
  rw [←average_pair e τ hτ htr hfaith h1 hcc p,
    ←average_pair e τ hτ htr hfaith h1 hcc q]
  apply Complex.re_le_re
  apply τ.monotone
  have h := star_right_conjugate_nonneg (sub_nonneg.mpr hpq) c
  rw [hc.isSelfAdjoint.star_eq,mul_sub,sub_mul,
    ←(average_central e τ hτ htr hfaith q c).eq,
    ←(average_central e τ hτ htr hfaith p c).eq,mul_assoc,mul_assoc,
    hc.isIdempotentElem.eq] at h
  rw [(average_central e τ hτ htr hfaith q c).eq,
    (average_central e τ hτ htr hfaith p c).eq] at h
  exact sub_nonneg.mp h
include e hτ htr hfaith h1 in
theorem equivalent_of_average_eq {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q)
    (hpq : average e τ hτ htr hfaith p=average e τ hτ htr hfaith q) :
    ∃ v : M, star v*v=p ∧ v*star v=q ∧ v*p=v ∧ q*v=v := by
  obtain ⟨v,hvp⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 hp hq hpq.le
  have hpqt : τ p=τ q := by
    rw [←trace_average e τ hτ htr hfaith h1 p,←trace_average e τ hτ htr hfaith h1 q,hpq]
  have htrace : (τ v.final).re=(τ q).re := by
    change (τ ((v:M)*star (v:M))).re=(τ q).re
    rw [htr]
    change (τ v.initial).re=(τ q).re
    rw [hvp,hpqt]
  have hqv : q ≤ v.final := HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
    hq v.final_proj (Or.inr v.final_le) htrace.ge
  have hvq : v.final=q := le_antisymm v.final_le hqv
  exact ⟨(v:M),hvp,hvq,by simpa only [hvp] using v.mul_initial,
    by simpa only [hvq] using v.final_mul⟩
end PopaCenter

end

end OAI
