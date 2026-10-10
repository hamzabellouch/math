import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationIncomingProbes
import OAI.Combinatorics.Chromatic.QuantumTorus.NearCutGeometry

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance nearCutMutationRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutMutationAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutMutationAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_factor (a:ℝ) (hh:NearCut Ω C pc e (k+a • v)) :
    mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a=
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1 := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have ha:∃N,a∈lineEvents (realRootsThrough e C N) v k:=
      ⟨1,RationalFiber.line_cut_event C pc e L hdeg v k H a hp⟩
    simp only [mutatedLineFactor,dite_eq_left ha,ite_eq_left hp]
  · rw [ite_eq_right hp]
    unfold mutatedLineFactor
    split
    · next ha=>
      let data:=lineRayData C e he L hdeg v k H a ha
      have HC:=nearCut_noncut_wall Ω C coord hcoord pc e he S hS hcomp L hdeg (k+a • v) hh
        data.root data.degree data.degree_pos data.root_degree data.generic
        (decide (0<(k+a • v) (e (simpleRoot C pc))))
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
      rw [HC]
      have HO:∀b,orientPowerSeries b (1:PowerSeries (Torus LaurentRay.vUnit Ω))=1:=by
        intro b
        apply PowerSeries.ext
        intro n
        exact orientPowerSeries_trivial b 1 n (fun _ _=>rfl) n le_rfl
      simp only [HO,mutationCompletion_one]
    · rfl

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_product (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) (N:ℕ) (hN:1≤N) :
    mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  rw [mutatedLineProduct]
  have HE:(intervalEventList C e v k lo hi N).map
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)=
      (intervalEventList C e v k lo hi N).map (fun a=>if k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 then
        orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
          (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1):=by
    apply List.map_congr_left
    intro a ha
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
      nearCut_mutated_factor Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
        (hh a (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.1.le
          (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.2.le)
  rw [HE]
  apply pureCut_telescope _ (normalizedSimple_constant Ω _)
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (RationalFiber.line_cut_offset_ne C pc e L hdeg v k H))
  · exact fun hz=>hlo (RationalFiber.line_cut_event C pc e L hdeg v k H lo hz)
  · exact fun hz=>hhi (RationalFiber.line_cut_event C pc e L hdeg v k H hi hz)
  · exact fun a ha=>(Finset.mem_filter.mp ha).2
  · intro a hla hah hz
    exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (RationalFiber.line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_completion (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) :
    mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have HH:=nearCut_mutated_product Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H
    lo hi hlohi hlo hhi hh N (le_max_left _ _)
  rw [←HH]
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi j N
        (le_max_left _ _) ((Nat.mul_le_mul_left _ hj).trans (le_max_right _ _))
  · exact fun _ _=>rfl

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_path {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b)
    (hh:p.InRegion C e {h | NearCut Ω C pc e h}) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<a (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>rw [mutatedPathCompletion,one_mul]
  | append s p ih=>
    rw [mutatedPathCompletion,mul_assoc,ih hh.2]
    exact nearCut_mutated_completion Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1) hh.1

variable (hnd:∀r≠0,∃m,Ω r m≠0)
include hnd in
lemma nearCut_mutated_transport (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc) := by
  obtain ⟨p,hp⟩:=nearCut_path Ω C pc e hC HA HB ha hb
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p]
  have HH:=nearCut_mutated_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p hp
  simpa only [pureCutGauge,decide_eq_false (not_lt.mpr hap.le),Bool.false_eq_true,ite_false,
    decide_eq_true hbp,ite_true,mul_one] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
include hS in
lemma nearCut_double_regular (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (pos:Bool) :
    ∃h:Module.Dual ℝ E,RegularCovector C e h ∧ NearCut Ω C pc e h ∧
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) h (e m)≠0) := by
  classical
  let ε:ℝ:=1/((mutationSize Ω C pc:ℝ)+1)
  have hep:0<ε:=by dsimp [ε]; positivity
  obtain ⟨J,hJ⟩:=real_covector_prescribe C e hC (fun _=>1)
  obtain ⟨k,hk⟩:=real_covector_prescribe C e hC (fun i=>if i=pc then if pos then ε/2 else -ε/2 else -2)
  have hkn:NearCut Ω C pc e k:=by
    constructor
    · rw [hk]; simp only [ite_true]
      cases pos <;> simp only [Bool.false_eq_true,ite_false,ite_true,abs_div,abs_of_pos hep,
        abs_neg,abs_of_pos (show (0:ℝ)<2 by norm_num)]
      all_goals change _<ε; linarith
    · intro i hi; rw [hk,ite_eq_right hi]; norm_num
  let P:=insert ((0:ℝ),e (simpleRoot C pc)) (nearCutProbes Ω C pc e)
  let T:ℕ → Finset E:=fun N=>realRootsThrough e C N ∪
    (realRootsThrough e (mutatedRoots Ω C pc) N).image
      (fun x=>if pos then x else realShearVector e S (simpleRoot C pc) x)
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions_with_probes T 0 0 k P J
  have Hreg:RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s (Finset.mem_union_left _ hs)
      (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have Hcut:=HP ((0:ℝ),e (simpleRoot C pc)) (Finset.mem_insert_self _ _)
  simp only [zero_smul,add_zero] at Hcut
  have Hside:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    cases pos
    · change h (e (simpleRoot C pc))<0
      apply Hcut.2
      rw [hk]; simp only [ite_true,Bool.false_eq_true,ite_false]
      linarith
    · change 0<h (e (simpleRoot C pc))
      apply Hcut.1
      rw [hk]; simp only [ite_true]
      linarith
  refine ⟨h,Hreg,nearCut_of_probes Ω C pc e J k h hJ hkn
    (fun x hx=>HP x (Finset.mem_insert_of_mem hx)),Hside,?_⟩
  intro n hn m hm
  obtain ⟨J',hJ'⟩:=mutated_degree_covector Ω C pc e hC
  have hm0:e m≠0:=by
    have H:=covector_root_pos (mutatedRoots Ω C pc) e J' (fun i=>by rw [hJ']; norm_num) hn hm
    intro h0
    rw [h0,map_zero] at H
    exact lt_irrefl _ H
  have hv:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
    cases pos
    · exact realShearVector_ne_zero C pc e S hS hm0
    · exact hm0
  have HT:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈T n:=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,realRoot_mem e _ n n le_rfl m hm,rfl⟩)
  have HH:=(Ha n).avoid _ HT (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hv)
  rw [realMutationCovector_eq_side e S _ pos h (by cases pos <;> exact le_of_lt Hside)]
  cases pos
  · simpa only [realSideCovector,Bool.false_eq_true,ite_false,realShearCovector_eval] using HH
  · exact HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
