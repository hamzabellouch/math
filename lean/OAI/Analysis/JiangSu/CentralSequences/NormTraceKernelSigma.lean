import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.ApproximateUnitSequence
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerPositive
import OAI.Analysis.JiangSu.CentralSequences.QuasicentralFinite

namespace OAI

noncomputable section
namespace NonunitalGamma

section
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "L" => lp (fun _ : ℕ => A) ∞

lemma kernel_diagonal_choice (hfree : (U : Filter ℕ) ≤ atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ m, ∀ᶠ k in (U : Filter ℕ), P m k) :
    ∃ j : ℕ → ℕ, Tendsto j (U : Filter ℕ) atTop ∧
      ∀ᶠ k in (U : Filter ℕ), P (j k) k := by
  classical
  let j : ℕ → ℕ := fun k => Nat.findGreatest (fun n => ∀ m ≤ n, P m k) k
  have hfin (n : ℕ) : ∀ᶠ k in (U : Filter ℕ), ∀ m ≤ n, P m k := by
    have h := (eventually_all_finset (Finset.range (n+1))).mpr (fun m _ => hP m)
    filter_upwards [h] with k hk
    intro m hm
    exact hk m (Finset.mem_range.mpr (by omega))
  refine ⟨j,?_,?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [hfin n,hfree (eventually_ge_atTop n)] with k hk hnk
    exact Nat.le_findGreatest hnk hk
  · filter_upwards [hfin 0] with k hk
    exact (Nat.findGreatest_spec (P := fun n => ∀ m ≤ n, P m k) (Nat.zero_le k) hk) (j k) le_rfl

omit [PartialOrder A] [StarOrderedRing A] [Nonempty (NormalizedTrace A)] in
lemma eventually_norm_lt_of_quotient_norm_lt (x : L) {r : ℝ}
    (h : ‖NormUltra.QuotientAlgebra.mk U x‖<r) :
    ∀ᶠ k in (U : Filter ℕ), ‖x k‖<r := by
  rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup] at h
  exact eventually_lt_of_limsup_lt h (NormUltra.BoundedFamilies.norm_bounded U x)

theorem trace_kernel_sigma_ideal (hfree : (U : Filter ℕ) ≤ atTop)
    (x w : ℕ → N) (hw : ∀ m, normToTracial U (w m)=0) :
    ∃ d : N, normToTracial U d=0 ∧ 0≤d ∧ ‖d‖≤1 ∧
      (∀ m, d*w m=w m) ∧ (∀ m, x m*d=d*x m) := by
  classical
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0<e n := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlocal (n : ℕ) : ∃ d : N, normToTracial U d=0 ∧ 0≤d ∧ ‖d‖≤1 ∧
      (∀ m≤n, ‖w m-d*w m‖≤e n) ∧ (∀ m≤n, ‖x m*d-d*x m‖<e n) := by
    obtain ⟨d,hd,hp,hn,hW,hX⟩ := Quasicentral.exists_quasicentral_kernel_contraction
      (normToTracial U) ((Finset.range (n+1)).image x) ((Finset.range (n+1)).image w)
      (by intro v hv; obtain ⟨m,_hm,rfl⟩ := Finset.mem_image.mp hv; exact hw m) (he n)
    exact ⟨d,hd,hp,hn,fun m hm => hW _ (Finset.mem_image.mpr ⟨m,Finset.mem_range.mpr (by omega),rfl⟩),
      fun m hm => hX _ (Finset.mem_image.mpr ⟨m,Finset.mem_range.mpr (by omega),rfl⟩)⟩
  choose d hd hp hn hW hX using hlocal
  choose b hb hbp hbn using fun n => NormUltra.QuotientAlgebra.positive_contraction_representative (hp n) (hn n)
  choose a ha using fun m => NormUltra.QuotientAlgebra.mk_surjective (x m)
  choose c hc using fun m => NormUltra.QuotientAlgebra.mk_surjective (w m)
  have hnull (n : ℕ) : Tendsto (fun k => familyTwoNorm T (Unitization.inr (b n k)))
      (U : Filter ℕ) (𝓝 0) := by
    have hz : sequenceQuotientMap (A := A) U (b n)=0 := by
      rw [←normToTracial_mk,hb n,hd n]
    exact (familyQuotientMap_eq_zero T U (boundedInr (A := A) (b n))).mp hz
  let P : ℕ → ℕ → Prop := fun n k => familyTwoNorm T (Unitization.inr (b n k))<e n ∧
    ∀ m≤n, ‖c m k-b n k*c m k‖<2*e n ∧ ‖a m k*b n k-b n k*a m k‖<2*e n
  have hP (n : ℕ) : ∀ᶠ k in (U : Filter ℕ), P n k := by
    have hz := (tendsto_order.mp (hnull n)).2 (e n) (he n)
    have herr (m : ℕ) (hm : m≤n) : ∀ᶠ k in (U : Filter ℕ),
        ‖c m k-b n k*c m k‖<2*e n ∧ ‖a m k*b n k-b n k*a m k‖<2*e n := by
      have h1 : ‖NormUltra.QuotientAlgebra.mk U (c m-b n*c m)‖<2*e n := by
        rw [NormUltra.QuotientAlgebra.mk_sub,NormUltra.QuotientAlgebra.mk_mul,hb n,hc m]
        exact (hW n m hm).trans_lt (by linarith [he n])
      have h2 : ‖NormUltra.QuotientAlgebra.mk U (a m*b n-b n*a m)‖<2*e n := by
        rw [NormUltra.QuotientAlgebra.mk_sub,NormUltra.QuotientAlgebra.mk_mul,
          NormUltra.QuotientAlgebra.mk_mul,hb n,ha m]
        exact (hX n m hm).trans (by linarith [he n])
      exact (eventually_norm_lt_of_quotient_norm_lt U _ h1).and (eventually_norm_lt_of_quotient_norm_lt U _ h2)
    have hall := (eventually_all_finset (Finset.range (n+1))).mpr
      (fun m hm => herr m (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hm))
    filter_upwards [hz,hall] with k hk hkall
    exact ⟨hk,fun m hm => hkall m (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨j,hj,hjP⟩ := kernel_diagonal_choice U hfree P hP
  let z : L := ⟨fun k => b (j k) k,memℓp_infty_iff.mpr ⟨1,by
    rintro _ ⟨k,rfl⟩; exact hbn (j k) k⟩⟩
  have hlim : Tendsto (fun k => e (j k)) (U : Filter ℕ) (𝓝 0) := he0.comp hj
  have hznull : normToTracial U (NormUltra.QuotientAlgebra.mk U z)=0 := by
    rw [normToTracial_mk,sequenceQuotientMap_apply,familyQuotientMap_eq_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => familyTwoNorm_nonneg T _) _ hlim
    filter_upwards [hjP] with k hk
    exact hk.1.le
  have hzpos : 0≤NormUltra.QuotientAlgebra.mk U z := by
    let r : L := ⟨fun k => CFC.sqrt (z k),memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨k,rfl⟩
      change ‖CFC.sqrt (b (j k) k)‖≤(1:ℝ)
      rw [CFC.norm_sqrt _ (hbp (j k) k)]
      exact Real.sqrt_le_one.mpr (hbn (j k) k)⟩⟩
    have hr : star r*r=z := by
      apply Subtype.ext
      funext k
      change star (CFC.sqrt (b (j k) k))*CFC.sqrt (b (j k) k)=b (j k) k
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (hbp (j k) k)]
    rw [←hr,NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_star]
    exact star_mul_self_nonneg _
  refine ⟨NormUltra.QuotientAlgebra.mk U z,hznull,hzpos,
    (NormUltra.QuotientAlgebra.norm_mk_le z).trans (lp.norm_le_of_forall_le zero_le_one (fun k => hbn (j k) k)),?_,?_⟩
  · intro m
    have hzero : c m-z*c m∈NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul 2)
      filter_upwards [hjP,hj (eventually_ge_atTop m)] with k hk hmk
      exact (hk.2 m hmk).1.le
    have hz := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (U := U) (c m) (z*c m)).mpr hzero
    rw [NormUltra.QuotientAlgebra.mk_mul,hc m] at hz
    exact hz.symm
  · intro m
    have hzero : a m*z-z*a m∈NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul 2)
      filter_upwards [hjP,hj (eventually_ge_atTop m)] with k hk hmk
      exact (hk.2 m hmk).2.le
    have hz := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (U := U) (a m*z) (z*a m)).mpr hzero
    rwa [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_mul,ha m] at hz

end

section
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem normToTracial_central_surjective (hfree : (U : Filter ℕ) ≤ atTop)
    (y : FamilyUltrapower T U) (hy : ∀ a : A, y*quotientInclusion U a=quotientInclusion U a*y) :
    ∃ z : N, normToTracial U z=y ∧ ∀ a : A, z*normInclusion U a=normInclusion U a*z := by
  obtain ⟨v,hv⟩ := normToTracial_surjective U hfree y
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let x : ℕ → N := fun m => normInclusion U (a m)
  let w : ℕ → N := fun m => v*x m-x m*v
  have hw (m : ℕ) : normToTracial U (w m)=0 := by
    simp only [w,x,map_sub,map_mul,hv,normToTracial_inclusion,hy,sub_self]
  obtain ⟨d,hd,_hdp,_hdn,hdw,hdx⟩ := trace_kernel_sigma_ideal U hfree x w hw
  have hcomm (m : ℕ) : (v-d*v)*x m=x m*(v-d*v) := by
    apply sub_eq_zero.mp
    calc
      (v-d*v)*x m-x m*(v-d*v) = w m-d*w m+(x m*d-d*x m)*v := by dsimp [w]; noncomm_ring
      _ = 0 := by rw [hdw m,hdx m,sub_self,sub_self,zero_mul,add_zero]
  refine ⟨v-d*v,?_,?_⟩
  · simp only [map_sub,map_mul,hd,zero_mul,sub_zero,hv]
  · have hi : Continuous (normInclusion (A := A) U) := by fun_prop
    have heq : (fun b : A => (v-d*v)*normInclusion U b) =
        (fun b : A => normInclusion U b*(v-d*v)) :=
      ha.equalizer (continuous_const.mul hi) (hi.mul continuous_const) (funext hcomm)
    exact fun b => congrFun heq b

end

open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem exists_norm_central_local_unit (hfree : (U : Filter ℕ) ≤ atTop) :
    ∃ u : N, 0≤u ∧ ‖u‖≤1 ∧ ∀ a : A,
      u*normInclusion U a=normInclusion U a ∧ normInclusion U a*u=normInclusion U a := by
  obtain ⟨b,hbp,hbn,hb⟩ := SequentialApproximateUnit.exists_sequence (A := A)
  let B : lp (fun _ : ℕ => A) ∞ := ⟨b,memℓp_infty ⟨1,by rintro _ ⟨n,rfl⟩; exact hbn n⟩⟩
  let u := NormUltra.QuotientAlgebra.mk U B
  have hup : 0≤u := by
    let r : lp (fun _ : ℕ => A) ∞ := ⟨fun n => CFC.sqrt (b n), memℓp_infty ⟨1,by
      rintro _ ⟨n,rfl⟩
      change ‖CFC.sqrt (b n)‖≤(1:ℝ)
      rw [CFC.norm_sqrt _ (hbp n)]
      exact Real.sqrt_le_one.mpr (hbn n)⟩⟩
    have heq : B=star r*r := by
      ext n
      change b n=star (CFC.sqrt (b n))*CFC.sqrt (b n)
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (hbp n)]
    change 0≤NormUltra.QuotientAlgebra.mk U B
    rw [heq,NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_star]
    exact star_mul_self_nonneg _
  refine ⟨u,hup,(NormUltra.QuotientAlgebra.norm_mk_le B).trans
    (lp.norm_le_of_forall_le zero_le_one hbn),?_⟩
  intro a
  constructor
  · change NormUltra.QuotientAlgebra.mk U (B*boundedConstant (A := A) a)=
      NormUltra.QuotientAlgebra.mk U (boundedConstant (A := A) a)
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff _ _).mpr
    change Tendsto (fun n => ‖b n*a-a‖) (U : Filter ℕ) (𝓝 0)
    simpa only [sub_self,norm_zero] using ((hb a).1.sub_const a).norm.mono_left hfree
  · change NormUltra.QuotientAlgebra.mk U (boundedConstant (A := A) a*B)=
      NormUltra.QuotientAlgebra.mk U (boundedConstant (A := A) a)
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff _ _).mpr
    change Tendsto (fun n => ‖a*b n-a‖) (U : Filter ℕ) (𝓝 0)
    simpa only [sub_self,norm_zero] using ((hb a).2.sub_const a).norm.mono_left hfree

end NonunitalGamma
end

end OAI
