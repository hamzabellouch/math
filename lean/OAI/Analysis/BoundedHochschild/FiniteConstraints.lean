import Mathlib
import OAI.Analysis.BoundedHochschild.NormalModulus

namespace OAI

/-! Finite cocycle constraints and exactness for bounded primitives. -/

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.smul {a p : M} (hp : IsSupportProjection a p)
    (r : ℝ) (hr : r ≠ 0) : IsSupportProjection (r • a) p := by
  refine ⟨hp.proj,?_,?_,?_⟩
  · rw [mul_smul_comm,hp.left]
  · rw [smul_mul_assoc,hp.right]
  · intro x hx
    apply hp.annihilate x
    rw [smul_mul_assoc,smul_eq_zero] at hx
    exact hx.resolve_left hr

omit [StarOrderedRing M] in
include htr in
lemma trace_mul_pow_swap (a b : M) (n : ℕ) : τ ((a*b)^n)=τ ((b*a)^n) := by
  cases n with
  | zero => simp only [pow_zero]
  | succ n => rw [pow_succ,← mul_assoc,htr,mul_pow_mul,← mul_assoc,← pow_succ']

omit [StarOrderedRing M] in
lemma trace_one_sub_pow {a b : M} (h : ∀ n : ℕ, τ (a^n)=τ (b^n)) (n : ℕ) :
    τ ((1-a)^n)=τ ((1-b)^n) := by
  have hn (k : ℕ) : τ ((-a)^k)=τ ((-b)^k) := by
    rw [show -a=(-1:ℂ) • a by simp,show -b=(-1:ℂ) • b by simp,
      smul_pow,smul_pow,map_smul,map_smul,h]
  rw [sub_eq_add_neg,sub_eq_add_neg,(Commute.one_left (-a)).add_pow,
    (Commute.one_left (-b)).add_pow,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [one_pow,one_mul,← nsmul_eq_mul',map_nsmul,hn]

include e hL hτ htr hfaith in
lemma support_trace_eq_of_moments (a b p q : M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hp : IsSupportProjection a p)
    (hq : IsSupportProjection b q) (ht : ∀ n : ℕ, τ (a^n)=τ (b^n)) : τ p=τ q := by
  obtain ⟨p',hp',hpt⟩ := exists_support_contraction e τ hL hτ htr hfaith a ha ha1
  obtain ⟨q',hq',hqt⟩ := exists_support_contraction e τ hL hτ htr hfaith b hb hb1
  have hp'p : p'=p := hp'.unique hp
  have hq'q : q'=q := hq'.unique hq
  subst p'; subst q'
  have hpa : ∀ n : ℕ, ‖1-(1-a)^n‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by
      have h := norm_pow_pos_contraction (1-a) (sub_nonneg.mpr ha1) (sub_le_self _ ha) n
      have h1 : ‖(1:M)‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
      linarith)
  have hqa : ∀ n : ℕ, ‖1-(1-b)^n‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by
      have h := norm_pow_pos_contraction (1-b) (sub_nonneg.mpr hb1) (sub_le_self _ hb) n
      have h1 : ‖(1:M)‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
      linarith)
  apply tendsto_nhds_unique (trace_predual_tendsto e τ hτ
    (hpt.predual e τ hL hτ hfaith 2 hpa))
  convert trace_predual_tendsto e τ hτ (hqt.predual e τ hL hτ hfaith 2 hqa) using 1
  ext n
  simp only [map_sub,trace_one_sub_pow τ ht]

include e hL hτ htr hfaith in
 

theorem support_trace_star_mul_self (x p q : M)
    (hp : IsSupportProjection (star x*x) p) (hq : IsSupportProjection (x*star x) q) :
    τ p=τ q := by
  let r : ℝ := (‖x‖^2+1)⁻¹
  have hd : 0 < ‖x‖^2+1 := by positivity
  have hr : 0 < r := inv_pos.mpr hd
  have hpos : 0 ≤ r • (star x*x) := smul_nonneg hr.le (star_mul_self_nonneg x)
  have hpos' : 0 ≤ r • (x*star x) := smul_nonneg hr.le (mul_star_self_nonneg x)
  have hnorm : ‖r • (star x*x)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,CStarRing.norm_star_mul_self]
    exact (inv_mul_le_one₀ hd).mpr (by linarith)
  have hnorm' : ‖r • (x*star x)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,CStarRing.norm_self_mul_star]
    exact (inv_mul_le_one₀ hd).mpr (by linarith)
  apply support_trace_eq_of_moments e τ hL hτ htr hfaith _ _ p q hpos hpos'
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hnorm)
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos').mp hnorm')
    (hp.smul r hr.ne') (hq.smul r hr.ne')
  intro n
  simp only [smul_pow,← Complex.coe_smul,map_smul,trace_mul_pow_swap τ htr (star x) x]

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.star_mul_self_right {x p : M}
    (hp : IsSupportProjection (star x*x) p) : x*p=x := by
  have h : star (x*(1-p))*(x*(1-p))=0 := by
    rw [star_mul,star_sub,star_one,hp.proj.isSelfAdjoint.star_eq]
    calc
      (1-p)*star x*(x*(1-p)) = (1-p)*((star x*x)*(1-p)) := by simp only [mul_assoc]
      _ = 0 := by rw [mul_sub,mul_one,hp.right,sub_self,mul_zero]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp h
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hz

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.mul_star_self_left {x p : M}
    (hp : IsSupportProjection (x*star x) p) : p*x=x := by
  have hh : star x*p=star x := IsSupportProjection.star_mul_self_right
    (x := star x) (by simpa only [star_star] using hp)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq] using congrArg Star.star hh

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

lemma IsSupportProjection.left_le {x r p : M}
    (hr : IsSupportProjection (x*star x) r) (hp : IsStarProjection p) (hpx : p*x=x) :
    r ≤ p := by
  apply hr.le_of_support hp
  have hx : star x*p=star x := by
    simpa only [star_mul,star_star,hp.isSelfAdjoint.star_eq] using congrArg Star.star hpx
  rw [mul_assoc,hx]

lemma IsSupportProjection.right_le {x r p : M}
    (hr : IsSupportProjection (star x*x) r) (hp : IsStarProjection p) (hxp : x*p=x) :
    r ≤ p := by
  apply hr.le_of_support hp
  rw [mul_assoc,hxp]

include e hL hτ htr hfaith in
 

theorem exists_projection_join (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ s : M, IsStarProjection s ∧ p ≤ s ∧ q ≤ s ∧
      (∀ z : M, IsStarProjection z → p ≤ z → q ≤ z → s ≤ z) ∧
      (τ s).re ≤ (τ p).re+(τ q).re := by
  let x := (1-p)*q
  obtain ⟨r,hr⟩ := exists_support_projection e τ hL hτ htr hfaith (x*star x)
    (mul_star_self_nonneg x)
  obtain ⟨t,ht⟩ := exists_support_projection e τ hL hτ htr hfaith (star x*x)
    (star_mul_self_nonneg x)
  have hpx : (1-p)*x=x := by dsimp [x]; rw [← mul_assoc,hp.one_sub.isIdempotentElem.eq]
  have hxq : x*q=x := by dsimp [x]; rw [mul_assoc,hq.isIdempotentElem.eq]
  have hrp : r ≤ 1-p := hr.left_le hp.one_sub hpx
  have htq : t ≤ q := ht.right_le hq hxq
  have hpr : p*r=0 := by
    have hh := (hr.proj.le_iff_mul_eq_right hp.one_sub).mp hrp
    simpa only [sub_mul,one_mul,sub_eq_self] using hh
  have hrp0 : r*p=0 := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hr.proj.isSelfAdjoint.star_eq,star_zero]
      using congrArg Star.star hpr
  have hs : IsStarProjection (p+r) := hp.add hr.proj hpr
  have hp_le : p ≤ p+r := (hp.le_iff_mul_eq_left hs).mpr (by
    rw [mul_add,hp.isIdempotentElem.eq,hpr,add_zero])
  have hrq : r*q=(1-p)*q := by
    have hh := hr.mul_star_self_left
    dsimp [x] at hh
    rw [← mul_assoc,mul_sub,mul_one,hrp0,sub_zero] at hh
    exact hh
  have hq_le : q ≤ p+r := (hq.le_iff_mul_eq_right hs).mpr (by
    rw [add_mul,hrq,sub_mul,one_mul,add_sub_cancel])
  refine ⟨p+r,hs,hp_le,hq_le,?_,?_⟩
  · intro z hz hpz hqz
    have hzp : z*p=p := (hp.le_iff_mul_eq_right hz).mp hpz
    have hzq : z*q=q := (hq.le_iff_mul_eq_right hz).mp hqz
    have hzx : z*x=x := by
      dsimp [x]
      rw [← mul_assoc,mul_sub,mul_one,sub_mul,hzq,hzp,sub_mul,one_mul]
    have hrz : r ≤ z := hr.left_le hz hzx
    apply (hs.le_iff_mul_eq_right hz).mpr
    rw [mul_add,hzp,(hr.proj.le_iff_mul_eq_right hz).mp hrz]
  · have hrt : τ r=τ t := (support_trace_star_mul_self e τ hL hτ htr hfaith x t r ht hr).symm
    rw [map_add,Complex.add_re,hrt]
    exact add_le_add le_rfl (Complex.re_le_re (τ.monotone htq))

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include e hL hτ htr hfaith in
lemma exists_monotone_projection_limit (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (ham : Monotone a) :
    ∃ p : M, IsStarProjection p ∧ GNSTendsto τ a atTop p ∧ (∀ n, a n ≤ p) ∧
      ∀ q : M, IsStarProjection q → (∀ n, a n ≤ q) → p ≤ q := by
  obtain ⟨p,_hp,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (ha n).norm_le _)
    (monotone_contractions_preGNS_cauchy τ a (fun n => (ha n).nonneg)
      (fun n => (ha n).le_one) ham)
  change GNSTendsto τ a atTop p at ht
  have hstar : star p=p := by
    apply GNSTendsto.unique τ hfaith (ht.star τ htr)
    simpa only [(ha _).isSelfAdjoint.star_eq] using ht
  have hmul : p*p=p := by
    apply GNSTendsto.unique τ hfaith (ht.mul τ htr ht 1 (fun n => (ha n).norm_le _))
    simpa only [(ha _).isIdempotentElem.eq] using ht
  have hp : IsStarProjection p := ⟨hmul,hstar⟩
  refine ⟨p,hp,ht,?_,?_⟩
  · intro n
    apply ((ha n).le_iff_mul_eq_left hp).mpr
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (a n) (atTop : Filter ℕ)).mul τ htr ht 1
        (fun _ => (ha n).norm_le _))
    change Tendsto (fun m => ‖τ.toPreGNS (a n*a m-a n)‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [((ha n).le_iff_mul_eq_left (ha m)).mp (ham hm),sub_self,map_zero,norm_zero]
  · intro q hq haq
    apply (hp.le_iff_mul_eq_left hq).mpr
    apply GNSTendsto.unique τ hfaith
      (ht.mul τ htr (GNSTendsto.const τ q atTop) 1 (fun n => (ha n).norm_le _))
    simpa only [((ha _).le_iff_mul_eq_left hq).mp (haq _)] using ht

include e hL hτ htr hfaith in
lemma exists_projection_finjoin (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n)) (n : ℕ) :
    ∃ p : M, IsStarProjection p ∧ (∀ i < n, a i ≤ p) ∧
      (∀ q : M, IsStarProjection q → (∀ i < n, a i ≤ q) → p ≤ q) ∧
      (τ p).re ≤ ∑ i ∈ Finset.range n, (τ (a i)).re := by
  induction n with
  | zero =>
    refine ⟨0,IsStarProjection.zero M,by simp,?_,by simp⟩
    intro q hq _h
    exact hq.nonneg
  | succ n ih =>
    obtain ⟨p,hp,had,hl,ht⟩ := ih
    obtain ⟨q,hq,hpq,hanq,hql,hqt⟩ := exists_projection_join e τ hL hτ htr hfaith p (a n) hp (ha n)
    refine ⟨q,hq,?_,?_,?_⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h|rfl
      · exact (had i h).trans hpq
      · exact hanq
    · intro z hz haz
      apply hql z hz (hl z hz (fun i hi => haz i (Nat.lt_succ_of_lt hi)))
      exact haz n (Nat.lt_succ_self n)
    · rw [Finset.sum_range_succ]
      exact hqt.trans (add_le_add ht le_rfl)

include e hL hτ htr hfaith in
 

theorem exists_projection_countable_join (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (C : ℝ) (hC : ∀ n : ℕ, (∑ i ∈ Finset.range n, (τ (a i)).re) ≤ C) :
    ∃ p : M, IsStarProjection p ∧ (∀ n, a n ≤ p) ∧
      (∀ q : M, IsStarProjection q → (∀ n, a n ≤ q) → p ≤ q) ∧ (τ p).re ≤ C := by
  classical
  choose b hb had hl ht using exists_projection_finjoin e τ hL hτ htr hfaith a ha
  have hbm : Monotone b := by
    intro n m hnm
    exact hl n (b m) (hb m) (fun i hi => had m i (hi.trans_le hnm))
  obtain ⟨p,hp,hpt,hbp,hpl⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith b hb hbm
  refine ⟨p,hp,?_,?_,?_⟩
  · intro n
    exact (had (n+1) n (Nat.lt_succ_self n)).trans (hbp (n+1))
  · intro q hq haq
    exact hpl q hq (fun n => hl n q hq (fun i _hi => haq i))
  · exact le_of_tendsto
      ((Complex.continuous_re.tendsto (τ p)).comp
        (trace_predual_tendsto e τ hτ (hpt.predual e τ hL hτ hfaith 1
          (fun n => (hb n).norm_le _))))
      (Filter.Eventually.of_forall (fun n => (ht n).trans (hC n)))

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

lemma trace_star_mul_self_re (x : M) : (τ (star x*x)).re=‖τ.toPreGNS x‖^2 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS x))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re]
    using h.symm

include e hL hτ htr hfaith in
 

theorem exists_spectral_cut (x : M) (α : ℝ) (hα : 0 < α) :
    ∃ p : M, IsStarProjection p ∧ ‖x-x*p‖ ≤ α ∧
      (τ p).re ≤ ‖τ.toPreGNS x‖^2 / α^2 := by
  let a := star x*x
  let b := a-(α^2) • (1:M)
  let c := b⁺
  let d := b⁻
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg x)
  have hsb : IsSelfAdjoint b := hsa.sub (IsSelfAdjoint.of_nonneg
    (smul_nonneg (sq_nonneg α) zero_le_one))
  have hc : 0 ≤ c := CFC.posPart_nonneg b
  have hd : 0 ≤ d := CFC.negPart_nonneg b
  have hcd : c*d=0 := CFC.posPart_mul_negPart b
  have had : a=c-d+(α^2) • 1 := by
    have hh := CFC.posPart_sub_negPart b hsb
    dsimp [c,d,b] at *
    rw [hh,sub_add_cancel]
  obtain ⟨p,hp⟩ := exists_support_projection e τ hL hτ htr hfaith c hc
  have hpd : p*d=0 := hp.annihilate d hcd
  have hdp : d*p=0 := by
    simpa only [star_mul,hp.proj.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hd).star_eq,
      star_zero] using congrArg Star.star hpd
  have hap : a*p=c+(α^2) • p := by
    rw [had,add_mul,sub_mul,hp.right,hdp,smul_mul_assoc,one_mul,sub_zero]
  have hcomp : a*(1-p)=(α^2) • (1-p)-d := by
    rw [mul_sub,mul_one,hap,had,smul_sub]
    abel
  let z := x*(1-p)
  have hzz : star z*z=(α^2) • (1-p)-d := by
    dsimp [z]
    rw [star_mul,star_sub,star_one,hp.proj.isSelfAdjoint.star_eq]
    calc
      (1-p)*star x*(x*(1-p)) = (1-p)*(a*(1-p)) := by dsimp [a]; simp only [mul_assoc]
      _ = (α^2) • (1-p)-d := by
        rw [hcomp,mul_sub,mul_smul_comm,hp.proj.one_sub.isIdempotentElem.eq,
          sub_mul,one_mul,hpd,sub_zero]
  have hzzle : star z*z ≤ (α^2) • (1:M) := by
    rw [hzz]
    exact (sub_le_self _ hd).trans (smul_le_smul_of_nonneg_left hp.proj.one_sub.le_one (sq_nonneg α))
  have hz : ‖z‖ ≤ α := by
    have hh : ‖star z*z‖ ≤ α^2 := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg α)
      (star_mul_self_nonneg z)).mpr (by simpa only [Algebra.algebraMap_eq_smul_one] using hzzle)
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg z]
  have htd : (α^2) • p ≤ a := by
    have hpos : 0 ≤ a-a*p := by
      have heq : a-a*p=star z*z := by rw [hzz,← hcomp,mul_sub,mul_one]
      rw [heq]
      exact star_mul_self_nonneg z
    have hh : (α^2) • p ≤ a*p := by rw [hap]; exact le_add_of_nonneg_left hc
    exact hh.trans (sub_nonneg.mp hpos)
  have htrace : (τ ((α^2) • p)).re ≤ (τ a).re := Complex.re_le_re (τ.monotone htd)
  have hsmall : (τ p).re ≤ ‖τ.toPreGNS x‖^2 / α^2 := by
    rw [← Complex.coe_smul,map_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] at htrace
    rw [le_div_iff₀ (sq_pos_of_pos hα),mul_comm]
    simpa only [a,trace_star_mul_self_re τ] using htrace
  refine ⟨p,hp.proj,?_,hsmall⟩
  simpa only [z,mul_sub,mul_one] using hz

include e hL hτ htr hfaith in
 

theorem exists_small_two_sided_support (x : M) (α : ℝ) (hα : 0 < α) :
    ∃ y p : M, IsStarProjection p ∧ p*y=y ∧ y*p=y ∧ ‖y‖ ≤ ‖x‖ ∧
      ‖x-y‖ ≤ α ∧ (τ p).re ≤ 2*(‖τ.toPreGNS x‖^2 / α^2) := by
  obtain ⟨r,hr,hdiff,hsmall⟩ := exists_spectral_cut e τ hL hτ htr hfaith x α hα
  let y := x*r
  obtain ⟨q,hq⟩ := exists_support_projection e τ hL hτ htr hfaith (y*star y)
    (mul_star_self_nonneg y)
  obtain ⟨t,ht⟩ := exists_support_projection e τ hL hτ htr hfaith (star y*y)
    (star_mul_self_nonneg y)
  have hyr : y*r=y := by dsimp [y]; rw [mul_assoc,hr.isIdempotentElem.eq]
  have htrle : t ≤ r := ht.right_le hr hyr
  have hqtrace : (τ q).re ≤ (τ r).re := by
    rw [← support_trace_star_mul_self e τ hL hτ htr hfaith y t q ht hq]
    exact Complex.re_le_re (τ.monotone htrle)
  obtain ⟨p,hp,hrp,hqp,_hmin,hptrace⟩ :=
    exists_projection_join e τ hL hτ htr hfaith r q hr hq.proj
  refine ⟨y,p,hp,?_,?_,?_,hdiff,?_⟩
  · calc
      p*y = p*(q*y) := by rw [hq.mul_star_self_left]
      _ = y := by rw [← mul_assoc,(hq.proj.le_iff_mul_eq_right hp).mp hqp,hq.mul_star_self_left]
  · calc
      y*p = (y*r)*p := by rw [hyr]
      _ = y := by rw [mul_assoc,(hr.le_iff_mul_eq_left hp).mp hrp,hyr]
  · exact (norm_mul_le x r).trans (by nlinarith [norm_nonneg x,hr.norm_le r])
  · linarith

end BoundedHochschild
end

end OAI
