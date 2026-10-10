import Mathlib
import OAI.Analysis.BoundedHochschild.PrimitiveAverages

namespace OAI

/-! Normal cochains, bounded-ball continuity and primitive construction. -/

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
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma preGNS_zero_of_predual_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (ha : Tendsto (fun i => ‖τ.toPreGNS (a i)‖) l (𝓝 0))
    (hb : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [zero_add] using preGNS_norm_le_of_predual_tendsto e τ hL hτ ε hε.le
    (ha.eventually (ge_mem_nhds hε)) hb

 

theorem predual_tendsto_of_preGNS
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) {b : M}
    (hb : Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)) :
    PredualTendsto e a l b := by
  intro z
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro u hu
  obtain ⟨c,_hc,ht⟩ := exists_predual_ultralimit e u a C ha
  have hzero := preGNS_zero_of_predual_limit e τ hL hτ (hb.mono_left hu)
    (predual_tendsto_sub e ht (predual_tendsto_const e b (u : Filter I)))
  have hcb : c=b := by
    apply sub_eq_zero.mp
    exact (preGNS_norm_eq_zero_iff τ hfaith (c-b)).mp hzero
  simpa only [hcb] using ht z

 

theorem exists_bounded_preGNS_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : ℕ → M} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C)
    (hc : CauchySeq (fun i => τ.toPreGNS (a i))) :
    ∃ b : M, ‖b‖ ≤ C ∧ Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) atTop (𝓝 0) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  refine ⟨b,hb,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hsmall : ∀ᶠ m in (u : Filter ℕ), ‖τ.toPreGNS (a n-a m)‖ ≤ ε/2 := by
    apply hu
    filter_upwards [eventually_ge_atTop N] with m hm
    simpa only [map_sub,← dist_eq_norm] using (hN n hn m hm).le
  have hbound := preGNS_norm_le_of_predual_tendsto e τ hL hτ (ε/2) (half_pos hε).le
    hsmall (predual_tendsto_sub e (predual_tendsto_const e (a n) (u : Filter ℕ)) ht)
  simpa only [Real.dist_eq,sub_zero,abs_norm] using hbound.trans_lt (half_lt_self hε)

lemma preGNS_sq_le_trace (a : M) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖τ.toPreGNS a‖^2 ≤ (τ a).re := by
  have hs := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,
    (IsSelfAdjoint.of_nonneg ha).star_eq,← Complex.ofReal_pow,Complex.ofReal_re] at hs
  rw [hs]
  apply Complex.re_le_re
  apply τ.monotone
  simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone ha1 ha (show 1 ≤ 2 by omega)

lemma monotone_contractions_preGNS_cauchy (a : ℕ → M) (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n ≤ 1) (hm : Monotone a) : CauchySeq (fun n => τ.toPreGNS (a n)) := by
  have hmono : Monotone (fun n => (τ (a n)).re) := fun n m hnm =>
    Complex.re_le_re (τ.monotone (hm hnm))
  have hbdd : BddAbove (Set.range (fun n => (τ (a n)).re)) :=
    ⟨(τ 1).re,fun _ ⟨n,hn⟩ => hn ▸ Complex.re_le_re (τ.monotone (h1 n))⟩
  have hc := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hd0 : 0 ≤ a n-a N := sub_nonneg.mpr (hm hn)
  have hd1 : a n-a N ≤ 1 := (sub_le_self _ (h0 N)).trans (h1 n)
  have hsq := preGNS_sq_le_trace τ (a n-a N) hd0 hd1
  have hdiff := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hn))] at hdiff
  simp only [map_sub,Complex.sub_re] at hsq
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (τ.toPreGNS (a n)-τ.toPreGNS (a N))]

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ)

def GNSTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)

lemma GNSTendsto.const (b : M) (l : Filter I) : GNSTendsto τ (fun _ => b) l b := by
  simp only [GNSTendsto,sub_self,map_zero,norm_zero]
  exact tendsto_const_nhds

lemma GNSTendsto.add {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i+c i) l (b+d) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa only [add_zero] using Filter.Tendsto.add ha hc)
  rw [show a i+c i-(b+d)=(a i-b)+(c i-d) by abel,map_add]
  exact norm_add_le _ _

lemma GNSTendsto.neg {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => -a i) l (-b) := by
  simpa only [GNSTendsto,neg_sub_neg,← neg_sub (a := b),map_neg,norm_neg] using ha

lemma GNSTendsto.sub {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i-c i) l (b-d) := by
  simpa only [sub_eq_add_neg] using ha.add τ (hc.neg τ)

lemma GNSTendsto.star (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => star (a i)) l (star b) := by
  simpa only [GNSTendsto,← star_sub,preGNS_norm_star τ htr] using ha

lemma GNSTendsto.mul (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C) :
    GNSTendsto τ (fun i => a i*c i) l (b*d) := by
  have ht := (hc.const_mul C).add (ha.const_mul ‖d‖)
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) ht
  rw [show a i*c i-b*d=a i*(c i-d)+(a i-b)*d by noncomm_ring,map_add]
  exact (norm_add_le _ _).trans (add_le_add
    ((preGNS_norm_mul_le τ _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
    (preGNS_norm_mul_right_le τ htr _ _))

lemma GNSTendsto.unique (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : GNSTendsto τ a l b) (hc : GNSTendsto τ a l c) : b=c := by
  have h : GNSTendsto τ (fun _ : I => (0:M)) l (b-c) := by
    simpa only [sub_self] using hb.sub τ hc
  have hz : ‖τ.toPreGNS (b-c)‖=0 := by
    have ht : Tendsto (fun _ : I => ‖τ.toPreGNS (b-c)‖) l (𝓝 0) := by
      simpa only [GNSTendsto,zero_sub,map_neg,norm_neg] using h
    exact tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaith _).mp hz)

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include hL hτ hfaith in
lemma GNSTendsto.predual {a : ℕ → M} {b : M} (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C)
    (ht : GNSTendsto τ a atTop b) : PredualTendsto e a atTop b :=
  predual_tendsto_of_preGNS e τ hL hτ hfaith C ha ht

lemma norm_pow_pos_contraction (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    ‖b^n‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg b n hb0)).mpr
  simpa only [pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n)

include e hL hτ htr hfaith in
 

theorem exists_power_projection (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ GNSTendsto τ (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : M, b*x=x → p*x=x := by
  let a : ℕ → M := fun n => 1-b^n
  have ha0 : ∀ n, 0 ≤ a n := fun n => sub_nonneg.mpr (by
    simpa only [pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n))
  have ha1 : ∀ n, a n ≤ 1 := fun n => sub_le_self _ (CStarAlgebra.pow_nonneg b n hb0)
  have ham : Monotone a := fun n m hnm => sub_le_sub_left
    (CStarAlgebra.pow_antitone hb1 hb0 hnm) 1
  obtain ⟨c,_hc,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (ha0 n)).mpr (ha1 n))
    (monotone_contractions_preGNS_cauchy τ a ha0 ha1 ham)
  let p : M := 1-c
  have hp : GNSTendsto τ (fun n : ℕ => b^n) atTop p := by
    simpa only [a,sub_sub_cancel] using (GNSTendsto.const τ (1:M) (atTop : Filter ℕ)).sub τ ht
  have hpstar : star p=p := by
    apply GNSTendsto.unique τ hfaith (hp.star τ htr)
    simpa only [star_pow,(IsSelfAdjoint.of_nonneg hb0).star_eq] using hp
  have htimes : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hpp : p*p=p := by
    apply GNSTendsto.unique τ hfaith (hp.mul τ htr hp 1 (norm_pow_pos_contraction b hb0 hb1))
    simpa only [GNSTendsto,Function.comp_def,two_mul,pow_add] using
      (show Tendsto (fun n : ℕ => ‖τ.toPreGNS (b^(2*n)-p)‖) atTop (𝓝 0) from hp.comp htimes)
  have hbp : b*p=p := by
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ b (atTop : Filter ℕ)).mul τ htr hp ‖b‖ (fun _ => le_rfl))
    simpa only [GNSTendsto,Function.comp_def,pow_succ'] using hp.comp (tendsto_add_atTop_nat 1)
  refine ⟨p,⟨hpp,hpstar⟩,hp,hbp,?_⟩
  intro x hx
  have hpow (n : ℕ) : b^n*x=x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hx]
  apply GNSTendsto.unique τ hfaith
    (hp.mul τ htr (GNSTendsto.const τ x atTop) 1 (norm_pow_pos_contraction b hb0 hb1))
  simpa only [hpow] using GNSTendsto.const τ x (atTop : Filter ℕ)

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

 

structure IsSupportProjection (a p : M) : Prop where
  proj : IsStarProjection p
  left : p*a=a
  right : a*p=a
  annihilate : ∀ x : M, a*x=0 → p*x=0

include e hL hτ htr hfaith in
lemma exists_support_contraction (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsSupportProjection a p ∧
      GNSTendsto τ (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection e τ hL hτ htr hfaith (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact (GNSTendsto.const τ 1 (atTop : Filter ℕ)).sub τ ht

include e hL hτ htr hfaith in
 

theorem exists_support_projection (a : M) (ha : 0 ≤ a) :
    ∃ p : M, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction e τ hL hτ htr hfaith (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : M => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : M => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

lemma IsSupportProjection.le_of_support {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsStarProjection q) (haq : a*q=a) : p ≤ q := by
  apply (hp.proj.le_iff_mul_eq_left hq).mpr
  have hh := hp.annihilate (1-q) (by simp only [mul_sub,mul_one,haq,sub_self])
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hh

lemma IsSupportProjection.unique {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsSupportProjection a q) : p=q :=
  le_antisymm (hp.le_of_support hq.proj hq.right) (hq.le_of_support hp.proj hp.right)

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.mul_eq_zero_iff {a p : M} (hp : IsSupportProjection a p) (x : M) :
    p*x=0 ↔ a*x=0 := by
  constructor
  · intro hx
    rw [← hp.right,mul_assoc,hx,mul_zero]
  · exact hp.annihilate x

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.commute {a p c : M} (hp : IsSupportProjection a p)
    (ha : IsSelfAdjoint a) (hc : Commute a c) : Commute p c := by
  have block (b : M) (hb : Commute a b) : p*b=p*b*p := by
    have hk : a*(b*(1-p))=0 := by
      rw [← mul_assoc,hb.eq,mul_assoc,mul_sub,mul_one,hp.right,sub_self,mul_zero]
    have hh := hp.annihilate (b*(1-p)) hk
    rw [← mul_assoc,mul_sub,mul_one,sub_eq_zero] at hh
    exact hh
  have hs : Commute a (star c) := by
    rw [commute_iff_eq]
    have hh := congrArg Star.star hc.eq
    simpa only [star_mul,ha.star_eq] using hh.symm
  have hh := congrArg Star.star (block (star c) hs)
  simp only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq] at hh
  rw [commute_iff_eq]
  exact (block c hc).trans (by simpa only [mul_assoc] using hh.symm)

end BoundedHochschild
end

end OAI
