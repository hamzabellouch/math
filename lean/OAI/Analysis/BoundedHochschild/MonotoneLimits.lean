import Mathlib
import OAI.Analysis.BoundedHochschild.StarPreduals

namespace OAI

/-! Monotone weak-star limits and bounded GNS limits. -/

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
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem nonneg_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, 0 ≤ a i) (ht : PredualTendsto e a l b) : 0 ≤ b := by
  have hs : PredualTendsto e (fun i => star (a i)) l b := by
    intro z
    apply (ht z).congr'
    filter_upwards [hp] with i hi
    rw [(IsSelfAdjoint.of_nonneg hi).star_eq]
  have hb : IsSelfAdjoint b := predual_tendsto_unique e (predual_tendsto_star e ht) hs
  let c := algebraMap ℝ M C
  have hc : 0 ≤ c := algebraMap_nonneg M hC
  have hac : ∀ᶠ i in l, ‖c-a i‖ ≤ C := by
    filter_upwards [ha,hp] with i hn hi
    have hai : a i ≤ c := (CStarAlgebra.norm_le_iff_le_algebraMap (a i) hC hi).mp hn
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (c-a i) hC (sub_nonneg.mpr hai)).mpr
      (sub_le_self _ hi)
  have hbc : ‖c-b‖ ≤ C := predual_norm_le e C hC hac
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  have hsa : IsSelfAdjoint (c-b) := (IsSelfAdjoint.of_nonneg hc).sub hb
  have hle : c-b ≤ c := hsa.le_algebraMap_norm_self.trans (algebraMap_mono M hbc)
  exact le_of_add_le_add_left (show c+0 ≤ c+b by
    simpa only [add_zero] using sub_le_iff_le_add.mp hle)

 
theorem le_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, a i ≤ c) (ht : PredualTendsto e a l b) : b ≤ c := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (‖c‖+C) (add_nonneg (norm_nonneg _) hC)
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  filter_upwards [ha] with i hi
  exact (norm_sub_le c (a i)).trans (by gcongr)

theorem ge_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, c ≤ a i) (ht : PredualTendsto e a l b) : c ≤ b := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (C+‖c‖) (add_nonneg hC (norm_nonneg _))
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e ht (predual_tendsto_const e c l))
  filter_upwards [ha] with i hi
  exact (norm_sub_le (a i) c).trans (by gcongr)

 

theorem exists_monotone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Monotone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ IsLUB (Set.range a) b ∧ PredualTendsto e a atTop b := by
  let u : Ultrafilter I := Ultrafilter.of atTop
  have hu : (u : Filter I) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  have hlu (v : Ultrafilter I) (hv : (v : Filter I) ≤ atTop) (c : M)
      (hc : PredualTendsto e a (v : Filter I) c) : IsLUB (Set.range a) c := by
    constructor
    · rintro _ ⟨i,rfl⟩
      apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact hv ((eventually_ge_atTop i).mono fun j hj => hm hj)
    · intro d hd
      apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact Eventually.of_forall fun i => hd (Set.mem_range_self i)
  have hbL := hlu u hu b ht
  refine ⟨b,hb,hbL,fun z => ?_⟩
  rw [Filter.tendsto_iff_ultrafilter]
  intro v hv
  obtain ⟨c,_hc,hct⟩ := exists_predual_ultralimit e v a C ha
  have hcb : c=b := (hlu v hv c hct).unique hbL
  exact hcb ▸ hct z

end HochschildSakai

 

open Filter Topology
namespace HochschildUltrafilter

 

theorem diagonal_rank (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ n, ∀ᶠ j in (ω : Filter ℕ), P n j) :
    ∃ r : ℕ → ℕ, Tendsto r (ω : Filter ℕ) atTop ∧ ∀ᶠ j in (ω : Filter ℕ), P (r j) j := by
  classical
  let r : ℕ → ℕ := fun j => Nat.findGreatest (fun n => P n j) j
  refine ⟨r,?_,?_⟩
  · apply Filter.tendsto_atTop.mpr
    intro n
    filter_upwards [hP n,hω (eventually_ge_atTop n)] with j hj hn
    exact Nat.le_findGreatest hn hj
  · filter_upwards [hP 0] with j hj
    exact Nat.findGreatest_spec (P := fun n => P n j) (Nat.zero_le j) hj

end HochschildUltrafilter

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open TracialUltrapower HochschildRigidity BoundedHochschild
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

lemma tendsto_quotient_preGNS_norm (a : ℕ →ᵇ A) :
    Tendsto (fun j => ‖τ.toPreGNS (a j)‖) (ω : Filter ℕ)
      (𝓝 ‖(quotientTrace τ h1 ω htr).toPreGNS (quotientHom τ h1 ω htr a)‖) := by
  rw [quotientTrace_preGNS_norm]
  exact tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω a

 

lemma quotient_norm_le_of_eventually (a : ℕ →ᵇ A) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ᶠ j in (ω : Filter ℕ), ‖a j‖ ≤ C) :
    ‖quotientHom τ h1 ω htr a‖ ≤ C := by
  classical
  let b : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun j => if ‖a j‖ ≤ C then a j else 0) C (fun j => by split_ifs <;> simp_all)
  have hb : ‖b‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr (fun j => by
    change ‖if ‖a j‖ ≤ C then a j else 0‖ ≤ C
    split_ifs <;> simp_all)
  have he : quotientHom τ h1 ω htr (a-b)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change a-b ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
    rw [mem_nullSubmodule]
    apply tendsto_const_nhds.congr'
    filter_upwards [ha] with j hj
    simp only [BoundedContinuousFunction.sub_apply]
    change (0:ℝ) = ‖τ.toPreGNS (a j - if ‖a j‖ ≤ C then a j else 0)‖
    simp only [ite_eq_left hj,sub_self,map_zero,norm_zero]
  have he' : quotientHom τ h1 ω htr a=quotientHom τ h1 ω htr b := by
    simpa only [map_sub,sub_eq_zero] using he
  rw [he']
  exact (HochschildCStarQuotient.norm_mk_le (ideal τ h1 ω htr) b).trans hb

 

theorem exists_bounded_GNS_limit (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Ultrapower τ h1 ω htr) (C : ℝ) (hx : ∀ n, ‖x n‖ ≤ C)
    (hc : CauchySeq (fun n => (quotientTrace τ h1 ω htr).toPreGNS (x n))) :
    ∃ b : Ultrapower τ h1 ω htr, ‖b‖ ≤ C ∧
      GNSTendsto (quotientTrace τ h1 ω htr) x atTop b := by
  classical
  let q := quotientHom τ h1 ω htr
  let T := quotientTrace τ h1 ω htr
  have hreps (n : ℕ) : ∃ a : ℕ →ᵇ A, q a=x n ∧ ‖a‖ < C+1/(n+1:ℝ) := by
    obtain ⟨a,ha,han⟩ := HochschildCStarQuotient.norm_mk_lt
      (ideal τ h1 ω htr) (x n) (show (0:ℝ)<1/(n+1:ℝ) by positivity)
    exact ⟨a,ha,han.trans_le (by linarith [hx n])⟩
  choose a ha han' using hreps
  have han (n : ℕ) : ‖a n‖ < C+1 := (han' n).trans_le (by
    have : 1/(n+1:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.le_add_left 1 n)
    linarith)
  let P : ℕ → ℕ → Prop := fun n j => ∀ k ≤ n,
    ‖τ.toPreGNS (a k j-a n j)‖ < ‖T.toPreGNS (x k-x n)‖ + 1/(n+1:ℝ)
  have hP (n : ℕ) : ∀ᶠ j in (ω : Filter ℕ), P n j := by
    have ht (k : ℕ) := tendsto_quotient_preGNS_norm τ h1 ω htr (a k-a n)
    have he : ∀ᶠ j in (ω : Filter ℕ), ∀ k ∈ Finset.range (n+1),
        ‖τ.toPreGNS (a k j-a n j)‖ < ‖T.toPreGNS (x k-x n)‖ + 1/(n+1:ℝ) := by
      rw [Filter.eventually_all_finset]
      intro k _hk
      have ht' : Tendsto (fun j => ‖τ.toPreGNS (a k j-a n j)‖) (ω : Filter ℕ)
          (𝓝 ‖T.toPreGNS (x k-x n)‖) := by
        simpa only [BoundedContinuousFunction.sub_apply,map_sub,← show q = quotientHom τ h1 ω htr from rfl,ha] using ht k
      exact ht'.eventually_lt_const (lt_add_of_pos_right _ (by positivity))
    filter_upwards [he] with j hj
    intro k hk
    exact hj k (Finset.mem_range.mpr (by omega))
  obtain ⟨r,hr,hrP⟩ := HochschildUltrafilter.diagonal_rank ω hω P hP
  let b : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun j => a (r j) j) (C+1) (fun j =>
      (BoundedContinuousFunction.norm_coe_le_norm (a (r j)) j).trans (han (r j)).le)
  have htol : Tendsto (fun j => 1/(r j+1:ℝ)) (ω : Filter ℕ) (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hr
  have hb : ‖q b‖ ≤ C := by
    apply le_of_forall_pos_le_add
    intro ε hε
    apply quotient_norm_le_of_eventually τ h1 ω htr b (C+ε)
      (by linarith [norm_nonneg (x 0),hx 0])
    filter_upwards [htol.eventually_lt_const hε] with j hj
    exact (BoundedContinuousFunction.norm_coe_le_norm (a (r j)) j).trans
      ((han' (r j)).trans_le (by linarith)).le
  refine ⟨q b,hb,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (ε/4) (by positivity)
  refine ⟨N,fun k hk => ?_⟩
  have he : ∀ᶠ j in (ω : Filter ℕ), ‖τ.toPreGNS (a k j-b j)‖ ≤ ε/2 := by
    filter_upwards [hrP,hr.eventually (eventually_ge_atTop k),
      htol.eventually_lt_const (show (0:ℝ)<ε/4 by positivity)] with j hj hjk hjε
    have hsmall : ‖T.toPreGNS (x k-x (r j))‖ < ε/4 := by
      simpa only [map_sub,← dist_eq_norm] using hN k hk (r j) (hk.trans hjk)
    have hj' := hj k hjk
    change ‖τ.toPreGNS (a k j-a (r j) j)‖ ≤ ε/2
    linarith
  have ht : Tendsto (fun j => ‖τ.toPreGNS (a k j-b j)‖) (ω : Filter ℕ)
      (𝓝 ‖T.toPreGNS (x k-q b)‖) := by
    simpa only [BoundedContinuousFunction.sub_apply,map_sub,← show q = quotientHom τ h1 ω htr from rfl,ha] using tendsto_quotient_preGNS_norm τ h1 ω htr (a k-b)
  have hbound : ‖T.toPreGNS (x k-q b)‖ ≤ ε/2 := le_of_tendsto ht he
  simpa only [Real.dist_eq,sub_zero,abs_norm] using hbound.trans_lt (half_lt_self hε)

end HochschildUltrapower
end

end OAI
