import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Pullback
import OAI.Analysis.JiangSu.Nonunital.TraceRays
import OAI.Analysis.JiangSu.Nonunital.CommonMinorant
import OAI.Analysis.JiangSu.Nonunital.IdealDensity

namespace OAI

noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ENNReal NNReal ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def NormalizedTrace.weight (τ : NormalizedTrace A) : ExtendedTrace A :=
  functionalWeight τ.functional τ.tracial

lemma NormalizedTrace.weight_rank (τ : NormalizedTrace A) (a : A) (ha : 0 ≤ a) :
    τ.weight.rank ⟨a,ha⟩=τ.rank a := by
  have ht := Pureness.source_root_trace_tendsto_rank τ.unitized
    (Unitization.inr a) (Unitization.inr_nonneg_iff.mpr ha)
  change τ.weight.rank ⟨a,ha⟩ = Pureness.normalizedRootRank τ.unitized (Unitization.inr a)
  apply tendsto_nhds_unique (τ.weight.tendsto_roots_rank_all ⟨a,ha⟩)
  convert ht using 1
  funext n
  have he := congrArg Subtype.val (Positive.map_power
    (Unitization.inrNonUnitalStarAlgHom ℂ A) ⟨a,ha⟩ (Positive.rootExponent n)
    (Positive.rootExponent_pos n))
  change Unitization.inr (CFC.nnrpow a (Positive.rootExponent n))=
    CFC.nnrpow (Unitization.inr a) (Positive.rootExponent n) at he
  simp only [Positive.rootExponent, one_div] at he ⊢
  change ENNReal.ofReal (τ.functional (CFC.nnrpow a (((n : ℝ≥0)+1)⁻¹))).re=
    ENNReal.ofReal (τ.unitized.functional (CFC.nnrpow (Unitization.inr a) (((n : ℝ≥0)+1)⁻¹))).re
  rw [←he, NormalizedTrace.unitized_inr]

end NonunitalGamma

namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_norm_le (τ : NormalizedTrace A) (a : A) : ‖τ.functional a‖ ≤ ‖a‖ := by
  have ht := (positiveFunctionalCLM τ.functional).le_opNorm a
  change ‖τ.functional a‖ ≤ ‖positiveFunctionalCLM τ.functional‖ * ‖a‖ at ht
  rwa [τ.norm_one,one_mul] at ht

lemma hereditary_trace_transfer (hsimple : TopologicallySimple A) {h g : A}
    (hh : 0 ≤ h) (hh0 : h ≠ 0) (hg : 0 ≤ g) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ c : A, 0 ≤ c ∧ c ∈ hereditaryCarrier h ∧
      ∀ τ : NormalizedTrace A, ‖τ.functional c-τ.functional g‖ < ξ := by
  classical
  obtain ⟨l,hl⟩ := exists_square_finiteIdealSum hsimple hh hh0 hg hξ
  let L : List (A × A) := (0,0)::l
  let r : Fin L.length → A := fun i => (L.get i).1
  let t : Fin L.length → A := fun i => (L.get i).2
  have hlen : 0 < L.length := by simp [L]
  let : NeZero L.length := ⟨hlen.ne'⟩
  have hs : (∑ i,r i*h*t i)=finiteIdealSum h l := by
    change (∑ i : Fin L.length, (fun p : A × A => p.1*h*p.2) (L.get i))=_
    rw [←List.sum_ofFn, List.ofFn_comp' (List.get L) (fun p : A × A => p.1*h*p.2),
      List.ofFn_get]
    simp [L,finiteIdealSum]
  obtain ⟨c,hc,hcm,hct⟩ := finite_trace_transfer h hh r t
  refine ⟨c,hc,hcm,fun τ => ?_⟩
  rw [hct τ,hs,←map_sub]
  exact (trace_norm_le τ _).trans_lt hl

theorem arbitrarily_small_rank_trace_transfer [Nontrivial A]
    (hsimple : TopologicallySimple A) (hproj : Projectionless A)
    (hT : Nonempty (NormalizedTrace A)) (g : A) (hg : 0 ≤ g) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ c : A, 0 ≤ c ∧ (∀ τ : NormalizedTrace A, ‖τ.functional c-τ.functional g‖ < ξ) ∧
      ∀ τ : NormalizedTrace A, τ.rank c < ENNReal.ofReal ξ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/ξ))
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left 1 (1/ξ)).trans hN.le
  have hNpos : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hN1)
  have hsmall : (1:ℝ)/(N:ℝ)<ξ := by
    have := (le_max_right 1 (1/ξ)).trans_lt hN
    exact (div_lt_iff₀ hNpos).mpr (by nlinarith [(div_mul_cancel₀ 1 hξ.ne')])
  obtain ⟨h,hh,hh0,hr⟩ := small_hereditary_rank hsimple hproj hT N hN1
  obtain ⟨c,hc,hcm,hct⟩ := hereditary_trace_transfer hsimple hh hh0 hg hξ
  refine ⟨c,hc,hct,fun τ => ?_⟩
  apply (τ.hereditary_rank_le hh hc hcm).trans (hr τ) |>.trans_lt
  have he : (1:ℝ≥0∞)/(N:ℝ≥0∞)=ENNReal.ofReal ((1:ℝ)/(N:ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hNpos]
    simp
  rw [he]
  exact (ENNReal.ofReal_lt_ofReal_iff hξ).mpr hsmall

end NonunitalGamma

end

noncomputable section
open Filter Topology
open scoped ComplexOrder ENNReal

namespace NonunitalGamma

def ramp (j : ℕ) (s : ℝ) : ℝ := min (max (s-(j:ℝ)) 0) 1

lemma ramp_zero (j : ℕ) : ramp j 0=0 := by
  simp [ramp]
lemma ramp_continuous (j : ℕ) : Continuous (ramp j) := by unfold ramp;fun_prop
lemma ramp_nonneg (j : ℕ) (s : ℝ) : 0 ≤ ramp j s := le_min (le_max_right _ _) zero_le_one
lemma ramp_le_one (j : ℕ) (s : ℝ) : ramp j s ≤ 1 := min_le_right _ _

lemma ramp_sum (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hN : s ≤ N) :
    (∑ j ∈ Finset.range N, ramp j s)=s := by
  induction N with
  | zero => have h : s=0 := le_antisymm (by simpa using hN) hs; simp [h]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases ht : s ≤ N
    · rw [ih ht]
      have hz : ramp N s=0 := by simp [ramp,max_eq_right (sub_nonpos.mpr ht)]
      rw [hz,add_zero]
    · have ht' : (N:ℝ)<s := lt_of_not_ge ht
      have hall : ∀ j ∈ Finset.range N,ramp j s=1 := by
        intro j hj
        have hj' : (j:ℝ)+1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        unfold ramp
        exact min_eq_right ((by linarith : (1:ℝ) ≤ s-j).trans (le_max_left _ _))
      rw [Finset.sum_congr rfl hall]
      have hr : ramp N s=s-N := by
        unfold ramp
        rw [max_eq_left (by linarith)]
        apply min_eq_left
        push_cast at hN
        linarith
      rw [hr]
      simp

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
open Pureness

lemma min_mul_min (p t : ℝ) (hp : 1 ≤ p) : min (p*min t 1) 1=min (p*t) 1 := by
  by_cases ht : t ≤ 1
  · rw [min_eq_left ht]
  · have ht' : 1 ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [min_eq_right ht',mul_one,min_eq_right hp,min_eq_right (by nlinarith)]

lemma cutoff_cutoff_zero (h : B) (hh : 0 ≤ h) (n : ℕ) :
    spectralApproxUnit (spectralApproxUnit h 0) n=spectralApproxUnit h n := by
  unfold spectralApproxUnit
  rw [←cfc_comp _ _ h hh.isSelfAdjoint]
  apply cfc_congr
  intro t _
  simp only [Nat.cast_zero,zero_add,one_mul,Function.comp_apply]
  exact min_mul_min _ _ (by linarith [Nat.cast_nonneg (α := ℝ) n])

lemma rank_cutoff_zero (τ : TracialState B) (h : B) (hh : 0 ≤ h) :
    normalizedRootRank τ (spectralApproxUnit h 0)=normalizedRootRank τ h := by
  have ht := spectralApproxUnit_trace_tendsto_rank τ (spectralApproxUnit h 0)
    (spectralApproxUnit_nonneg h hh 0)
  simp only [cutoff_cutoff_zero h hh] at ht
  exact tendsto_nhds_unique ht (spectralApproxUnit_trace_tendsto_rank τ h hh)

lemma ramp_cfc_zero (c : B) (hc : 0 ≤ c) : cfc (ramp 0) c=spectralApproxUnit c 0 := by
  apply cfc_congr
  intro t ht
  simp only [ramp,Nat.cast_zero,sub_zero,zero_add,one_mul]
  rw [max_eq_left (spectrum_nonneg_of_nonneg hc ht)]

lemma ramp_cfc_succ (c : B) (hc : 0 ≤ c) (j : ℕ) :
    cfc (ramp (j+1)) c=spectralApproxUnit (positiveIntegerCut c j) 0 := by
  rw [spectralApproxUnit_positiveIntegerCut c hc j 0]
  congr 1
  funext t
  simp [ramp]

lemma ramp_cfc_sum (c : B) (hc : 0 ≤ c) (N : ℕ) (hN : ‖c‖ ≤ N) :
    (∑ j ∈ Finset.range N,cfc (ramp j) c)=c := by
  calc
    _ = cfc (∑ j ∈ Finset.range N,ramp j) c :=
      (cfc_sum (fun j => ramp j) c (Finset.range N)
        (hf := fun j _ => (ramp_continuous j).continuousOn)).symm
    _ = cfc (fun t : ℝ => t) c := by
      apply cfc_congr
      intro t ht
      simp only [Finset.sum_apply]
      apply ramp_sum N t (spectrum_nonneg_of_nonneg hc ht)
      have hn : ‖t‖ ≤ ‖c‖ := by
        simpa only [cfc_id' ℝ c hc.isSelfAdjoint] using norm_apply_le_norm_cfc (fun t : ℝ => t) c ht
      exact (le_abs_self t).trans (hn.trans hN)
    _ = c := cfc_id' ℝ c hc.isSelfAdjoint

lemma ramp_rank_sum (τ : TracialState B) (c : B) (hc : 0 ≤ c) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1),(normalizedRootRank τ (cfc (ramp j) c)).toReal)=
      (normalizedRootRank τ c).toReal+
        ∑ j ∈ Finset.range N,(normalizedRootRank τ (positiveIntegerCut c j)).toReal := by
  rw [Finset.sum_range_succ']
  rw [ramp_cfc_zero c hc,rank_cutoff_zero τ c hc]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ramp_cfc_succ c hc j,rank_cutoff_zero τ _ (positiveIntegerCut_nonneg c j)]

lemma ramp_rank_defect (τ : TracialState B) (c : B) (hc : 0 ≤ c) (N : ℕ) (hN : ‖c‖ ≤ N) :
    0 ≤ (∑ j ∈ Finset.range (N+1),(normalizedRootRank τ (cfc (ramp j) c)).toReal)-(τ.functional c).re ∧
    (∑ j ∈ Finset.range (N+1),(normalizedRootRank τ (cfc (ramp j) c)).toReal)-(τ.functional c).re ≤
      (normalizedRootRank τ c).toReal := by
  rw [ramp_rank_sum τ c hc]
  have hi := actual_spectral_integer_approximation τ c hc N hN
  constructor <;> linarith

end NonunitalGamma

end

end OAI
