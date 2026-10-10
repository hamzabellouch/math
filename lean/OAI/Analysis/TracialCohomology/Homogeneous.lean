import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Partitions

namespace OAI

/-! Homogeneous for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def Homogeneous (p : M) : Prop := average e τ hτ htr hfaith p=(τ p).re • (1:M)

include h1 in
lemma average_gns_tendsto {I : Type*} {l : Filter I} {a : I → M} {b : M}
    (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun n => average e τ hτ htr hfaith (a n)) l (average e τ hτ htr hfaith b) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) ha
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 (a n)-expectation e τ hτ htr hfaith h1 b)‖≤_
  rw [←map_sub]
  exact average_gns_norm e τ hτ htr hfaith _

include h1 in
lemma homogeneous_limit {a : ℕ → M} {b : M} (ha : ∀ n, Homogeneous e τ hτ htr hfaith (a n))
    (ht : GNSTendsto τ a atTop b) (C : ℝ) (hC : ∀ n, ‖a n‖≤C) :
    Homogeneous e τ hτ htr hfaith b := by
  have htt := Complex.continuous_re.tendsto _ |>.comp
    (trace_predual_tendsto e τ hτ (ht.predual e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ hfaith C hC))
  have htn : Tendsto (fun n => (τ (a n)).re • (1:M)) atTop (𝓝 ((τ b).re • (1:M))) :=
    htt.smul_const 1
  have hgns : GNSTendsto τ (fun n => (τ (a n)).re • (1:M)) atTop ((τ b).re • (1:M)) := by
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp htn
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => preGNS_norm_le τ h1 _) hn
  exact GNSTendsto.unique τ hfaith (average_gns_tendsto e τ hτ htr hfaith h1 ht)
    (by simpa only [show ∀ n, average e τ hτ htr hfaith (a n)=(τ (a n)).re • (1:M) from ha] using hgns)

include h1 in
lemma homogeneous_zero : Homogeneous e τ hτ htr hfaith (0:M) := by
  change expectation e τ hτ htr hfaith h1 0=(τ 0).re • (1:M)
  rw [map_zero, map_zero, Complex.zero_re, zero_smul]

include h1 in
lemma homogeneous_sub {p q : M} (hp : Homogeneous e τ hτ htr hfaith p)
    (hq : Homogeneous e τ hτ htr hfaith q) : Homogeneous e τ hτ htr hfaith (p-q) := by
  change expectation e τ hτ htr hfaith h1 (p-q)=(τ (p-q)).re • (1:M)
  rw [map_sub,show expectation e τ hτ htr hfaith h1 p=(τ p).re • (1:M) from hp,
    show expectation e τ hτ htr hfaith h1 q=(τ q).re • (1:M) from hq,map_sub,Complex.sub_re,sub_smul]

include h1 in
lemma homogeneous_add {p q : M} (hp : Homogeneous e τ hτ htr hfaith p)
    (hq : Homogeneous e τ hτ htr hfaith q) : Homogeneous e τ hτ htr hfaith (p+q) := by
  change expectation e τ hτ htr hfaith h1 (p+q)=(τ (p+q)).re • (1:M)
  rw [map_add,show expectation e τ hτ htr hfaith h1 p=(τ p).re • (1:M) from hp,
    show expectation e τ hτ htr hfaith h1 q=(τ q).re • (1:M) from hq,map_add,Complex.add_re,add_smul]

include h1 in
lemma small_homogeneous (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hEp : Homogeneous e τ hτ htr hfaith p) (δ : ℝ) (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re < δ ∧ Homogeneous e τ hτ htr hfaith q := by
  have ht := projection_trace_pos τ hfaith hp hp0
  obtain ⟨k,hk⟩ := exists_nat_gt ((τ p).re/δ)
  let n := 2^(k+1)
  have hn : 0<n := pow_pos (by omega) _
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hkn : k<n := lt_trans (Nat.lt_succ_self k) Nat.lt_two_pow_self
  obtain ⟨q,hq,hqe,hqo,hqs⟩ := dyadic_partition e τ hτ htr hfaith h1 hII (k+1) hp
  let i : Fin n := ⟨0,hn⟩
  have hsum : (n:ℝ) • average e τ hτ htr hfaith (q i)=average e τ hτ htr hfaith p := by
    calc
      _=∑ j : Fin n, average e τ hτ htr hfaith (q j) := by
        simp only [←hqe i _,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
      _=_ := by change (∑ j : Fin n, expectation e τ hτ htr hfaith h1 (q j))=expectation e τ hτ htr hfaith h1 p; rw [←map_sum,hqs]
  have hqi : average e τ hτ htr hfaith (q i)=((τ p).re/(n:ℝ)) • (1:M) := by
    have hh := congrArg (fun z : M => (n:ℝ)⁻¹ • z) hsum
    rw [smul_smul,inv_mul_cancel₀ hnR.ne',one_smul,hEp,smul_smul] at hh
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hqt : (τ (q i)).re=(τ p).re/(n:ℝ) := by
    rw [←trace_average e τ hτ htr hfaith h1 (q i),hqi,τ.map_smul_of_tower,h1]
    simp
  have hqp : q i ≤ p := by
    rw [←hqs]
    exact Finset.single_le_sum (fun j _ => (hq j).nonneg) (Finset.mem_univ i)
  refine ⟨q i,hq i,hqp,?_,?_,?_⟩
  · intro he
    have hh := div_pos ht hnR
    rw [←hqt,he,map_zero,Complex.zero_re] at hh
    exact lt_irrefl 0 hh
  · rw [hqt]
    apply (div_lt_iff₀ hnR).mpr
    have hh := (div_lt_iff₀ hδ).mp (hk.trans (Nat.cast_lt.mpr hkn))
    nlinarith
  · change average e τ hτ htr hfaith (q i)=(τ (q i)).re • (1:M)
    rw [hqt,hqi]
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem homogeneous_chain_upper {p : M} (hp : IsStarProjection p) (t : ℝ)
    (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t ∧ Homogeneous e τ hτ htr hfaith q) :
    ∃ s : M, IsStarProjection s ∧ s ≤ p ∧ (τ s).re ≤ t ∧ Homogeneous e τ hτ htr hfaith s ∧ ∀ q ∈ c, q ≤ s := by
  classical
  let T : Set ℝ := (fun q : M => (τ q).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨t,by rintro _ ⟨q,hq,rfl⟩; exact (hs q hq).2.2.1⟩
  obtain ⟨v,hvm,_hvL,hvt,hv⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hav using hv
  change ∀ n, (τ (a n)).re=v n at hav
  have ham : Monotone a := by
    intro m n hmn
    apply projection_le_of_comparable_trace_le τ hfaith (hs _ (ha m)).1 (hs _ (ha n)).1
      (hc.total (ha m) (ha n))
    rw [hav,hav]
    exact hvm hmn
  obtain ⟨s,hsp,ht,hns,hsl⟩ := exists_monotone_projection_limit e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith
    a (fun n => (hs _ (ha n)).1) ham
  have htrace : (τ s).re=sSup T := by
    have htd := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ hfaith 1
        (fun n => (hs _ (ha n)).1.norm_le _) ht)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp htd)
    simpa only [Function.comp_def,hav] using hvt
  refine ⟨s,hsp,hsl p hp (fun n => (hs _ (ha n)).2.1),?_,?_,?_⟩
  · rw [htrace]
    apply csSup_le hTne
    rintro _ ⟨q,hq,rfl⟩
    exact (hs q hq).2.2.1
  · exact homogeneous_limit e τ hτ htr hfaith h1 (fun n => (hs _ (ha n)).2.2.2) ht 1
      (fun n => (hs _ (ha n)).1.norm_le)
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
include h1 in

theorem exists_homogeneous_trace (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) (t : ℝ) (ht0 : 0 ≤ t) (htp : t ≤ (τ p).re) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ (τ q).re=t ∧ Homogeneous e τ hτ htr hfaith q := by
  classical
  let S : Set M := {q | IsStarProjection q ∧ q ≤ p ∧ (τ q).re ≤ t ∧ Homogeneous e τ hτ htr hfaith q}
  have h0 : (0 : M) ∈ S := ⟨IsStarProjection.zero M,hp.nonneg,by simpa only [map_zero,Complex.zero_re],homogeneous_zero e τ hτ htr hfaith h1⟩
  obtain ⟨q,_hq0,hqm⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsp_le,hst,hsE,hsup⟩ := homogeneous_chain_upper e τ hτ htr hfaith h1
      hp t c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsp_le,hst,hsE⟩,hsup⟩) 0 h0
  have hq : IsStarProjection q := hqm.1.1
  have hqp : q ≤ p := hqm.1.2.1
  have hqt : (τ q).re ≤ t := hqm.1.2.2.1
  have hEq := hqm.1.2.2.2
  refine ⟨q,hq,hqp,le_antisymm hqt ?_,hEq⟩
  by_contra hle
  have hlt : (τ q).re<t := lt_of_not_ge hle
  have hpq : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hqp
  have hpq0 : p-q ≠ 0 := by
    intro he
    have hh := congrArg (fun a : M => (τ a).re) (sub_eq_zero.mp he)
    linarith
  obtain ⟨r,hr,hrpq,hr0,hrt,hrE⟩ := small_homogeneous e τ hτ htr hfaith h1 hII hpq hpq0
    (homogeneous_sub e τ hτ htr hfaith h1 hEp hEq)
    (t-(τ q).re) (sub_pos.mpr hlt)
  have hqr : q*r=0 := by
    have hh := (hr.le_iff_mul_eq_right hpq).mp hrpq
    calc
      q*r=q*((p-q)*r) := by rw [hh]
      _=(q*p-q*q)*r := by noncomm_ring
      _=0 := by rw [(hq.le_iff_mul_eq_left hp).mp hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
  have hsum : q+r ∈ S := by
    refine ⟨hq.add hr hqr,?_,?_,homogeneous_add e τ hτ htr hfaith h1 hEq hrE⟩
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

end PopaCenter

end

end OAI
