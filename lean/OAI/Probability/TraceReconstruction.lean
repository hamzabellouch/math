import OAI.Probability.TraceReconstruction.Induction
import OAI.Probability.TraceReconstruction.Testing

namespace OAI

/-!
# Bounds

Restored construction and final scales; quantitative sample lower bound and both fixed-channel superpolynomial endpoints.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The exact source error is negligible compared to the squared score energy. -/
theorem source_final_error_eventually (B : ℕ) (ζ : ℝ) (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀ (U : ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩ (n t)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t))))
      (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^(2*B*sourceDepth B ζ ((q t)^3*Real.log (n t))+2))
      (sourceDepth B ζ ((q t)^3*Real.log (n t)))
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t)
        (sourceDepth B ζ ((q t)^3*Real.log (n t))))),
      U.error≤(n t)^(-2*totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  have ht := SourceExpUpper.uniform (fun D _=>(D:ℝ)+1) SourcePolyUpper.depth.expUpper
    B ζ 1 hB hζ zero_lt_one hn hq hH
  filter_upwards [ht,hn.eventually_ge_atTop 2] with t ht hn2 U
  let D := sourceDepth B ζ ((q t)^3*Real.log (n t))
  let d := totalScoreExponent B D
  have hn0 : 0<n t := by linarith only [hn2]
  have hn1 : 1≤n t := by linarith only [hn2]
  have hD : (D:ℝ)+1≤n t := by
    have hh := ht D
    rw [sourceTargetScale_top,one_mul] at hh
    exact hh.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (sourceEpsilon_le_one B D))
  have hd : 11/5≤d := (totalScoreExponent_bounds B D hB).1
  calc
    U.error ≤ ((D:ℝ)+1)*(n t)^(-100*(d+B+1))*n t := U.error_le hn0 (Real.rpow_nonneg hn0.le _)
    _ ≤ (n t)*(n t)^(-100*(d+B+1))*n t := by gcongr
    _ = (n t)^(-100*(d+B+1)+2) := by
      rw [Real.rpow_add hn0,Real.rpow_two]
      ring
    _ ≤ (n t)^(-2*d) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [Nat.cast_nonneg B (α:=ℝ)])

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem exists_source_slope {c : ℝ} (hc : c<1/(4*Real.log 2)) :
    ∃B : ℕ,2≤B ∧ ∃ζ : ℝ,ζ∈Set.Ioo 0 1 ∧ c<finalSlope B ζ := by
  have hn : Tendsto (fun B : ℕ=>(B:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hn1 : Tendsto (fun B : ℕ=>(B:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun B=>by linarith) hn
  have h1 := hn1.const_div_atTop (1:ℝ)
  have h2 := hn.const_div_atTop (3/10:ℝ)
  have hlim := ((tendsto_const_nhds (x:=(1:ℝ))).sub h1).mul
    ((tendsto_const_nhds (x:=(1/4:ℝ))).sub h2) |>.div_const (Real.log 2)
  have hlim' : Tendsto (fun B : ℕ=>(1-1/((B:ℝ)+1))*((1/4:ℝ)-(3/10:ℝ)/(B:ℝ))/Real.log 2)
      atTop (𝓝 (1/(4*Real.log 2))) := by
    convert hlim using 1
    ring_nf
  obtain ⟨B,hB,hβ⟩ := ((eventually_ge_atTop 2).and (hlim'.eventually_const_lt hc)).exists
  refine ⟨B,hB,1/((B:ℝ)+1),⟨by positivity,?_⟩,?_⟩
  · have hBr : (2:ℝ)≤B := by exact_mod_cast hB
    exact (div_lt_one (by positivity)).mpr (by linarith)
  · have hBr : (B:ℝ)≠0 := by exact_mod_cast (show B≠0 by omega)
    have he : finalSlope B (1/((B:ℝ)+1))=
        (1-1/((B:ℝ)+1))*((1/4:ℝ)-(3/10:ℝ)/(B:ℝ))/Real.log 2 := by
      unfold finalSlope blockGain
      field_simp
      ring
    rw [he]
    exact hβ

/-- Constant-size subdivision and larger deletion preserve the joint regime.
 The factor 16 includes the factor eight of the working deletion cube. -/
theorem subdivided_working_scale {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioo 0 1)
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop)
    {G : ℝ} (hG : 0<G) :
    Tendsto (fun t=>n t/G) atTop atTop ∧
    Tendsto (fun t=>(workingDeletion (q t))^3*Real.log (n t/G)) atTop atTop ∧
    ∀ᶠt in atTop,(q t)^3*Real.log (n t)/16 ≤
      (workingDeletion (q t))^3*Real.log (n t/G) := by
  have hN := hn.atTop_div_const hG
  have hl := Real.tendsto_log_atTop.comp hn
  have hh : ∀ᶠt in atTop,(q t)^3*Real.log (n t)/16 ≤
      (workingDeletion (q t))^3*Real.log (n t/G) := by
    filter_upwards [hn.eventually_ge_atTop 1,hl.eventually_ge_atTop (max 0 (2*Real.log G))] with t hn1 hl
    have hn0 : 0<n t := by linarith only [hn1]
    have hl0 : 0≤Real.log (n t) := (le_max_left _ _).trans hl
    have hlg : 2*Real.log G≤Real.log (n t) := (le_max_right _ _).trans hl
    have hhalf : Real.log (n t)/2≤Real.log (n t/G) := by
      rw [Real.log_div hn0.ne' hG.ne']
      linarith only [hlg]
    have hb := (workingScale_bounds (hq t) hl0).1
    have hm := mul_le_mul_of_nonneg_left hhalf (pow_nonneg (workingDeletion_bounds (hq t)).1.1.le 3)
    nlinarith only [hb,hm]
  exact ⟨hN,tendsto_atTop_mono' atTop hh (hH.atTop_div_const (by norm_num : (0:ℝ)<16)),hh⟩

theorem workingDeletion_Ioc {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    workingDeletion q ∈Set.Ioc 0 (1/2:ℝ) :=
  ⟨(workingDeletion_bounds hq).1.1,min_le_right _ _⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Full sharp slope restoration after fixed gadget packing. Both deletion
 probability and length may vary; the working channel is only internal. -/
theorem source_restored_exponent_margin (B : ℕ) (ζ c G a : ℝ)
    (hB : 2≤B) (hζ : ζ∈Set.Ioo 0 1) (hc : 0<c) (hα : c<finalSlope B ζ)
    (hG : 0<G) (ha : 0<a) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioo 0 1)
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,(n t)^(c*Real.log ((q t)^3*Real.log (n t))) ≤
      a*(n t/G)^(totalScoreExponent B
        (sourceDepth B ζ ((workingDeletion (q t))^3*Real.log (n t/G)))) := by
  let α := finalSlope B ζ
  have hα0 : 0<α := hc.trans hα
  obtain ⟨ρ,hρc,hρ1⟩ := exists_between ((div_lt_one hα0).mpr hα)
  have hρ0 : 0<ρ := (div_pos hc hα0).trans hρc
  have hρc' : c<ρ*α := (div_lt_iff₀ hα0).mp hρc
  let H := fun t=>(q t)^3*Real.log (n t)
  let J := fun t=>(workingDeletion (q t))^3*Real.log (n t/G)
  let d := fun t=>totalScoreExponent B (sourceDepth B ζ (J t))
  let K := blockGain B+(warmupBlocks B:ℝ)*blockGain B+α*Real.log 16
  have hsc := subdivided_working_scale hn hq hH hG
  have hdepth := sourceDepth_tendsto B ζ hB hζ.2 hsc.2.1
  have hd : ∀ᶠt in atTop,(ρ*α)*Real.log (H t)-ρ*K≤ρ*d t := by
    filter_upwards [hsc.2.2,hH.eventually_gt_atTop 0,
      hdepth.eventually_ge_atTop (warmupBlocks B)] with t hj hp hD
    have hJ : 0<J t := lt_of_lt_of_le (div_pos hp (by norm_num)) hj
    have hlog : Real.log (H t)-Real.log 16≤Real.log (J t) := by
      have hh := Real.log_le_log (div_pos hp (by norm_num)) hj
      simpa only [Real.log_div (ne_of_gt hp) (by norm_num : (16:ℝ)≠0)] using hh
    have hs := (totalScoreExponent_slope_lower B ζ (J t) hB hD).le
    have hm := mul_le_mul_of_nonneg_left hlog hα0.le
    have hbase : α*Real.log (H t)-K≤d t := by
      dsimp only [K,d,α] at *
      linarith only [hs,hm]
    have hh := mul_le_mul_of_nonneg_left hbase hρ0.le
    nlinarith only [hh]
  have hex := eventually_exponent_margin hn hH hρc' ha hd
  have hsub := ((PowerRate.base hn).div_const hn hG).lower hn hρ1
  filter_upwards [hex,hsub,hn.eventually_gt_atTop 0] with t he hs hp
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ ha.le
  rw [Real.rpow_mul hp.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hp.le _) hs
    (by have hh := (totalScoreExponent_bounds B (sourceDepth B ζ (J t)) hB).1; dsimp [d]; linarith only [hh])

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical ENNReal

theorem sample_tv_small {s G N d E M : ℝ} (hs : s∈Set.Ioc 0 1)
    (hG : 0<G) (hN : 1 ≤ N) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hE : E ≤ N^(-2*d)) (hbudget : M ≤ (s^2/(64*G))*N^d) :
    Real.sqrt (M*G*N^(-d))+2*M*G*E ≤ s/4 := by
  have hN0 : 0<N := by linarith only [hN]
  have hV0 : 0 ≤ N^(-d) := Real.rpow_nonneg hN0.le _
  have hV1 : N^(-d) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hN (neg_nonpos.mpr hd)
  have hVV : N^(-2*d)=(N^(-d))^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hprod : N^d*N^(-d)=1 := by rw [←Real.rpow_add hN0,add_neg_cancel,Real.rpow_zero]
  have hMV : M*G*N^(-d) ≤ s^2/64 := by
    calc
      _  ≤  ((s^2/(64*G))*N^d)*G*N^(-d) := by gcongr
      _ = (s^2/(64*G)*G)*(N^d*N^(-d)) := by ring
      _ = s^2/64 := by rw [hprod]; field_simp
  have hsq : Real.sqrt (M*G*N^(-d)) ≤ s/8 := by
    apply (Real.sqrt_le_left (div_nonneg hs.1.le (by norm_num) : 0 ≤ s/8)).mpr
    nlinarith only [hMV]
  have hE' : E ≤ N^(-d) := by
    rw [hVV] at hE
    nlinarith only [hE,mul_le_mul_of_nonneg_left hV1 hV0]
  have he := mul_le_mul_of_nonneg_left hE' (show 0 ≤ 2*M*G by positivity)
  have hss := mul_nonneg hs.1.le (sub_nonneg.mpr hs.2)
  nlinarith only [hsq,he,hMV,hss]

/-- Source Theorem 1: all fixed positive success levels, not only binary
 testing above one half, with complete independent traces and known channel. -/
theorem quantitative_sample_lower_bound
    (s c : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (hc : c ∈ Set.Ioo 0 (1 / (4 * Real.log 2)))
    (n : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hq : ∀ k, q k ∈ Set.Ioo 0 1)
    (hscale : Tendsto (fun k => (q k) ^ 3 * Real.log (n k)) atTop atTop) :
    ∀ᶠ k in atTop,
      ENNReal.ofReal ((n k : ℝ) ^ (c * Real.log ((q k) ^ 3 * Real.log (n k))))  ≤ 
        sampleComplexity (n k) (q k) s := by
  obtain ⟨B,hB,ζ,hζ,hα⟩ := exists_source_slope hc.2
  obtain ⟨g,hg⟩ := exists_nat_gt (max 1 (2/s))
  have hg1 : 1<(g:ℝ) := (le_max_left _ _).trans_lt hg
  have hg0 : 0<(g:ℝ) := by linarith only [hg1]
  have hgs : 1/(2:ℝ)^g<s/2 := by
    have hp : (g:ℝ)<(2:ℝ)^g := by
      clear hg hg1 hg0
      induction g with
      | zero => norm_num
      | succ g ih =>
        push_cast
        rw [pow_succ]
        have hg : (0:ℝ) ≤ g := Nat.cast_nonneg g
        have hp : (1:ℝ) ≤ 2^g := one_le_pow₀ (by norm_num)
        nlinarith only [ih,hg,hp]
    have hbig : 2/s<(2:ℝ)^g := ((le_max_right _ _).trans_lt hg).trans hp
    have hh := (div_lt_iff₀ hs.1).mp hbig
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2^g)).mpr
    nlinarith only [hh]
  have hnr : Tendsto (fun t=>(n t:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  let N := fun t=>(n t:ℝ)/(g:ℝ)
  let r := fun t=>workingDeletion (q t)
  have hr (t) : r t∈Set.Ioc 0 (1/2:ℝ) := workingDeletion_Ioc (hq t)
  have hsc := subdivided_working_scale hnr hq hscale hg0
  have hpair := source_final_pair_eventually B ζ hB hζ hsc.1 hr hsc.2.1
  have herr := source_final_error_eventually B ζ hB hζ hsc.1 hr hsc.2.1
  have hmargin := source_restored_exponent_margin B ζ c (g:ℝ) (s^2/(64*g))
    hB hζ hc.1 hα hg0 (div_pos (sq_pos_of_pos hs.1) (mul_pos (by norm_num) hg0)) hnr hq hscale
  filter_upwards [hpair,herr,hmargin,hsc.1.eventually_ge_atTop 2] with t hp he hm hn2
  obtain ⟨U⟩ := hp
  have hN1 : 1 ≤ N t := by dsimp [N]; linarith only [hn2]
  have hN2 : 1<N t := by dsimp [N]; linarith only [hn2]
  have hk := (sourceHalfMoment_bounds B
    (sourceDepth B ζ ((r t)^3*Real.log (N t)))
    (sourceDepth B ζ ((r t)^3*Real.log (N t))) hB hN2).1
  obtain ⟨W,hW,hTV⟩ := U.restored_family (by have hh := (hr t).2; dsimp [r] at *; linarith only [hh])
    ⟨(hq t).1.le,(hq t).2.le⟩ (workingDeletion_bounds (hq t)).2.2 hk g (n t)
    (by field_simp; exact le_rfl)
  apply le_sInf
  rintro z ⟨m,hbudget,rfl⟩
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  by_contra hnot
  have hm' : (m:ℝ) ≤ (s^2/(64*g))*(N t)^(
      totalScoreExponent B (sourceDepth B ζ ((r t)^3*Real.log (N t)))) :=
    (le_of_lt (lt_of_not_ge hnot)).trans hm
  have hclose (θ : Fin g→Bool) := (hTV θ m).trans
    (sample_tv_small hs hg0 hN1
      (by have hd := (totalScoreExponent_bounds B (sourceDepth B ζ ((r t)^3*Real.log (N t))) hB).1; linarith only [hd])
      (Nat.cast_nonneg m) (he U) hm')
  have hbad := family_testing_bound ⟨(hq t).1.le,(hq t).2.le⟩ W hW hclose hbudget
  linarith only [hbad,hgs,hs.1]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical ENNReal

namespace FiniteLaw
variable {α : Type*} [Fintype α]
theorem tv_product_one (P Q : FiniteLaw α) : (P.product 1).tv (Q.product 1)=P.tv Q := by
  rw [show 1=0+1 from rfl,tv_product_succ]
  simp only [tv,tensor,product,Fintype.sum_prod_type,Fintype.prod_empty,mul_one,Fintype.sum_unique]
end FiniteLaw

theorem totalScoreExponent_two (D : ℕ) : totalScoreExponent 2 D=11/5+(D:ℝ)/5 := by
  simp only [totalScoreExponent,ite_self,blockGain_two,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

theorem minTraceTV_nonneg_of_pair {n : ℕ} (q : ℝ) (x y : Word n) (hxy : x≠y) :
    0 ≤ minTraceTV n q := by
  apply le_csInf (show {t | ∃x y : Word n,x≠y ∧ t=traceTV q x y}.Nonempty from
    ⟨_,x,y,hxy,rfl⟩)
  rintro b ⟨u,v,_,rfl⟩
  exact traceTV_nonneg q u v

theorem minTraceTV_le_pair {n : ℕ} (q : ℝ) (x y : Word n) (hxy : x≠y) :
    minTraceTV n q ≤ traceTV q x y := by
  apply csInf_le (show BddBelow {t | ∃x y : Word n,x≠y ∧ t=traceTV q x y} from ?_) ⟨x,y,hxy,rfl⟩
  exact ⟨0,by rintro b ⟨u,v,_,rfl⟩; exact traceTV_nonneg q u v⟩

theorem one_trace_power_bound {N d C R : ℝ} (hN : 1 ≤ N) (hC : 0<C)
    (hd : 2*(C+1) ≤ d) (hR : R ≤ Real.sqrt (N^(-d))+2*N^(-2*d)) :
    N^C*R ≤ 3/N := by
  have hN0 : 0<N := by linarith only [hN]
  have he : (N^(-(C+1)))^2=N^(-2*(C+1)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hs : Real.sqrt (N^(-d)) ≤ N^(-(C+1)) := by
    apply (Real.sqrt_le_left (Real.rpow_nonneg hN0.le _)).mpr
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hd])
  have herr : N^(-2*d) ≤ N^(-(C+1)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hd,hC])
  calc
    N^C*R ≤ N^C*(3*N^(-(C+1))) :=
      mul_le_mul_of_nonneg_left (by linarith only [hR,hs,herr]) (Real.rpow_nonneg hN0.le _)
    _ = 3/N := by
      rw [mul_left_comm,←Real.rpow_add hN0]
      rw [show C+ -(C+1)=(-1:ℝ) by ring,Real.rpow_neg_one]
      ring

/-- Source Theorem 2, first conclusion, over all integer lengths and at the
 same fixed channel for every power. -/
theorem superpolynomial_one_trace
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (C : ℝ) (hC : 0<C) :
    Tendsto (fun n : ℕ=>(n:ℝ)^C*minTraceTV n q) atTop (𝓝 0) := by
  let r := workingDeletion q
  have hr : r∈Set.Ioc 0 (1/2:ℝ) := workingDeletion_Ioc hq
  have hn : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hJ : Tendsto (fun n : ℕ=>r^3*Real.log (n:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hn).const_mul_atTop (pow_pos hr.1 3)
  have hpair := source_final_pair_eventually 2 (1/2) (by omega) (by norm_num) hn (fun _=>hr) hJ
  have herr := source_final_error_eventually 2 (1/2) (by omega) (by norm_num) hn (fun _=>hr) hJ
  obtain ⟨D0,hD0⟩ := exists_nat_ge (5*(2*(C+1)))
  have hdepth := (sourceDepth_tendsto 2 (1/2) (by omega) (by norm_num) hJ).eventually_ge_atTop D0
  have hb : ∀ᶠ n : ℕ in atTop,0 ≤ (n:ℝ)^C*minTraceTV n q ∧
      (n:ℝ)^C*minTraceTV n q ≤ 3/(n:ℝ) := by
    filter_upwards [hpair,herr,hdepth,hn.eventually_ge_atTop 2] with n hp he hD hn2
    obtain ⟨U⟩ := hp
    have hn1 : 1<(n:ℝ) := by linarith only [hn2]
    have hk := (sourceHalfMoment_bounds 2
      (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ)))
      (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ))) (by omega) hn1).1
    obtain ⟨x,y,hxy,hTV⟩ := U.restored_words (by linarith only [hr.2])
      ⟨hq.1.le,hq.2.le⟩ (workingDeletion_bounds hq).2.2 hk n le_rfl
    have ht := hTV 1
    rw [FiniteLaw.tv_product_one] at ht
    rw [completeTraceLaw_tv q ⟨hq.1.le,hq.2.le⟩ x y] at ht
    norm_num only [Nat.cast_one,one_mul,mul_one] at ht
    have hd : 2*(C+1) ≤ totalScoreExponent 2 (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ))) := by
      rw [totalScoreExponent_two]
      have hDD : (D0:ℝ) ≤ (sourceDepth 2 (1/2) (r^3*Real.log (n:ℝ)):ℝ) := by exact_mod_cast hD
      linarith only [hD0,hDD]
    refine ⟨mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (minTraceTV_nonneg_of_pair q x y hxy),?_⟩
    apply (mul_le_mul_of_nonneg_left (minTraceTV_le_pair q x y hxy)
      (Real.rpow_nonneg (Nat.cast_nonneg n) C)).trans
    apply one_trace_power_bound hn1.le hC hd
    linarith only [ht,he U]
  exact squeeze_zero' (hb.mono fun _ h=>h.1) (hb.mono fun _ h=>h.2) (hn.const_div_atTop 3)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical ENNReal

/-- Source Theorem 2's sample conclusion at the same fixed deletion channel. -/
theorem superpolynomial_sample_complexity
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (s : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => sampleComplexity n q s / ENNReal.ofReal ((n : ℝ) ^ C))
      atTop (𝓝 ⊤) := by
  let c : ℝ := 1/(8*Real.log 2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc : c ∈ Set.Ioo 0 (1/(4*Real.log 2)) := by
    refine ⟨hc0,?_⟩
    dsimp [c]
    apply one_div_lt_one_div_of_lt
    · positivity
    · nlinarith only [hl]
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hH : Tendsto (fun n : ℕ => q^3*Real.log (n:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hn).const_mul_atTop (pow_pos hq.1 3)
  have hb := quantitative_sample_lower_bound s c hs hc id (fun _ => q) tendsto_id (fun _ => hq) hH
  have he := ((Real.tendsto_log_atTop.comp hH).const_mul_atTop hc0).eventually_ge_atTop (2*C+1)
  have hbound : ∀ᶠ n : ℕ in atTop,(n:ℝ≥0∞) ≤
      sampleComplexity n q s / ENNReal.ofReal ((n:ℝ)^C) := by
    filter_upwards [hb,he,hn.eventually_gt_atTop 1] with n hb he hn1
    dsimp only [Function.comp_apply] at he
    have hn0 : 0 < (n:ℝ) := zero_lt_one.trans hn1
    have hpow : (n:ℝ)^(C+1) ≤ (n:ℝ)^(c*Real.log (q^3*Real.log (n:ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith only [he,hC])
    have hnC : 0 < (n:ℝ)^C := Real.rpow_pos_of_pos hn0 C
    have hdiv : ENNReal.ofReal ((n:ℝ)^(C+1)) /
        ENNReal.ofReal ((n:ℝ)^C) = (n:ℝ≥0∞) := by
      rw [← ENNReal.ofReal_div_of_pos hnC,Real.rpow_add hn0,Real.rpow_one]
      rw [mul_div_cancel_left₀ _ hnC.ne',ENNReal.ofReal_natCast]
    rw [← hdiv]
    exact ENNReal.div_le_div_right ((ENNReal.ofReal_le_ofReal hpow).trans hb) _
  apply ENNReal.tendsto_nhds_top
  intro k
  filter_upwards [hbound,eventually_gt_atTop k] with n hn hk
  exact (show (k:ℝ≥0∞) < (n:ℝ≥0∞) by exact_mod_cast hk).trans_le hn

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
