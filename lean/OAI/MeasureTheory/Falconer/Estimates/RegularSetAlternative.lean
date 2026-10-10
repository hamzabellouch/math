import OAI.MeasureTheory.Falconer.Estimates.RegularCoarsePreparation
import OAI.MeasureTheory.Falconer.Incidence.FrozenCoarseConfiguration
import OAI.MeasureTheory.Falconer.Incidence.FrozenCoarseObstruction
import OAI.MeasureTheory.Falconer.Recursion.RegularPacketScaleBudget
import OAI.MeasureTheory.Falconer.Estimates.CoarseFreezingBudget
import OAI.MeasureTheory.Falconer.Estimates.SmallUnionLogs
import OAI.MeasureTheory.Falconer.Incidence.UniformSmallCoverPencils

namespace OAI

/-! The regular-set alternative at adjacent square-root scales. All coarse
cells, pencils and frozen packets in the contradiction are constructed from
the original finite point and tube configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_cover_alternative {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          1/(K*(Δ^s)^2) ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K/(Δ^s)^2 ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ (((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 ∧
          (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ K/(ρ^s)^2) := by
  obtain ⟨θ,N1,hθ,hN1,hfalse⟩ := frozen_coarse_packet_impossible hκ hκ1
  obtain ⟨ε,N2,hε,hε1,hN2,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jf := Nat.log 2 (P.biUnion V).card+1
  obtain ⟨hn3,hD80,hHD,h13,h8,hdepth,hDE⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hdepth' : 10*((n:ℝ)+2) ≤ D := by
    change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hD1 : 1 ≤ D := by change 1 ≤ K^2; exact one_le_pow₀ hK1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have powE (a : ℕ) (ha : a ≤ 40) : D^a ≤ E :=
    (pow_le_pow_right₀ hD1 ha).trans hDE
  have hDE' : D ≤ E := by simpa only [pow_one] using powE 1 (by norm_num)
  have hKE : K ≤ E := hKD.trans hDE'
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  obtain ⟨hJp,hJf,hJv⟩ := small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall.1
  have hJpD : (Nat.log 2 P.card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJp).trans (by push_cast; linarith only [hdepth',hn0])
  have hJvD : (Jv:ℝ) ≤ D :=
    (Nat.cast_le.mpr hJv).trans (by push_cast; linarith only [hdepth',hn0])
  have hJfD : (Jf:ℝ) ≤ D :=
    (Nat.cast_le.mpr hJf).trans (by push_cast; linarith only [hdepth',hn0])
  have hJv0 : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJf0 : 0 < (Jf:ℝ) := by dsimp [Jf]; positivity
  obtain ⟨C,hCP,hC,hCchart,hCsep,hCball,hcells,T,hT,hTU,hTUorig,hG,hGsum,hGmem,hnear⟩ :=
    regular_coarse_preparation n hn3 hs0 hsone ht0 ht hK1 hKD hD80 h13 P V hP hPsmall hPball
      (fun p hp => ⟨(hV p hp).1,(hV p hp).2.2.1,(hV p hp).2.2.2.2.2⟩)
      hJpD hJvD hpoint hsmall.2 hsmall.1
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  let Jc := Nat.log 2 (C.biUnion T).card+1
  have hCpow : (C.biUnion T).card ≤ 2^(5*n+6) := by
    have hu := small_union_card_dyadic n hε1 hsone (P.biUnion V).card hsmall.1
    have hc : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by exact_mod_cast hTUorig
    calc
      _ ≤ 13*2^(5*n+2) := hc.trans (Nat.mul_le_mul_left _ hu)
      _ ≤ 16*2^(5*n+2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by rw [show 5*n+6 = (5*n+2)+4 by omega,pow_add]; norm_num; ring
  have hJcD : (Jc:ℝ) ≤ D := by
    have hh := packet_log_of_card_bound hCpow
    have hh' : Jc ≤ 5*n+7 := by dsimp [Jc]; omega
    exact (Nat.cast_le.mpr hh').trans (by push_cast; linarith only [hdepth',hn0])
  have hJc1 : (1:ℝ) ≤ Jc := by dsimp [Jc]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hD5 : 1 ≤ D^5 := one_le_pow₀ hD1
  obtain ⟨k,R,hRC,hR,_,hRball,hmlow,hmup,hband⟩ := uniform_small_cover_pencils (n+3) hs0 hst hD5
    (show 0 ≤ D/(ρ^s)^2 by positivity) C T hC hCchart hCball
    (fun c hc => ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.2.1,
      fun a ha => ((hT c hc).2.2.2.2 a ha).1⟩) hTU
  let m := (2:ℝ)^k
  let Kc := D^5*(Jc:ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hKc : 1 ≤ Kc := hD5.trans (le_mul_of_one_le_right (pow_nonneg hD0 _) hJc1)
  have hKc6 : Kc ≤ D^6 := by
    calc
      _ ≤ D^5*D := mul_le_mul_of_nonneg_left hJcD (pow_nonneg hD0 _)
      _ = _ := by ring
  have hMM : 2*m ≤ D^20/ρ^s := coarse_comparable_size_bound hρ hκ hs0 hsone hge hD80
    (zero_le_one.trans hKc) hKc6 (by positivity) le_rfl hHD hmup
  have hmlow6 : 1/(D^6*ρ^s) ≤ m := by
    apply le_trans _ hmlow
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh : 2*D^5 ≤ D^6 := by
      calc
        _ ≤ D*D^5 := mul_le_mul_of_nonneg_right (by linarith only [hD80]) (pow_nonneg hD0 _)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hh hρs.le
  have mono_ball {d u A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d u A F) : NormalizedFiniteBallBound d u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hTreg (c : Space 2) (hc : c ∈ R) : NormalizedFiniteBallBound ρ s Kc (T c) :=
    mono_ball hρ.le (le_mul_of_one_le_right (pow_nonneg hD0 _) hJc1) (hT c (hRC hc)).2.2.2.1
  have hRu : R.biUnion T ⊆ C.biUnion T := Finset.biUnion_subset_biUnion_of_subset_left T hRC
  obtain ⟨Q,hQR,hQ,_,hQball,U,hU,hUsub,hUsum,hUband⟩ := frozen_coarse_configuration hρ
    (zero_le_one.trans hKc) hm (show 0 < 2*m by positivity) R T G hR hRball (by
      intro c hc
      exact ⟨(hband c hc).1,(hband c hc).2,(hT c (hRC hc)).2.1,(hT c (hRC hc)).2.2.1,
        hTreg c hc,fun a ha => ((hT c (hRC hc)).2.2.2.2 a ha).1⟩)
    (P.biUnion V).card (fun a ha => hG a (hRu ha))
  have hQC : Q ⊆ C := hQR.trans hRC
  have hUC : Q.biUnion U ⊆ C.biUnion T := hUsub.trans hRu
  have hF : 2*(Jf:ℝ)*(2*m)/m = 4*(Jf:ℝ) := by field_simp; norm_num
  have hF2 : 2*(Jf:ℝ)*(2*m)/m ≤ D^2 := by
    rw [hF]
    have hh : 4*D ≤ D^2 := by nlinarith only [hD80,hD0]
    exact (mul_le_mul_of_nonneg_left hJfD (by norm_num)).trans hh
  have hKF : Kc*(2*(Jf:ℝ)*(2*m)/m) ≤ E := by
    calc
      _ ≤ D^6*D^2 := mul_le_mul hKc6 hF2 (by positivity) (pow_nonneg hD0 _)
      _ = D^8 := by ring
      _ ≤ _ := powE 8 (by norm_num)
  have hm8 : 1/(D^8*ρ^s) ≤ m/(2*(Jf:ℝ)) := by
    calc
      _ ≤ (1/(D^6*ρ^s))/(2*D) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hh : 2*D ≤ D^2 := by nlinarith only [hD80,hD0]
        calc
          _ = (2*D)*(D^6*ρ^s) := by ring
          _ ≤ D^2*(D^6*ρ^s) := mul_le_mul_of_nonneg_right hh (by positivity)
          _ = _ := by ring
      _ ≤ _ := by gcongr
  have hMfinal : 2*m ≤ E/ρ^s := hMM.trans (div_le_div_of_nonneg_right (powE 20 (by norm_num)) hρs.le)
  have hmfinal : 1/(E*ρ^s) ≤ m/(2*(Jf:ℝ)) := by
    apply le_trans _ hm8
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right (powE 8 (by norm_num)) hρs.le
  have hρeq : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hBfinal : 2*m ≤ E/Δ^s := by
    have hh := coarse_weight_scale_bound hΔ hsone hD80 (B := 2*m) (by simpa only [hρeq] using hMM)
    exact hh.trans (div_le_div_of_nonneg_right (powE 21 (by norm_num)) hΔs.le)
  apply hfalse n ((le_max_left _ _).trans hn) s t (m/(2*(Jf:ℝ))) (2*m)
    (1/(K*(Δ^s)^2)) (K/(Δ^s)^2) (D/(ρ^s)^2) (Jv:ℝ) (2*m) Q U S
    (fun _ p => V p) (fun c l => roundedIncidentLine ρ c (l 0)) G hs hs1 hgap ht
    (by positivity) (by positivity) hMfinal hmfinal (by positivity)
    (div_le_div_of_nonneg_right hDE' (sq_nonneg _)) hJv0 (hJvD.trans hDE') (by positivity) hBfinal
    (by gcongr) (by positivity) (by gcongr) hQ
    (fun c hc => hCchart c (hQC hc)) (finiteSeparatedAt_subset hQC hCsep)
    (mono_ball hρ.le hKF hQball)
  · intro c hc
    obtain ⟨_,_,hlo,hup,hchart,hsep,hball,hinc⟩ := hU c hc
    exact ⟨hlo,hup,hchart,hsep,mono_ball hρ.le hKF hball,hinc⟩
  · exact (Nat.cast_le.mpr (Finset.card_le_card hUC)).trans hTU
  · intro c hc
    obtain ⟨hne,hrect,hball⟩ := hcells c (hQC hc)
    exact ⟨hne,hrect,mono_ball hΔ.le (powE 5 (by norm_num)) hball⟩
  · intro c hc p hp
    have hpP := (Finset.mem_filter.mp hp).1
    obtain ⟨_,hsep,hball,hlo,hup,hinc⟩ := hV p hpP
    exact ⟨hlo,hup,hsep,mono_ball (sq_nonneg Δ) hKE hball,
      fun l hl => ⟨(hinc l hl).1.trans (by norm_num),(hinc l hl).2⟩⟩
  · exact fun c hc p hp l hl => hnear c (hQC hc) p hp l hl
  · intro c hc a ha
    have haT := (hU c hc).1 ha
    have hw := ((hT c (hQC hc)).2.2.2.2 a haT).2
    have hcard := (hband c (hQR hc)).2
    exact hw.trans (by gcongr)
  · exact fun c hc p hp l hl => hGmem c (hQC hc) p hp l hl
  · exact hUband
  · exact (hUsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hRu (fun a _ _ => Nat.cast_nonneg _))).trans
      (hGsum.trans (div_le_div_of_nonneg_right hDE' (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))

end Falconer

end OAI
