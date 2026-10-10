import OAI.MeasureTheory.Falconer.Estimates.RegularRefinementData

namespace OAI

/-! Assemble the retained regular refinement from coarse cells and original
weighted pencils. All selection costs fit a fixed polynomial budget. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem ball_constant_mono {δ s A B : ℝ} {P : Finset (Space 2)}
    (hδ : 0 ≤ δ) (hAB : A ≤ B) (h : NormalizedFiniteBallBound δ s A P) :
    NormalizedFiniteBallBound δ s B P := by
  intro z r hr hr1
  exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

theorem build_regular_refinement (n k : ℕ) {s t D : ℝ}
    (hn : 3 ≤ n) (hD : 80 ≤ D)
    (P C : Finset (Space 2)) (V T G : Space 2 → Finset (Space 2))
    (hC : C.Nonempty) (hCchart : InBoundedLineChart C)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t (D^4) P)
    (hCb : NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t (D^4) C)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hJc : (Nat.log 2 (C.biUnion T).card+1:ℕ) ≤ D)
    (hJg : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D)
    (hmass : (P.card:ℝ) ≤ (Nat.log 2 P.card+1:ℕ)*
      ∑ c ∈ C, ((P.filter fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c).card:ℝ))
    (hcell : ∀ c ∈ C,
      let S := P.filter fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c
      S.Nonempty ∧ 2^k ≤ S.card ∧ S.card < 2^(k+1) ∧
      (∀ p ∈ S, |p 0-c 0| ≤ (1/(2:ℝ)^n)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^n)/4) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^n) t (D^4)
        (S.image (localPacketPoint (1/(2:ℝ)^n) (c 0) (c 1))))
    (hV : ∀ p ∈ P,
      1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s (D^4) (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hT : ∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (T c) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s (D^4) (T c) ∧
      ∀ a ∈ T c, TubeIncident (1/(2:ℝ)^(n+3)) c a ∧
        ((∑ p ∈ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c), (V p).card):ℝ) ≤
          2*(Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ)*((T c).card:ℝ)*
            (coarsePencilWeight (P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c))
              V (fun l => roundedIncidentLine (1/(2:ℝ)^(n+3)) c (l 0)) a:ℝ))
    (hG : ∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card)
    (hGsum : (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ))
    (hGcap : ∀ c ∈ C, ∀ p ∈ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c),
      ∀ l ∈ V p, l ∈ G (roundedIncidentLine (1/(2:ℝ)^(n+3)) c (l 0))) :
    Nonempty (RegularRefinementData n s t (D^40) P V) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp : ℝ := ((Nat.log 2 P.card+1:ℕ):ℝ)
  let Jv : ℝ := ((Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ):ℝ)
  let Jc : ℝ := ((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ)
  let Jg : ℝ := ((Nat.log 2 (P.biUnion V).card+1:ℕ):ℝ)
  let L := 4*Jc*Jg
  let mF := 1/(D*(Δ^s)^2)
  let MF := D/(Δ^s)^2
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hmF : 0 < mF := by dsimp [mF]; positivity
  have hMF : 0 < MF := by dsimp [MF]; positivity
  have hJp0 : 0 ≤ Jp := by dsimp [Jp]; positivity
  have hJv0 : 0 < Jv := by dsimp [Jv]; positivity
  have hJg0 : 0 < Jg := by dsimp [Jg]; positivity
  have hJc0 : 0 < Jc := by dsimp [Jc]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hJpR : Jp ≤ D := by
    simpa only [Jp,Nat.cast_add,Nat.cast_one] using hJp
  have hJvR : Jv ≤ D := by
    simpa only [Jv,Nat.cast_add,Nat.cast_one] using hJv
  have hJcR : Jc ≤ D := by
    simpa only [Jc,Nat.cast_add,Nat.cast_one] using hJc
  have hJgR : Jg ≤ D := by
    simpa only [Jg,Nat.cast_add,Nat.cast_one] using hJg
  have hL : L ≤ D^3 := by
    calc
      L ≤ 4*D*D := by dsimp [L]; gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have pow40 (a : ℕ) (ha : a ≤ 40) : D^a ≤ D^40 := pow_le_pow_right₀ hD1 ha
  obtain ⟨m,hm,R,hRC,hR,hRsize,hRb,U,hU,hUT,hGsumR,j,hGband⟩ := comparable_frozen_pencils
    hρ (one_le_pow₀ hD1 (n := 4)) C T G hC hCb
    (fun c hc => ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.1,
      (hT c hc).2.2.2.1,fun l hl => ((hT c hc).2.2.2.2 l hl).1⟩) (P.biUnion V).card hG
  let E := (2*Jv)*(2*m)/(m/(2*Jg))
  let F := 2*E*MF/mF
  have hEeq : E = 8*Jv*Jg := by dsimp [E]; field_simp; ring
  have hE : E ≤ D^3 := by
    rw [hEeq]
    calc
      8*Jv*Jg ≤ 8*D*D := by gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have hE0 : 0 < E := by rw [hEeq]; positivity
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hFeq : F = 2*E*D^2 := by dsimp [F,MF,mF]; field_simp
  have hF : F ≤ D^7 := by
    rw [hFeq]
    calc
      _ ≤ D*D^3*D^2 := by gcongr; linarith only [hD]
      _ = D^6 := by ring
      _ ≤ D^7 := pow_le_pow_right₀ hD1 (by norm_num)
  have hmassbound : 2*Jp*L*F ≤ D^40 := by
    calc
      _ ≤ D*D*D^3*D^7 := by gcongr; linarith only [hD]
      _ = D^12 := by ring
      _ ≤ _ := pow40 12 (by norm_num)
  have hregbound : D^4*F ≤ D^40 := by
    calc
      _ ≤ D^4*D^7 := mul_le_mul_of_nonneg_left hF (pow_nonneg hD0.le _)
      _ = D^11 := by ring
      _ ≤ _ := pow40 11 (by norm_num)
  have hcregbound : D^4*L ≤ D^40 := by
    calc
      _ ≤ D^4*D^3 := mul_le_mul_of_nonneg_left hL (pow_nonneg hD0.le _)
      _ = D^7 := by ring
      _ ≤ _ := pow40 7 (by norm_num)
  let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
  obtain ⟨A,hA,hAP,hAne,hAsize,_⟩ := retained_regular_cells (sq_nonneg Δ) hΔ.le
    (one_le_pow₀ hD1 (n := 4)) hmF hMF (mul_pos (by norm_num : (0:ℝ) < 2) hJv0)
    (mul_pos (by norm_num : (0:ℝ) < 2) hm) (div_pos hm (mul_pos (by norm_num : (0:ℝ) < 2) hJg0)) hJp0 hL0
    (by positivity : 0 ≤ (2:ℝ)^k) P C R q V U
    (fun c l => roundedIncidentLine ρ c (l 0)) (fun c => localPacketPoint Δ (c 0) (c 1)) hR hRC
    hPball hmass (fun c hc => ⟨by
      have hh : 2^k ≤ (S c).card := (hcell c hc).2.1
      exact_mod_cast hh,by
      have hhN : (S c).card < 2^(k+1) := (hcell c hc).2.2.1
      have hh : ((S c).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast hhN
      simpa only [pow_succ,mul_comm] using hh.le⟩) hRsize
    (fun c hc => ⟨(hcell c (hRC hc)).1,localPacketPoint_injective hΔ _ _,(hcell c (hRC hc)).2.2.2.2⟩)
    (fun p hp => ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.1⟩) (fun c hc => by
      refine ⟨(hU c hc).2.2.2.2.1,?_⟩
      intro a ha
      have hh := ((hT c (hRC hc)).2.2.2.2 a ((hU c hc).2.2.1 ha)).2
      have hupper := (hU c hc).2.1
      have hweight0 : 0 ≤ (coarsePencilWeight (S c) V
        (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ) := Nat.cast_nonneg _
      apply (show (∑ p ∈ S c, ((V p).card:ℝ)) ≤ _ by simpa only [Nat.cast_sum] using hh).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper (show 0 ≤ 2*Jv by positivity)) hweight0)
  have hRchart : InBoundedLineChart R := fun c hc => hCchart c (hRC hc)
  have hmin : ∀ c ∈ R, m/(D^40) ≤ ((U c).card:ℝ) := by
    intro c hc
    apply le_trans _ (hU c hc).2.2.2.2.1
    apply div_le_div_of_nonneg_left hm.le (by positivity)
    exact (show 2*Jg ≤ D^2 by nlinarith only [hJgR,hD]).trans (pow40 2 (by norm_num))
  have hfinemin : 1/(D^40*(Δ^s)^2) ≤ mF/(2*E) := by
    have hcoef : 2*D*E ≤ D^40 := by
      calc
        _ ≤ D*D*D^3 := by gcongr; linarith only [hD]
        _ = D^5 := by ring
        _ ≤ _ := pow40 5 (by norm_num)
    calc
      _ ≤ 1/((2*D*E)*(Δ^s)^2) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      _ = _ := by dsimp [mF]; field_simp
  refine ⟨{
    cells := R
    pencils := U
    points := A
    fine := W
    packets := G
    width := m
    level := j
    width_pos := hm
    cells_nonempty := hR
    cells_chart := hRchart
    cells_regular := ball_constant_mono hρ.le hcregbound hRb
    pencil_data := ?_
    point_data := ?_
    point_mass := ?_
    fine_data := ?_
    packet_cover := ?_
    packet_sum := hGsumR.trans hGsum
    packet_band := hGband
    coarse_cover := ?_ }⟩
  · intro c hc
    obtain ⟨_,hmax,hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩ := hU c hc
    refine ⟨hmin c hc,hup.trans ?_,hchart,hsep,ball_constant_mono hρ.le hcregbound hball,hinc⟩
    exact mul_le_mul_of_nonneg_right (show 2 ≤ D^40 from
      (show (2:ℝ) ≤ D by linarith only [hD]).trans (by simpa using pow40 1 (by norm_num))) hm.le
  · intro c hc
    refine ⟨(hA c hc).1,(hA c hc).2.1,?_,ball_constant_mono hΔ.le hregbound (hA c hc).2.2.2.1⟩
    exact fun p hp => (hcell c (hRC hc)).2.2.2.1 p ((hA c hc).1 hp)
  · exact hAsize.trans (mul_le_mul_of_nonneg_right hmassbound (Nat.cast_nonneg _))
  · intro c hc p hp
    obtain ⟨hsub,hlo,hup,hball,_⟩ := (hA c hc).2.2.2.2 p hp
    refine ⟨hsub,hfinemin.trans hlo,hup.trans ?_,ball_constant_mono (sq_nonneg Δ) hregbound hball⟩
    exact div_le_div_of_nonneg_right (by simpa using pow40 1 (by norm_num)) (sq_nonneg _)
  · intro c hc p hp l hl
    have hd := (hA c hc).2.2.2.2 p hp
    refine ⟨roundedIncidentLine ρ c (l 0),hd.2.2.2.2 l hl,?_⟩
    exact hGcap c (hRC hc) p ((hA c hc).1 hp) l (hd.1 hl)
  · have hδρ : Δ^2 ≤ ρ := by
      have he : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
      have hd : Δ ≤ 1/8 := by
        apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
        norm_num at hh
        exact hh
      rw [he]
      nlinarith only [hd,hΔ]
    have hres : ∀ c ∈ R, ∀ l ∈ (A c).biUnion W, |c 1-l 0*c 0-l 1| ≤ 4*ρ := by
      intro c hc l hl
      obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
      have hpc : q p = c := (Finset.mem_filter.mp ((hA c hc).1 hp)).2
      have hpP := (Finset.mem_filter.mp ((hA c hc).1 hp)).1
      have hVpl := (hA c hc).2.2.2.2 p hp |>.1 hl
      exact moved_point_residual (sq_nonneg Δ) hρ hδρ p c l
        (by simpa only [← hpc] using coarsePlanarRound_near hρ p)
        (((hV p hpP).2.2.2 l hVpl).1.trans (by norm_num)) ((hV p hpP).2.2.2 l hVpl).2
    have hc := retained_coarse_cover_card hρ R (fun c => (A c).biUnion W) U
      (fun c hc => (hRchart c hc).1) hres (fun c hc l hl => by
        obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
        exact (hA c hc).2.2.2.2 p hp |>.2.2.2.2 l hl)
    simpa only [Finset.biUnion_biUnion] using hc

end Falconer

end OAI
