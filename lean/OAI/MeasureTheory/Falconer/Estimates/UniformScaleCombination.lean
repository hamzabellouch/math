import OAI.MeasureTheory.Falconer.Incidence.UniformFrozenCells
import OAI.MeasureTheory.Falconer.Measures.RescaledScaleProduct

namespace OAI

/-! The scale-product construction for original cell configurations. Coarse
pencils and every local pencil are constructed, with explicit logarithmic losses. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_scale_combination {δ ρ s t K KP m M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hm : 0 < m) (hM : 0 < M)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C.Nonempty) (hCP : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : ∀ c ∈ C, NormalizedFiniteBallBound (δ/(4*ρ)) t KP
      ((P.filter fun p => q p = c).image (localPacketPoint (4*ρ) (c 0) (c 1))))
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ L E F w : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧
      F = 2*E*M/m ∧ 0 < w ∧
      ∃ R ⊆ C, R.Nonempty ∧ (C.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ c ∈ R, w/(2*(Jg:ℝ)) ≤ ((U c).card:ℝ) ∧ ((U c).card:ℝ) ≤ 2*w ∧
          InBoundedLineChart (U c) ∧ FiniteSeparatedAt ρ (U c) ∧
          NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U c) ∧
          ∀ a ∈ U c, TubeIncident ρ c a) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound ρ a| ≤ 1/2) →
          ∀ c ∈ R, ∀ a ∈ U c, |a 0| ≤ 1/2) ∧
        ∀ c ∈ R, ∃ j : ℕ, ∃ Q ⊆ (S c).image (localPacketPoint (4*ρ) (c 0) (c 1)),
          Q.Nonempty ∧ ((S c).card:ℝ) ≤ (F*(Jg:ℝ))*(Q.card:ℝ) ∧
          (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
          FiniteSeparatedAt (δ/(4*ρ)) Q ∧
          NormalizedFiniteBallBound (δ/(4*ρ)) t ((KP*F)*(Jg:ℝ)) Q ∧
          ∃ T : Space 2 → Finset (Space 2),
            (∀ p ∈ Q, (T p).Nonempty ∧ InBoundedLineChart (T p) ∧
              FiniteSeparatedAt (δ/(4*ρ)) (T p) ∧
              NormalizedFiniteBallBound (δ/(4*ρ)) s (2*(((K*F)*3^s)*7^s)*(Jg:ℝ)) (T p) ∧
              (∀ l ∈ T p, TubeIncident (δ/(4*ρ)) p l) ∧
              (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j) ≤ ((T p).card:ℝ) ∧
              ((T p).card:ℝ) ≤ M/(2:ℝ)^j) ∧
            (((R.biUnion U).card:ℝ)/(w/(2*(Jg:ℝ))))*
              (((Q.biUnion T).card:ℝ)/((m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j))) ≤
                (43264*(Jv:ℝ)*(Jg:ℝ)^3)*(((P.biUnion V).card:ℝ)/m) ∧
            ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/(4*ρ)) a| ≤ 1/2) →
              ∀ p ∈ Q, ∀ l ∈ T p, |l 0| ≤ 1/2) := by
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  let S := fun c => P.filter fun p => q p = c
  obtain ⟨L,E,F,hL,hLb,hEeq,hFeq,w,hw,R,hRC,hR,hcount,U,A,hdata,hGsum,⟨k,hGband⟩,hslopes⟩ :=
    uniform_frozen_cells hδ hρ (hρ1.trans (by norm_num)) hδρ hs hK hm hM P C V q hC hCP hnear hchart hV
  let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hE : 0 < E := by rw [hEeq]; positivity
  have hF : 0 < F := by rw [hFeq]; positivity
  refine ⟨L,E,F,w,hL,hLb,hEeq,hFeq,hw,R,hRC,hR,hcount,U,?_,hslopes,?_⟩
  · intro c hc
    obtain ⟨hl,hu,hch,hsep,hreg,hinc,_⟩ := hdata c hc
    exact ⟨hl,hu,hch,hsep,hreg,hinc⟩
  intro c hc
  obtain ⟨_,hUmax,_,_,_,_,hAS,hA,hAmass,hfine⟩ := hdata c hc
  have hAP : A c ⊆ P := hAS.trans (Finset.filter_subset _ _)
  have hF1 : 1 ≤ F := by
    have ha : 0 < ((A c).card:ℝ) := Nat.cast_pos.mpr hA.card_pos
    have hs : ((A c).card:ℝ) ≤ ((S c).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hAS)
    nlinarith only [ha,hs,hAmass]
  have hKF : 1 ≤ K*F := by
    simpa using mul_le_mul hK hF1 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  have hpoint : NormalizedFiniteBallBound (δ/(4*ρ)) t (KP*F)
      ((A c).image (localPacketPoint (4*ρ) (c 0) (c 1))) := by
    have himass : (((S c).image (localPacketPoint (4*ρ) (c 0) (c 1))).card:ℝ) ≤
        F*(((A c).image (localPacketPoint (4*ρ) (c 0) (c 1))).card:ℝ) := by
      simpa only [Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity : 0 < 4*ρ) _ _)] using hAmass
    exact normalized_finite_ball_bound_subset (by positivity) hKP (Finset.image_subset_image hAS) himass (hPball c (hRC hc))
  have hcell : ∀ p ∈ A c, |p 0-c 0| ≤ (4*ρ)/4 ∧ |p 1-c 1| ≤ (4*ρ)/4 := by
    intro p hp
    have hh : dist p c ≤ ρ := by simpa only [(Finset.mem_filter.mp (hAS hp)).2] using hnear p (hAP hp)
    constructor
    · exact (show |p 0-c 0| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans (by linarith only [hh])
    · exact (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans (by linarith only [hh])
  have hWdata : ∀ p ∈ A c, (W p).Nonempty ∧ m/(2*E) ≤ ((W p).card:ℝ) ∧
      ((W p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (W p) ∧
      ∀ l ∈ W p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l := by
    intro p hp
    obtain ⟨hsub,hlo,hup,hreg,_⟩ := hfine p hp
    exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp ((by positivity : 0 < m/(2*E)).trans_le hlo)),
      hlo,hup,hreg,fun l hl => (hV p (hAP hp)).2.2.2 l (hsub hl)⟩
  have hWD : ∀ p ∈ A c, (W p).card ≤ (P.biUnion V).card := by
    intro p hp
    exact Finset.card_le_card (((hfine p hp).1).trans (Finset.subset_biUnion_of_mem V (hAP hp)))
  have hGbandR : ∀ b ∈ R.biUnion U, (2:ℝ)^k ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*(2:ℝ)^k := by
    intro b hb
    have hh := hGband b hb
    constructor
    · exact_mod_cast hh.1
    · have hi : ((G b).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast hh.2
      simpa only [pow_succ,mul_comm] using hi.le
  obtain ⟨j,Q,hQA,hQ,hsize,hsmall,hsep,hreg,T,hT,hproduct,hlocalSlopes⟩ := rescaled_cell_scale_product
    hδ (by positivity : 0 < 4*ρ) (by linarith only [hρ1])
    ((div_le_iff₀ (by positivity : 0 < 4*ρ)).2 (by linarith only [hδρ,hρ])) hs hKF
    (mul_nonneg hKP hF.le) ((hchart c (hRC hc)).1.trans (by norm_num)) (A c) W hA hcell
    (finiteSeparatedAt_subset hAP hPsep) hpoint hWdata (P.biUnion V).card hWD
    (by positivity : 0 < m/(2*E)) (by positivity : 0 < w/(2*(Jg:ℝ)))
    (by positivity : 0 < (2:ℝ)^k) (by norm_num : (0:ℝ) ≤ 13) (by positivity : 0 ≤ 2*w)
    (R.biUnion U) (U c) (P.biUnion V) G (Finset.subset_biUnion_of_mem U hc) hUmax
    (fun p hp l hl => (hfine p hp).2.2.2.2 l hl) hGbandR hGsum
  refine ⟨j,Q,hQA.trans (Finset.image_subset_image hAS),hQ,?_,hsmall,hsep,hreg,T,hT,?_,hlocalSlopes⟩
  · calc
      _ ≤ F*((A c).card:ℝ) := hAmass
      _ ≤ F*((Jg:ℝ)*(Q.card:ℝ)) := mul_le_mul_of_nonneg_left hsize hF.le
      _ = _ := by ring
  · convert hproduct using 1
    rw [hEeq]
    field_simp
    ring

end Falconer

end OAI
