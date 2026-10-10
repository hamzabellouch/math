import OAI.MeasureTheory.Falconer.Incidence.CoarseCellPencils
import OAI.MeasureTheory.Falconer.Incidence.OriginalCoarsePackets
import OAI.MeasureTheory.Falconer.Incidence.ComparableFrozenPencils
import OAI.MeasureTheory.Falconer.Incidence.RetainedCoarseIncidences

namespace OAI

/-! Original uniform fine pencils produce frozen coarse cells at every
intermediate scale. The point restrictions have explicit logarithmic costs. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_frozen_cells {δ ρ s K m M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C.Nonempty) (hCP : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ L E F : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧ F = 2*E*M/m ∧
      ∃ w : ℝ, 0 < w ∧ ∃ R ⊆ C, R.Nonempty ∧ (C.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U A : Space 2 → Finset (Space 2),
      let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
      let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
      (∀ c ∈ R,
        w/(2*(Jg:ℝ)) ≤ ((U c).card:ℝ) ∧ ((U c).card:ℝ) ≤ 2*w ∧
        InBoundedLineChart (U c) ∧ FiniteSeparatedAt ρ (U c) ∧
        NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U c) ∧
        (∀ a ∈ U c, TubeIncident ρ c a) ∧
        A c ⊆ S c ∧ (A c).Nonempty ∧ ((S c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
        ∀ p ∈ A c, W p ⊆ V p ∧ m/(2*E) ≤ ((W p).card:ℝ) ∧
          ((W p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (W p) ∧
          ∀ l ∈ W p, ∃ a ∈ U c, l ∈ G a) ∧
      (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
      (∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) ∧
      ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound ρ a| ≤ 1/2) →
        ∀ c ∈ R, ∀ a ∈ U c, |a 0| ≤ 1/2) := by
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  let S := fun c => P.filter fun p => q p = c
  let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hS (c : Space 2) (hc : c ∈ C) : (S c).Nonempty := by
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (hCP hc)
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,he⟩⟩
  have hVne (p : Space 2) (hp : p ∈ P) : (V p).Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le (hV p hp).1))
  obtain ⟨T,hT⟩ := coarse_cell_pencils hδ.le hρ hρ1 hδρ hs hK P C V q hCP hnear hchart
    (fun p hp => ⟨hVne p hp,(hV p hp).2.2.1,(hV p hp).2.2.2⟩)
  obtain ⟨hGne,_,hGmem,hGsum,hTsum⟩ := original_coarse_packets hδ.le hρ hδρ P C V T q hnear
    (fun c hc => (hchart c hc).1.trans (by norm_num))
    (fun p hp l hl => ⟨((hV p hp).2.2.2 l hl).1.trans (by norm_num),((hV p hp).2.2.2 l hl).2⟩)
    (fun c hc => (hT c hc).1)
  let Kc := 2*(K*7^s)*(Jv:ℝ)
  have hJv1 : 1 ≤ (Jv:ℝ) := by dsimp [Jv]; exact_mod_cast Nat.le_add_left 1 _
  have hKc : 1 ≤ Kc := by
    have h7 := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 7) hs
    have h1 : 1 ≤ K*7^s := by
      simpa using mul_le_mul hK h7 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    dsimp [Kc]
    nlinarith only [mul_le_mul h1 hJv1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ K*7^s)]
  have hCball : NormalizedFiniteBallBound ρ 0 Kc C := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hKc)
  have hGmax : ∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card := by
    intro a ha
    exact ⟨hGne a ha,(fineCoarsePacket_card_le _ _ _ _).trans (Finset.card_le_card (by
      intro l hl
      obtain ⟨c,_,hl⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
      exact Finset.mem_biUnion.mpr ⟨p,(Finset.mem_filter.mp hp).1,hl⟩))⟩
  obtain ⟨w,hw,R,hRC,hR,hmass,_,U,hU,_,hsum,k,hband⟩ := comparable_frozen_pencils
    hρ hKc C T G hC hCball (fun c hc => ⟨(hT c hc).2.1,(hT c hc).2.2.1,
      (hT c hc).2.2.2.1,(hT c hc).2.2.2.2.1,fun a ha => ((hT c hc).2.2.2.2.2.1 a ha).1⟩)
    (P.biUnion V).card hGmax
  let L := 4*((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ)*(Jg:ℝ)
  let E := 8*(Jv:ℝ)*(Jg:ℝ)
  let F := 2*E*M/m
  have hL : 0 < L := by dsimp [L]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hcoarse : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by
    exact_mod_cast hTsum.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr Finset.card_image_le) (by norm_num : (0:ℝ) ≤ 13))
  have hpow : (P.biUnion V).card < 2^Jg := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlt : (C.biUnion T).card < 2^(Jg+4) := by
    calc
      _ ≤ 13*(P.biUnion V).card := hcoarse
      _ ≤ 16*(P.biUnion V).card := Nat.mul_le_mul_right _ (by norm_num)
      _ < 16*2^Jg := Nat.mul_lt_mul_of_pos_left hpow (by norm_num)
      _ = _ := by rw [pow_add]; norm_num; ring
  have hlog : Nat.log 2 (C.biUnion T).card+1 ≤ 5*Jg := by
    have hh := Nat.log_lt_of_lt_pow' (by omega : Jg+4 ≠ 0) hlt
    have hj : 1 ≤ Jg := by dsimp [Jg]; omega
    omega
  have hLbound : L ≤ 20*(Jg:ℝ)^2 := by
    dsimp [L]
    have hh : ((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ) ≤ 5*(Jg:ℝ) := by exact_mod_cast hlog
    calc
      _ ≤ 4*(5*(Jg:ℝ))*(Jg:ℝ) := by gcongr
      _ = _ := by ring
  have he : (2*(Jv:ℝ))*(2*w)/(w/(2*(Jg:ℝ))) = E := by dsimp [E]; field_simp; ring
  have hzero (c : Space 2) : NormalizedFiniteBallBound δ 0 K (S c) := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hK)
  have hretain (c : Space 2) (hc : c ∈ R) := retain_coarse_incidences (H := 2*(Jv:ℝ)) (B := 2*w) (b := w/(2*(Jg:ℝ))) hδ.le
    (zero_le_one.trans hK) hm hM (mul_pos (by norm_num) hJv) (mul_pos (by norm_num) hw)
    (div_pos hw (mul_pos (by norm_num) hJg)) (S c) (U c) V (ql c)
    (hS c (hRC hc)) (hU c hc).2.2.2.2.1 (hzero c)
    (fun p hp => ⟨(hV p (Finset.mem_filter.mp hp).1).1,(hV p (Finset.mem_filter.mp hp).1).2.1,
      (hV p (Finset.mem_filter.mp hp).1).2.2.1⟩) (by
        intro a ha
        have haT := (hU c hc).2.2.1 ha
        have hh := ((hT c (hRC hc)).2.2.2.2.2.1 a haT).2
        exact hh.trans (by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hU c hc).2.1 (by positivity)))
  let A := fun c => if hc : c ∈ R then (hretain c hc).choose else ∅
  refine ⟨L,E,F,hL,hLbound,rfl,rfl,w,hw,R,hRC,hR,hmass,U,A,?_,hsum.trans hGsum,
    ⟨k,hband⟩,?_⟩
  · intro c hc
    have ha := (hretain c hc).choose_spec
    have hA : A c = (hretain c hc).choose := dite_eq_left hc
    rw [← hA] at ha
    rw [he] at ha
    refine ⟨(hU c hc).2.2.2.2.1,(hU c hc).2.2.2.2.2.1,
      (hU c hc).2.2.2.2.2.2.1,(hU c hc).2.2.2.2.2.2.2.1,
      (hU c hc).2.2.2.2.2.2.2.2.1,(hU c hc).2.2.2.2.2.2.2.2.2,
      ha.1,ha.2.1,ha.2.2.1,?_⟩
    intro p hp
    have hpc := (Finset.mem_filter.mp (ha.1 hp)).2
    simp only [hpc]
    obtain ⟨hsub,hlo,hup,hball⟩ := ha.2.2.2.2 p hp
    refine ⟨hsub,hlo,hup,hball,?_⟩
    intro l hl
    have hlV := hsub hl
    refine ⟨ql c l,(Finset.mem_filter.mp hl).2,?_⟩
    exact hGmem c (hRC hc) p (Finset.mem_filter.mp (ha.1 hp)).1 hpc l hlV
  · intro hround c hc a ha
    have haT := (hU c hc).2.2.1 ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ((hT c (hRC hc)).1 haT)
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact hround (l 0) (((hV p (Finset.mem_filter.mp hp).1).2.2.2 l hl).1)

end Falconer

end OAI
