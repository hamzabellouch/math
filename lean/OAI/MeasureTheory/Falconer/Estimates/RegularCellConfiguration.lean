import OAI.MeasureTheory.Falconer.Radial.HeavyPacketCells
import OAI.MeasureTheory.Falconer.Incidence.CoarseCellPencils
import OAI.MeasureTheory.Falconer.Incidence.OriginalCoarsePackets

namespace OAI

/-! The regular coarse configuration with its original cell occupancies and
fine mass retained. No small coarse-tube cover is assumed here. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_cell_configuration (n : ℕ) {s t K : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht1 : t ≤ 2) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      K/(1/(2:ℝ)^n)^t) :
    let Δ := 1/(2:ℝ)^n
    let ρ := 1/(2:ℝ)^(n+3)
    let q := coarsePlanarRound ρ
    let S := fun c => P.filter fun p => q p = c
    let Jp := Nat.log 2 P.card+1
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      (∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4) ∧ FiniteSeparatedAt ρ C ∧
      NormalizedFiniteBallBound ρ t (8*K*(Jp:ℝ)) C ∧
      (P.card:ℝ) ≤ (Jp:ℝ)*(∑ c ∈ C, ((S c).card:ℝ)) ∧
      (∀ c ∈ C, (S c).Nonempty ∧ 2^k ≤ (S c).card ∧ (S c).card < 2^(k+1) ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ/4 ∧ |p 1-c 1| ≤ Δ/4) ∧
        NormalizedFiniteBallBound Δ t (2*K*(Jp:ℝ)*K)
          ((S c).image (localPacketPoint Δ (c 0) (c 1)))) ∧
      ∃ T : Space 2 → Finset (Space 2),
        (∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
          NormalizedFiniteBallBound ρ s (2*(K*7^s)*(Jv:ℝ)) (T c) ∧
          ∀ a ∈ T c, TubeIncident ρ c a ∧
            ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(Jv:ℝ)*((T c).card:ℝ)*
              (coarsePencilWeight (S c) V (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ)) ∧
        ((C.biUnion T).card:ℝ) ≤ 13*(((P.biUnion V).image q).card:ℝ) ∧
        let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
        (∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card) ∧
        (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, l ∈ G (roundedIncidentLine ρ c (l 0))) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscale : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hΔ8 : Δ ≤ 1/8 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num at hh
    exact hh
  have hδρ : Δ^2 ≤ ρ := by rw [hscale]; nlinarith only [hΔ8,hΔ]
  have hρΔ : ρ ≤ Δ := by rw [hscale]; linarith only [hΔ]
  have hρ8 : ρ ≤ 1/8 := hρΔ.trans hΔ8
  have hnear : ∀ p ∈ P, dist p (q p) ≤ ρ := fun p _ => coarsePlanarRound_near hρ p
  have hqchart : ∀ c ∈ P.image q, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4 := by
    intro c hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    have bound (i : Fin 2) (hi : |p i| ≤ 1/8) : |q p i| ≤ 1/4 := by
      have hd : |q p i-p i| ≤ ρ := (show |q p i-p i| ≤ dist (q p) p by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (q p) p i).trans
          (by simpa only [dist_comm] using hnear p hp)
      calc
        _ ≤ |q p i-p i|+|p i| := by simpa using abs_add_le (q p i-p i) (p i)
        _ ≤ 1/4 := by linarith only [hd,hi,hρ8]
    exact ⟨bound 0 (hPchart p hp).1,bound 1 (hPchart p hp).2⟩
  obtain ⟨k,C,hCP,hC,hCb,hmass,hcells⟩ := heavy_regular_packet_cells hΔ
    (hΔ8.trans (by norm_num)) hρ hδρ hρΔ ht ht1 hK (zero_le_one.trans hK)
    P hP q hnear hPball hpoint
  have hCchart := fun c hc => hqchart c (hCP hc)
  obtain ⟨T,hT⟩ := coarse_cell_pencils (sq_nonneg Δ) hρ (hρ8.trans (by norm_num)) hδρ
    hs hK P C V q hCP hnear hCchart hV
  obtain ⟨hGne,hGsub,hGmem,hGsum,hTsum⟩ := original_coarse_packets (sq_nonneg Δ)
    hρ hδρ P C V T q hnear (fun c hc => (hCchart c hc).1.trans (by norm_num))
    (fun p hp l hl => ⟨((hV p hp).2.2 l hl).1.trans (by norm_num),(hV p hp).2.2 l hl |>.2⟩)
    (fun c hc => (hT c hc).1)
  refine ⟨k,C,hCP,hC,hCchart,finiteSeparatedAt_subset hCP (coarsePlanarRound_separated hρ P),
    hCb,hmass,?_,T,?_,hTsum,?_,hGsum,?_⟩
  · intro c hc
    obtain ⟨_,hne,hlo,hup,_,hball⟩ := hcells c hc
    refine ⟨hne,hlo,hup,?_,hball⟩
    intro p hp
    have hd := hnear p (Finset.mem_filter.mp hp).1
    have hpc : q p = c := (Finset.mem_filter.mp hp).2
    rw [hpc] at hd
    have h0 : |p 0-c 0| ≤ dist p c := by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0
    have h1 : |p 1-c 1| ≤ dist p c := by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1
    rw [hscale] at hd
    constructor <;> linarith only [h0,h1,hd,hΔ]
  · intro c hc
    obtain ⟨_,hne,hchart,hsep,hreg,hweight,_⟩ := hT c hc
    exact ⟨hne,hchart,hsep,hreg,hweight⟩
  · exact fun a ha => ⟨hGne a ha,Finset.card_le_card (hGsub a)⟩
  · exact fun c hc p hp l hl => hGmem c hc p (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hp).2 l hl

end Falconer

end OAI
