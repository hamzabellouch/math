import OAI.MeasureTheory.Falconer.Radial.HeavyPacketCells
import OAI.MeasureTheory.Falconer.Incidence.CoarseCellPencils
import OAI.MeasureTheory.Falconer.Incidence.OriginalCoarsePackets

namespace OAI

/-! Construct the regular coarse cells, their pencils and their original
fine packets from the two covering assumptions in the regular-set alternative. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_preparation (n : ℕ) {s t K D : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 2)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D) (h13 : 13*K ≤ D)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ K/(1/(2:ℝ)^n)^t)
    (hline : (((P.biUnion V).image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      K/((1/(2:ℝ)^(n+3))^s)^2)
    (hsize : ((P.biUnion V).card:ℝ) ≤ K/((1/(2:ℝ)^n)^s)^4) :
    let Δ := 1/(2:ℝ)^n
    let ρ := 1/(2:ℝ)^(n+3)
    let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
    let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ C ⊆ P.image (coarsePlanarRound ρ), C.Nonempty ∧ InBoundedLineChart C ∧
      FiniteSeparatedAt ρ C ∧ NormalizedFiniteBallBound ρ t (D^5) C ∧
      (∀ c ∈ C, (S c).Nonempty ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ ∧ |p 1-c 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t (D^5) ((S c).image (localPacketPoint Δ (c 0) (c 1)))) ∧
      ∃ T : Space 2 → Finset (Space 2),
        (∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
          NormalizedFiniteBallBound ρ s (D^5) (T c) ∧
          ∀ a ∈ T c, TubeIncident ρ c a ∧
            ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
              (coarsePencilWeight (S c) V (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ)) ∧
        ((C.biUnion T).card:ℝ) ≤ D/(ρ^s)^2 ∧
        ((C.biUnion T).card:ℝ) ≤ 13*((P.biUnion V).card:ℝ) ∧
        let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
        (∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card) ∧
        (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ D/(Δ^s)^4 ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, l ∈ G (roundedIncidentLine ρ c (l 0))) ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, dist l (roundedIncidentLine ρ c (l 0)) ≤ Δ) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp := Nat.log 2 P.card+1
  let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscale : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hΔ8 : Δ ≤ 1/8 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num at hh
    exact hh
  have hΔ1 : Δ ≤ 1 := hΔ8.trans (by norm_num)
  have hρΔ : ρ ≤ Δ := by rw [hscale]; linarith only [hΔ]
  have hρ8 : ρ ≤ 1/8 := hρΔ.trans hΔ8
  have hδρ : Δ^2 ≤ ρ := by rw [hscale]; nlinarith only [hΔ8,hΔ]
  have hnear : ∀ p ∈ P, dist p (q p) ≤ ρ := fun p _ => coarsePlanarRound_near hρ p
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hD35 : D^3 ≤ D^5 := pow_le_pow_right₀ hD1 (by norm_num)
  have hD45 : D^4 ≤ D^5 := pow_le_pow_right₀ hD1 (by norm_num)
  have hquad (a : ℝ) (ha : a ≤ D) : a*D^2 ≤ D^3 := by
    calc
      _ ≤ D*D^2 := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
      _ = _ := by ring
  have hcube : 2*D^3 ≤ D^5 := by
    calc
      _ ≤ D*D^3 := mul_le_mul_of_nonneg_right (by linarith only [hD]) (pow_nonneg hD0 _)
      _ = D^4 := by ring
      _ ≤ _ := hD45
  have hcp : 8*K*(Jp:ℝ) ≤ D^5 := by
    calc
      _ ≤ 8*D*D := by gcongr
      _ = 8*D^2 := by ring
      _ ≤ D^3 := hquad 8 (by linarith only [hD])
      _ ≤ _ := hD35
  have hcl : 2*K*(Jp:ℝ)*K ≤ D^5 := by
    calc
      _ ≤ 2*D*D*D := by gcongr
      _ = 2*D^3 := by ring
      _ ≤ _ := hcube
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 7) hs1
  have hct : 2*(K*(7:ℝ)^s)*(J:ℝ) ≤ D^5 := by
    calc
      _ ≤ 2*(D*7)*D := by gcongr
      _ = 14*D^2 := by ring
      _ ≤ D^3 := hquad 14 (by linarith only [hD])
      _ ≤ _ := hD35
  have hqchart : ∀ c ∈ P.image q, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4 := by
    intro c hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    have bound (i : Fin 2) (hi : |p i| ≤ 1/8) : |q p i| ≤ 1/4 := by
      have hd : |q p i-p i| ≤ ρ := (show |q p i-p i| ≤ dist (q p) p by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (q p) p i).trans
          (by simpa only [dist_comm] using hnear p hp)
      calc
        _ = |(q p i-p i)+p i| := by congr 1; ring
        _ ≤ |q p i-p i|+|p i| := abs_add_le _ _
        _ ≤ 1/4 := by linarith only [hd,hi,hρ8]
    exact ⟨bound 0 (hPchart p hp).1,bound 1 (hPchart p hp).2⟩
  obtain ⟨_,C,hCsub,hC,hCball,_,hcell⟩ := heavy_regular_packet_cells hΔ hΔ1 hρ hδρ hρΔ
    ht ht1 hK (zero_le_one.trans hK) P hP q hnear hPball hpoint
  have hCchart : InBoundedLineChart C := fun c hc =>
    ⟨((hqchart c (hCsub hc)).1.trans (by norm_num)),((hqchart c (hCsub hc)).2.trans (by norm_num))⟩
  have hCsep := finiteSeparatedAt_subset hCsub (coarsePlanarRound_separated hρ P)
  obtain ⟨T,hT⟩ := coarse_cell_pencils (sq_nonneg Δ) hρ (hρ8.trans (by norm_num)) hδρ hs hK P C V q
    hCsub hnear (fun c hc => hqchart c (hCsub hc)) hV
  obtain ⟨hGne,hGsub,hGmem,hGsum,hTsum⟩ := original_coarse_packets (sq_nonneg Δ) hρ hδρ P C V T q
    hnear (fun c hc => (hCchart c hc).1)
    (fun p hp l hl => ⟨((hV p hp).2.2 l hl).1.trans (by norm_num),(hV p hp).2.2 l hl |>.2⟩)
    (fun c hc => (hT c hc).1)
  refine ⟨C,hCsub,hC,hCchart,hCsep,?_,?_,T,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z r hr hr1
    exact (hCball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcp (Real.rpow_nonneg (hρ.le.trans hr) _)) (Nat.cast_nonneg _))
  · intro c hc
    obtain ⟨_,hne,_,_,hrect,hball⟩ := hcell c hc
    refine ⟨hne,hrect,?_⟩
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcl (Real.rpow_nonneg (hΔ.le.trans hr) _)) (Nat.cast_nonneg _))
  · intro c hc
    obtain ⟨_,hne,hchart,hsep,hball,hinc,_⟩ := hT c hc
    refine ⟨hne,hchart,hsep,?_,hinc⟩
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg (hρ.le.trans hr) _)) (Nat.cast_nonneg _))
  · calc
      _ ≤ 13*(((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) := hTsum
      _ ≤ 13*(K/(ρ^s)^2) := mul_le_mul_of_nonneg_left hline (by norm_num)
      _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h13 (sq_nonneg _)
  · exact hTsum.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_image_le : (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ (P.biUnion V).card)
      (by norm_num))
  · exact fun a ha => ⟨hGne a ha,Finset.card_le_card (hGsub a)⟩
  · calc
      _ ≤ 13*((P.biUnion V).card:ℝ) := hGsum
      _ ≤ 13*(K/(Δ^s)^4) := mul_le_mul_of_nonneg_left hsize (by norm_num)
      _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h13 (pow_nonneg (Real.rpow_nonneg hΔ.le s) _)
  · exact fun c hc p hp l hl => hGmem c hc p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2 l hl
  · intro c hc p hp l hl
    have hh := (hT c hc).2.2.2.2.2.2 p hp l hl
    exact hh.trans (by rw [hscale]; linarith only [hΔ])

end Falconer

end OAI
