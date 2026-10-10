import OAI.MeasureTheory.Falconer.Estimates.RegularRefinementBound
import OAI.MeasureTheory.Falconer.Estimates.RegularRefinementData
import OAI.MeasureTheory.Falconer.Estimates.GeneralRegularSetAlternative

namespace OAI

/-! The regular-set alternative and the normalized scale comparison
exclude a small fine union once the original configuration is refined. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem regular_refinement_contradiction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ n+2 → 3 ≤ n →
      let Δ := 1/(2:ℝ)^n
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t u β D : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
        0 ≤ u → u < t → 0 < β → β < 1 → u = s*(1-β)+2*β →
        80 ≤ D → D^2 ≤ E → D^40 < E^β →
        planarPotentialConstant s t ≤ D → planarPotentialConstant u t ≤ D →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t D P →
        ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ D/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, InBoundedLineChart (V p) ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        RegularRefinementData n s t D P V → ¬ ((P.biUnion V).card:ℝ) ≤ D/(Δ^s)^4 := by
  obtain ⟨ε,N₀,hε,_,hN₀,hmain⟩ := general_regular_coarse_cover_alternative hκ (hκ1.trans (by norm_num))
  refine ⟨ε,N₀,hε,hN₀,?_⟩
  intro n hn hn3
  dsimp only
  intro s t u β D hs hs1 hgap ht hu hut hβ hβ1 huEq hD hDE hpower hp hpu
    P hP hPsmall hPsep hPball hPcover V hV F hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Q := F.cells.biUnion F.points
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hDle : D ≤ E := (by nlinarith only [hD1] : D ≤ D^2).trans hDE
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have hQP : Q ⊆ P := by
    intro p hp
    obtain ⟨c,hc,hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp ((F.point_data c hc).1 hp)).1
  have hQ : Q.Nonempty := by
    obtain ⟨c,hc⟩ := F.cells_nonempty
    obtain ⟨p,hp⟩ := (F.point_data c hc).2.1
    exact ⟨p,Finset.mem_biUnion.mpr ⟨c,hc,hp⟩⟩
  have mono {d v A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {S : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d v A S) : NormalizedFiniteBallBound d v B S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hQball : NormalizedFiniteBallBound (Δ^2) t E Q := by
    have hb := normalized_finite_ball_bound_subset (sq_nonneg Δ) hD0.le hQP F.point_mass hPball
    exact mono (sq_nonneg Δ) (by simpa only [pow_two] using hDE) hb
  have hQunion : Q.biUnion F.fine ⊆ P.biUnion V := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨c,hc,hpc⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨p,hQP hp,(F.fine_data c hc p hpc).1 hl⟩
  have hAupper : ¬ ((F.cells.biUnion F.pencils).card:ℝ) ≤ E/(13*(ρ^s)^2) := by
    intro hA
    apply hmain n hn s t hs hs1 hgap ht Q hQ (fun p hp => hPsmall p (hQP hp))
      (finiteSeparatedAt_subset hQP hPsep) hQball
    · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hQP))).trans
        (hPcover.trans (div_le_div_of_nonneg_right hDle (Real.rpow_nonneg hΔ.le _)))
    · intro p hp
      obtain ⟨c,hc,hpc⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hsub,hlo,_,hb⟩ := F.fine_data c hc p hpc
      have hpos : 0 < ((F.fine p).card:ℝ) := (by positivity : 0 < 1/(D*(Δ^s)^2)).trans_le hlo
      exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp hpos),
        fun l hl => (hV p (hQP hp)).1 l (hsub hl),
        finiteSeparatedAt_subset hsub (hV p (hQP hp)).2.1,
        mono (sq_nonneg Δ) hDle hb,
        fun l hl => (hV p (hQP hp)).2.2 l (hsub hl)⟩
    · constructor
      · exact (Nat.cast_le.mpr (Finset.card_le_card hQunion)).trans
          (hsmall.trans (div_le_div_of_nonneg_right hDle (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))
      · apply F.coarse_cover.trans
        have hh := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 13)
        change 13*((F.cells.biUnion F.pencils).card:ℝ) ≤ E/(ρ^s)^2
        exact hh.trans_eq (by field_simp)
  have ha : E/13 ≤ ((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 13*(ρ^s)^2)).1 (lt_of_not_ge hAupper)
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 13)).2
    nlinarith only [hh]
  obtain ⟨c,hc⟩ := F.cells_nonempty
  have hbounded := regular_refinement_coarse_bound n F.level hn3 hD F.width_pos hs0 hsone hst
    hu hut hβ hβ1 huEq hp hpu F.cells (F.points c) (P.biUnion V) F.pencils F.fine F.packets c hc
    (F.point_data c hc).2.1 F.cells_chart F.cells_regular F.pencil_data
    (F.point_data c hc).2.2.1 (F.point_data c hc).2.2.2
    (fun p hp => ⟨(F.fine_data c hc p hp).2.1,(F.fine_data c hc p hp).2.2.1,
      (F.fine_data c hc p hp).2.2.2,
      fun l hl => (hV p (Finset.mem_filter.mp ((F.point_data c hc).1 hp)).1).2.2 l
        ((F.fine_data c hc p hp).1 hl)⟩)
    (F.packet_cover c hc) F.packet_band F.packet_sum hsmall
  have hEp : E^β ≤ 13^β*D^37 := by
    have hEE : E ≤ 13*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2) :=
      by
        convert (div_le_iff₀ (by norm_num : (0:ℝ) < 13)).1 ha using 1
        ring
    calc
      E^β ≤ (13*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2))^β :=
        Real.rpow_le_rpow (Real.exp_pos _).le hEE hβ.le
      _ = 13^β*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2)^β :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbounded (by positivity)
  have h13 : (13:ℝ)^β ≤ D := by
    apply le_trans _ (show (13:ℝ) ≤ D by linarith only [hD])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 13) hβ1.le
  have hh : E^β ≤ D^40 := calc
    E^β ≤ 13^β*D^37 := hEp
    _ ≤ D*D^37 := mul_le_mul_of_nonneg_right h13 (pow_nonneg hD0.le _)
    _ = D^38 := by ring
    _ ≤ D^40 := pow_le_pow_right₀ hD1 (by norm_num)
  exact (not_lt_of_ge hh) hpower

end Falconer

end OAI
