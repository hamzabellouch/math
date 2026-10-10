import OAI.MeasureTheory.Falconer.Geometry.NormalizedRegularGain
import OAI.MeasureTheory.Falconer.Incidence.SquashedPencils
import OAI.MeasureTheory.Falconer.Estimates.SquashGainBudget

namespace OAI

/-! Pencil-normalized gain for the full bounded point and line chart.
The fixed change of slope chart preserves original incidences and pays only
the explicitly proved finite thinning and covering losses. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem full_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
      ∀ n : ℕ, N0 ≤ n+2 →
        let Δ := 1/(2:ℝ)^n
        let δ := 1/(2:ℝ)^(2*n)
        let ρ := 1/(2:ℝ)^(n+3)
        let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
        ∀ s t m : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
        ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
          FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ t K P →
          ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
        ∀ V : Space 2 → Finset (Space 2),
          (∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K*m ∧
            InBoundedLineChart (V p) ∧ FiniteSeparatedAt δ (V p) ∧
            NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l) →
          ¬ ((P.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨θ,η,N1,hθ,_,hη,hN1,hgain⟩ := normalized_regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,_,hbudget⟩ := squash_gain_budget hθ hη
  refine ⟨ε,η/2,max N1 N2,hε,hε1,half_pos hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m hs hs1 hgap ht hm P hP hPchart hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(2*n)
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Δ' := 1/(2:ℝ)^(n+1)
  let E := Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ' : 0 < Δ' := by dsimp [Δ']; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hK0 : 0 < K := Real.exp_pos _
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hs2 : s ≤ 2 := by linarith only [hs1,hκ]
  have ht0 : 0 ≤ t := by linarith only [hs0,hgap,hκ]
  obtain ⟨hKE,h81⟩ := hbudget n ((le_max_right _ _).trans hn)
  have hΔeq : Δ' = Δ/2 := by dsimp [Δ',Δ]; rw [pow_succ]; ring
  have hδeq : 1/(2:ℝ)^(2*(n+1)) = δ/4 := by
    dsimp [δ]
    rw [show 2*(n+1) = 2*n+2 by omega,pow_add]
    norm_num
    ring
  have hρeq : 1/(2:ℝ)^((n+1)+3) = ρ/2 := by
    dsimp [ρ]
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]
    ring
  obtain ⟨R,hRP,hR,_,hchart,hsep,hball,W,_,hdata,hunion⟩ :=
    squashed_pencil_configuration hδ hs0 hs2 ht0 ht hK hm P V hP hPchart hPsep hPball hV
  have h25 : 25*K ≤ E := (by linarith only [hK0] : 25*K ≤ 20736*K).trans hKE
  have h81K : 81*K ≤ E := (by linarith only [hK0] : 81*K ≤ 20736*K).trans hKE
  have mono {u : ℝ} {S : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound (δ/4) u (20736*K) S) :
      NormalizedFiniteBallBound (δ/4) u E S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKE (Real.rpow_nonneg (by linarith only [hr,hδ]) _))
        (Nat.cast_nonneg _))
  have hcover : ((((R.image planarSquash).image (coarsePlanarRound (ρ/2))).card:ℝ)) ≤ E/Δ'^t := by
    calc
      _ ≤ 25*((R.image (coarsePlanarRound ρ)).card:ℝ) := planarSquash_coarse_cover hρ R
      _ ≤ 25*((P.image (coarsePlanarRound ρ)).card:ℝ) := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRP))) (by norm_num)
      _ ≤ 25*(K/Δ^t) := mul_le_mul_of_nonneg_left hPcover (by norm_num)
      _ = (25*K)/Δ^t := by ring
      _ ≤ E/Δ'^t := by
        gcongr
        rw [hΔeq]
        linarith only [hΔ]
  have hden : 81*(δ/4)^(s+η) ≤ δ^(s+η/2) := by
    calc
      _ ≤ 81*δ^(s+η) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [hδ]) (by linarith only [hs0,hη]))
        (by norm_num)
      _ ≤ δ^(-η/2)*δ^(s+η) := mul_le_mul_of_nonneg_right h81 (by positivity)
      _ = δ^(s+η/2) := by rw [← Real.rpow_add hδ]; congr 1; ring
  have hsize : m/δ^(s+η/2) ≤ (m/81)/(δ/4)^(s+η) := by
    calc
      _ ≤ m/(81*(δ/4)^(s+η)) := div_le_div_of_nonneg_left hm.le (by positivity) hden
      _ = _ := by ring
  refine hgain (n+1) (by have := (le_max_left N1 N2).trans hn; omega) s t (m/81) hs hs1 hgap ht
    (by positivity) (R.image planarSquash) (hR.image _) hchart ?_ ?_ ?_
      (squashedPencils W) ?_ ?_
  · rw [hδeq]
    exact hsep
  · rw [hδeq]
    convert mono hball using 1
  · rw [hρeq]
    convert hcover using 1
  · intro q hq
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hdata q hq
    rw [hδeq]
    refine ⟨hlo,?_,hch,hsp,?_,hinc⟩
    · calc
        _ ≤ K*m := hhi
        _ = (81*K)*(m/81) := by ring
        _ ≤ E*(m/81) := mul_le_mul_of_nonneg_right h81K (by positivity)
    · convert mono hb using 1
  · rw [hδeq]
    exact hunion.trans (hsmall.trans hsize)

end Falconer

end OAI
