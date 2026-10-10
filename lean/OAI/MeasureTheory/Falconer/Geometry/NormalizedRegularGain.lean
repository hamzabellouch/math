import OAI.MeasureTheory.Falconer.Geometry.BoundedChartFineGain
import OAI.MeasureTheory.Falconer.Incidence.InterpolatedPencilGain
import OAI.MeasureTheory.Falconer.Incidence.PencilGainAlgebra

namespace OAI

/-! The good-scale estimate normalized by the actual pencil cardinality.
Small pencils use the regular-set theorem, and large pencils use the
interpolated second moment. No upper bound on the union is assumed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem normalized_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
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
            NormalizedFiniteBallBound δ s K (V p) ∧
            ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) →
          ¬ ((P.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨θ,N1,hθ,_,hN1,hgain⟩ := bounded_chart_regular_fine_gain hκ hκ1
  let A := 80*25921*(1+projectionGapConstant κ)
  have hA : 0 ≤ A := by
    have hh := projectionGapConstant_pos hκ
    dsimp [A]
    positivity
  obtain ⟨ε,γ,η,N2,hε,hε1,_,hη,hN2,hrel,hbudget⟩ :=
    normalized_regular_gain_budget hκ hκ1 hθ hA
  refine ⟨ε,η,max N1 N2,hε,hε1,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m hs hs1 hgap ht hm P hP hPchart hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(2*n)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδeq : δ = Δ^2 := by
    dsimp [δ,Δ]
    rw [show 2*n = n*2 by omega,pow_mul,div_pow,one_pow]
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hKE,hEpower,hcost⟩ := hbudget n ((le_max_right _ _).trans hn)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have mono {u : ℝ} {F : Finset (Space 2)} (hb : NormalizedFiniteBallBound δ u K F) :
      NormalizedFiniteBallBound δ u E F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKE (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  by_cases hmSmall : m ≤ 1/δ^(s+γ)
  · have hsmall' : ((P.biUnion V).card:ℝ) ≤ E/(Δ^s)^4 :=
      hsmall.trans (small_pencil_gain_bound hδ hΔ hδeq hEpower hmSmall)
    refine hgain n ((le_max_left _ _).trans hn) s t hs hs1 hgap ht P hP hPchart
      ?_ ?_ ?_ V ?_ hsmall'
    · rw [← hδeq]
      exact hPsep
    · rw [← hδeq]
      exact mono hPball
    · exact hPcover.trans (div_le_div_of_nonneg_right hKE (by positivity))
    · intro p hp
      have hv := hV p hp
      refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le hv.1)),hv.2.2.1,?_,?_,?_⟩
      · rw [← hδeq]
        exact hv.2.2.2.1
      · rw [← hδeq]
        exact mono hv.2.2.2.2.1
      · rw [← hδeq]
        exact hv.2.2.2.2.2
  · have hlarge := large_pencil_growth (2*n) hκ hκ1 hs0 hs1 hgap hK hm
      P V hP hPchart hPball (fun p hp => by
        have hv := hV p hp
        exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,
          fun l hl => (hv.2.2.2.2.2 l hl).2⟩)
    exact large_pencil_gain_contradiction hδ hκ.le hA (zero_le_one.trans hK) hm
      hrel hcost (le_of_lt (lt_of_not_ge hmSmall)) hlarge hsmall

end Falconer

end OAI
