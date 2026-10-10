import OAI.MeasureTheory.Falconer.Geometry.QuarterChartFineGain

namespace OAI

/-! Extend the checked regular gain to the full bounded point chart by
a second fixed contraction, preserving the original finite union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem bounded_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        InBoundedLineChart P →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨θ,N1,hθ,_,hN1,hgain⟩ := quarter_chart_regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,_,hbudget⟩ := chart_gain_budget hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let Δ' := 1/(2:ℝ)^(n+1)
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E := Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ' : 0 < Δ' := by dsimp [Δ']; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hEK : 400*K ≤ E := hbudget n ((le_max_right _ _).trans hn)
  have hKE : K ≤ E := (by linarith only [hK] : K ≤ 400*K).trans hEK
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have ht0 : 0 ≤ t := by linarith only [hs0,hgap,hκ]
  have h4s : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hsone
  have h4t : (4:ℝ)^t ≤ 16 := by
    calc
      _ ≤ (4:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
      _ = 16 := by norm_num
  have hKs : K*4^s ≤ E := (mul_le_mul_of_nonneg_left h4s hK.le).trans
    ((by linarith only [hK] : K*4 ≤ 400*K).trans hEK)
  have hKt : K*4^t ≤ E := (mul_le_mul_of_nonneg_left h4t hK.le).trans
    ((by linarith only [hK] : K*16 ≤ 400*K).trans hEK)
  have h25 : 25*K ≤ E := (by linarith only [hK] : 25*K ≤ 400*K).trans hEK
  have hΔeq : Δ' = Δ/2 := by dsimp [Δ',Δ]; rw [pow_succ]; ring
  have hδeq : Δ^2/4 = Δ'^2 := by rw [hΔeq]; ring
  have hρeq : 1/(2:ℝ)^((n+1)+3) = ρ/2 := by
    dsimp [ρ]
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]
    ring
  have hΔle : Δ' ≤ Δ := by rw [hΔeq]; linarith only [hΔ]
  have mono {δ u A B : ℝ} (hd : 0 ≤ δ) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound δ u A F) : NormalizedFiniteBallBound δ u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hPball' : NormalizedFiniteBallBound (Δ'^2) t E (P.image planarQuarter) := by
    rw [← hδeq]
    exact mono (by positivity) hKt (planarQuarter_regular (by positivity) ht0 hK1 P hPball)
  have hPcover' : (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤ E/Δ'^t := by
    calc
      _ ≤ 25*((P.image (coarsePlanarRound ρ)).card:ℝ) := planarQuarter_coarse_cover hρ P
      _ ≤ 25*(K/Δ^t) := mul_le_mul_of_nonneg_left hPcover (by norm_num)
      _ = (25*K)/Δ^t := by ring
      _ ≤ E/Δ'^t := by gcongr
  have hV' := quarterPencils_data (by positivity : 0 < Δ^2) hs0 hK1 P V hV
  refine hgain (n+1) (by omega) s t hs hs1 hgap ht (P.image planarQuarter) (hP.image _) ?_ ?_
    hPball' ?_ (quarterPencils V) ?_ ?_
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [planarQuarter_apply,planarQuarter_apply,abs_div,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    constructor <;> linarith only [(hPsmall p hp).1,(hPsmall p hp).2]
  · rw [← hδeq]
    exact planarQuarter_separated P hPsep
  · rw [hρeq]
    exact hPcover'
  · intro z hz
    obtain ⟨hne,hch,hsep,hball,hinc⟩ := hV' z hz
    rw [hδeq] at hsep hball hinc
    exact ⟨hne,hch,hsep,mono (by positivity) hKs hball,hinc⟩
  · rw [quarterPencils_union_card]
    exact hsmall.trans (by gcongr)

end Falconer

end OAI
