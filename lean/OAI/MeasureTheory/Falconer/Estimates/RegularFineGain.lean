import OAI.MeasureTheory.Falconer.Estimates.RegularRefinementPreparation
import OAI.MeasureTheory.Falconer.Estimates.RegularRefinementContradiction

namespace OAI

/-! Fine-scale growth for a regular point set. The frozen refinement and
all its numerical budgets are obtained from the original configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
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
        (∀ p ∈ P, InBoundedLineChart (V p) ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          1/(K*(Δ^s)^2) ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K/(Δ^s)^2 ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨η,N1,hη,hN1,hfalse⟩ := regular_refinement_contradiction hκ hκ1
  let β := κ/4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by dsimp [β]; linarith only [hκ1]
  let θ := η*β/80
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨ε,N2,hε,hε1,_,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let B := D^40
  let E := Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2)
  let u := s*(1-β)+2*β
  obtain ⟨hn3,hD80,hHD,_,_,hdepth,hDB⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have hD1 : 1 ≤ D := by linarith only [hD80]
  have hDB' : D ≤ B := by simpa only [pow_one] using pow_le_pow_right₀ hD1 (show 1 ≤ 40 by norm_num)
  have hKB : K ≤ B := hKD.trans hDB'
  have hB80 : 80 ≤ B := hD80.trans hDB'
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 1-β by linarith only [hβ1])
    dsimp [u,β] at hh ⊢
    nlinarith only [hh,hκ,hκ1,sq_nonneg κ]
  have hgu : κ ≤ t-u := by
    have hh := mul_nonneg hs0 hβ.le
    dsimp [u,β] at hh ⊢
    nlinarith only [hgap,hκ,hh]
  have hut : u < t := by linarith only [hgu,hκ]
  have hp : planarPotentialConstant s t ≤ B :=
    (planarPotentialConstant_gap hκ hsone (by linarith only [hgap,hκ])).trans (hHD.trans hDB')
  have hpu : planarPotentialConstant u t ≤ B :=
    (planarPotentialConstant_gap hκ hu1 hgu).trans (hHD.trans hDB')
  have hN : 0 < ((n+2:ℕ):ℝ)*Real.log 2 := mul_pos (by positivity) (Real.log_pos (by norm_num))
  have hB2 : B^2 ≤ E := by
    calc
      B^2 ≤ (Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2))^2 := pow_le_pow_left₀ (by positivity) hDB _
      _ = Real.exp (2*(θ*((n+2:ℕ):ℝ)*Real.log 2)) := (Real.exp_nat_mul _ 2).symm
      _ ≤ E := by
        apply Real.exp_le_exp.mpr
        have hh : 2*θ ≤ η := by dsimp [θ]; nlinarith only [hη,hβ1]
        nlinarith only [mul_le_mul_of_nonneg_right hh hN.le]
  have hB40 : B^40 < E^β := by
    calc
      B^40 ≤ (Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2))^40 := pow_le_pow_left₀ (by positivity) hDB _
      _ = Real.exp (40*(θ*((n+2:ℕ):ℝ)*Real.log 2)) := (Real.exp_nat_mul _ 40).symm
      _ < Real.exp ((η*((n+2:ℕ):ℝ)*Real.log 2)*β) := by
        apply Real.exp_lt_exp.mpr
        have hh : 40*θ < η*β := by dsimp [θ]; nlinarith only [mul_pos hη hβ]
        nlinarith only [mul_lt_mul_of_pos_right hh hN]
      _ = E^β := Real.exp_mul _ _
  have hdepth' : 10*((n:ℝ)+2) ≤ D := by
    change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  obtain ⟨hJp,_,hJv⟩ := small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall
  have hJpD : (Nat.log 2 P.card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJp).trans (by push_cast; linarith only [hdepth',hn0])
  have hJvD : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJv).trans (by push_cast; linarith only [hdepth',hn0])
  have hUpow : 13*(P.biUnion V).card ≤ 2^(5*n+6) := by
    have hh := small_union_card_dyadic n hε1 hsone (P.biUnion V).card hsmall
    calc
      _ ≤ 13*2^(5*n+2) := Nat.mul_le_mul_left _ hh
      _ ≤ 16*2^(5*n+2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by rw [show 5*n+6 = (5*n+2)+4 by omega,pow_add]; norm_num; ring
  have hJall : (Nat.log 2 (13*(P.biUnion V).card)+1:ℕ) ≤ D := by
    have hh := packet_log_of_card_bound hUpow
    exact (Nat.cast_le.mpr hh).trans (by push_cast; linarith only [hdepth',hn0])
  obtain ⟨F⟩ := regular_refinement_preparation n hn3 hs0 hsone ht0 ht hK1 hKD hD80 P V hP hPsmall hPball
    (fun p hp => ⟨(div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hKD (sq_nonneg _))).trans (hV p hp).2.2.2.1,
      (hV p hp).2.2.2.2.1.trans (div_le_div_of_nonneg_right hKD (sq_nonneg _)),
      (hV p hp).2.2.1,(hV p hp).2.2.2.2.2⟩) hJpD hJvD hJall hpoint
  have hPballB : NormalizedFiniteBallBound (Δ^2) t B P := by
    intro z r hr hr1
    exact (hPball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg ((sq_nonneg Δ).trans hr) _))
      (Nat.cast_nonneg _))
  exact hfalse n ((le_max_left _ _).trans hn) hn3 s t u β B hs hs1 hgap ht
    hu0 hut hβ hβ1 rfl hB80 hB2 hB40 hp hpu P hP hPsmall hPsep hPballB
    (hpoint.trans (div_le_div_of_nonneg_right hKB (Real.rpow_nonneg hΔ.le _))) V
    (fun p hp => ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.2.2.2⟩) F
    (hsmall.trans (div_le_div_of_nonneg_right hKB (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))

end Falconer

end OAI
