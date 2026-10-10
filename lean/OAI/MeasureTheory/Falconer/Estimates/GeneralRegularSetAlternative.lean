import OAI.MeasureTheory.Falconer.Estimates.RegularSetAlternative
import OAI.MeasureTheory.Falconer.Estimates.UniformPacketBounds

namespace OAI

/-! Remove the auxiliary fine-pencil cardinality normalization from the
regular-set alternative by selecting comparable original pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem general_regular_coarse_cover_alternative {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
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
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ (((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 ∧
          (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ K/(ρ^s)^2) := by
  obtain ⟨θ,N1,hθ,_,hN1,hmain⟩ := regular_coarse_cover_alternative hκ hκ1
  obtain ⟨ε,N2,hε,hε1,hN2,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let δ := 1/(2:ℝ)^(2*n)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  obtain ⟨_,hD80,hHD,_,_,hdepth,hDE⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδ : δ = Δ^2 := by
    dsimp [δ,Δ]
    rw [show 2*n = n*2 by omega,pow_mul,div_pow,one_pow]
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ^s = (Δ^s)^2 := by
    rw [hδ,← Real.rpow_natCast_mul hΔ.le 2 s]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*s = s*2 by ring]
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hΔ.le s 2
  have hδs2 : (δ^s)^2 = (Δ^s)^4 := by rw [hδs]; ring
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hD1 : 1 ≤ D := by change 1 ≤ K^2; exact one_le_pow₀ hK1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have powE (a : ℕ) (ha : a ≤ 40) : D^a ≤ E := (pow_le_pow_right₀ hD1 ha).trans hDE
  have hKE : K ≤ E := hKD.trans (by simpa only [pow_one] using powE 1 (by norm_num))
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  have hlog : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D := by
    have hh := (small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall.1).2.1
    have hd : 10*((n:ℝ)+2) ≤ D := by
      change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
    exact (Nat.cast_le.mpr hh).trans (by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith only [hd,this])
  have hunion : ((P.biUnion V).card:ℝ) ≤ D/(δ^s)^2 := by
    rw [hδs2]
    exact hsmall.1.trans (div_le_div_of_nonneg_right hKD (pow_nonneg (Real.rpow_nonneg hΔ.le _) _))
  have hPballδ : NormalizedFiniteBallBound δ t K P := by rw [hδ]; exact hPball
  have hVδ (p : Space 2) (hp : p ∈ P) : (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
      NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l := by
    rw [hδ]
    exact ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.2.1,
      fun l hl => ((hV p hp).2.2.2.2 l hl).2⟩
  obtain ⟨k,R,hRP,hR,_,hRball,hlo,hup,hband⟩ := uniform_packet_bounds (2*n) hκ hs0 hsone hge
    hK1 hKD hD80 hHD P V hP hPchart hPballδ hVδ hunion hlog
  have hRU : R.biUnion V ⊆ P.biUnion V := Finset.biUnion_subset_biUnion_of_subset_left V hRP
  have mono_ball {d u A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d u A F) : NormalizedFiniteBallBound d u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hRball' : NormalizedFiniteBallBound (Δ^2) t E R := by
    rw [← hδ]
    exact mono_ball hδ0.le (powE 2 (by norm_num)) hRball
  refine hmain n ((le_max_left _ _).trans hn) s t hs hs1 hgap ht R hR
    (fun p hp => hPsmall p (hRP hp)) (finiteSeparatedAt_subset hRP hPsep) hRball' ?_ V ?_ ?_
  · calc
      _ ≤ ((P.image (coarsePlanarRound ρ)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRP))
      _ ≤ K/Δ^t := hpoint
      _ ≤ _ := div_le_div_of_nonneg_right hKE (Real.rpow_nonneg hΔ.le _)
  · intro p hp
    have htube := hV p (hRP hp)
    refine ⟨htube.1,htube.2.2.1,mono_ball (sq_nonneg Δ) hKE htube.2.2.2.1,?_,?_,htube.2.2.2.2⟩
    · have hc := (hband p hp).1
      have hl : 1/(E*δ^s) ≤ (2:ℝ)^k := by
        apply le_trans _ hlo
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right (powE 2 (by norm_num)) (Real.rpow_nonneg hδ0.le _))
      rw [hδs] at hl
      exact hl.trans hc
    · have hu : 2*(2:ℝ)^k ≤ E/δ^s := by
        calc
          _ ≤ 2*(D^9/δ^s) := mul_le_mul_of_nonneg_left hup (by norm_num)
          _ ≤ D^10/δ^s := by
            rw [← mul_div_assoc]
            apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hδ0.le _)
            calc
              _ ≤ D*D^9 := mul_le_mul_of_nonneg_right (by linarith only [hD80]) (pow_nonneg hD0 _)
              _ = _ := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (powE 10 (by norm_num)) (Real.rpow_nonneg hδ0.le _)
      rw [hδs] at hu
      exact (hband p hp).2.trans hu
  · constructor
    · exact (Nat.cast_le.mpr (Finset.card_le_card hRU)).trans
        (hsmall.1.trans (div_le_div_of_nonneg_right hKE (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))
    · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRU))).trans
        (hsmall.2.trans (div_le_div_of_nonneg_right hKE (sq_nonneg _)))

end Falconer

end OAI
