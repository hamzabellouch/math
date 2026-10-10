import OAI.MeasureTheory.Falconer.Radial.HeavyCellRegularity

namespace OAI

/-! A regular coarse cover gives heavy cells whose original fine points
remain regular in the normalized packet chart. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem heavy_regular_packet_cells {Δ ρ t K H : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ : 0 < ρ) (hδρ : Δ^2 ≤ ρ) (hρΔ : ρ ≤ Δ)
    (ht : 0 ≤ t) (ht1 : t ≤ 2) (hK : 1 ≤ K) (_hH : 0 ≤ H)
    (P : Finset (Space 2)) (hP : P.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hball : NormalizedFiniteBallBound (Δ^2) t K P)
    (hcover : ((P.image q).card:ℝ) ≤ H/Δ^t) :
    let J := Nat.log 2 P.card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      NormalizedFiniteBallBound ρ t (8*K*(J:ℝ)) C ∧
      (P.card:ℝ) ≤ (J:ℝ)*(∑ c ∈ C, ((S c).card:ℝ)) ∧
      ∀ c ∈ C, S c ⊆ P ∧ (S c).Nonempty ∧
        2^k ≤ (S c).card ∧ (S c).card < 2^(k+1) ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ ∧ |p 1-c 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t (2*K*(J:ℝ)*H)
          ((S c).image (localPacketPoint Δ (c 0) (c 1))) := by
  let J := Nat.log 2 P.card+1
  let S := fun c => P.filter fun p => q p = c
  have hJ : 0 ≤ (J:ℝ) := Nat.cast_nonneg _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hΔt : 0 < Δ^t := Real.rpow_pos_of_pos hΔ _
  obtain ⟨k,C,hCP,hC,hCball,hmass,hband⟩ := regular_coarse_cells hρ hδρ ht hK P hP q hnear hball
  have hlocal := heavy_cells_local_regular (pow_pos hΔ 2) hΔ hΔ1 hK0 hJ P C S k hball
    (fun c hc => ⟨Finset.filter_subset _ _,hband c hc⟩) hmass
  have hCsize : (C.card:ℝ) ≤ H/Δ^t :=
    (Nat.cast_le.mpr (Finset.card_le_card hCP)).trans hcover
  have hCloss : (K*(2*(J:ℝ)*(C.card:ℝ)))*Δ^t ≤ 2*K*(J:ℝ)*H := by
    have hh := (le_div_iff₀ hΔt).1 hCsize
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*K*(J:ℝ) by positivity)
    nlinarith only [hh']
  have h2 : (2:ℝ)^t ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1
      _ = 4 := by norm_num
  refine ⟨k,C,hCP,hC,?_,hmass,?_⟩
  · intro z r hr hr1
    have hr0 : 0 ≤ r := hρ.le.trans hr
    have hconstant : 2*(K*(2:ℝ)^t)*(J:ℝ) ≤ 8*K*(J:ℝ) := by
      calc
        _ ≤ 2*(K*4)*(J:ℝ) := by gcongr
        _ = _ := by ring
    exact (hCball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  · intro c hc
    refine ⟨Finset.filter_subset _ _,(hlocal c hc).1,(hband c hc).1,(hband c hc).2,?_,?_⟩
    · intro p hp
      have hh := hnear p (Finset.mem_filter.mp hp).1
      rw [(Finset.mem_filter.mp hp).2] at hh
      exact ⟨(show |p 0-c 0| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans
        (hh.trans hρΔ),
        (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans
          (hh.trans hρΔ)⟩
    · have hscale : Δ^2/Δ = Δ := by field_simp
      have hb := (hlocal c hc).2
      rw [hscale] at hb
      intro z r hr hr1
      exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCloss (Real.rpow_nonneg (hΔ.le.trans hr) _)) (Nat.cast_nonneg _))

end Falconer

end OAI
