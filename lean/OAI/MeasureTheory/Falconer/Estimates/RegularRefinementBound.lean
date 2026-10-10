import OAI.MeasureTheory.Falconer.Estimates.RegularScaleCoefficients
import OAI.MeasureTheory.Falconer.Estimates.PacketScaleCombination

namespace OAI

/-! A frozen regular refinement with a small fine union cannot have a large
coarse union. This combines the actual local and coarse incidence estimates. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_refinement_coarse_bound (N k : ℕ) {s t u β D m : ℝ}
    (hN : 3 ≤ N) (hD : 80 ≤ D) (hm : 0 < m)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hst : s < t) (hu : 0 ≤ u) (hut : u < t)
    (hβ : 0 < β) (hβ1 : β < 1) (huEq : u = s*(1-β)+2*β)
    (hp : planarPotentialConstant s t ≤ D) (hpu : planarPotentialConstant u t ≤ D)
    (C P U₀ : Finset (Space 2)) (T V G : Space 2 → Finset (Space 2))
    (c : Space 2) (hc : c ∈ C) (hP : P.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t D C)
    (hT : ∀ x ∈ C, m/D ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ D*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s D (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hcell : ∀ p ∈ P, |p 0-c 0| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t D
      (P.image (localPacketPoint (1/(2:ℝ)^N) (c 0) (c 1))))
    (hV : ∀ p ∈ P, 1/(D*((1/(2:ℝ)^N)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s D (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l)
    (hcover : ∀ p ∈ P, ∀ l ∈ V p, ∃ a ∈ T c, l ∈ G a)
    (hband : ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1))
    (htotal : (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*(U₀.card:ℝ))
    (hsmall : (U₀.card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^4) :
    (((C.biUnion T).card:ℝ)*((1/(2:ℝ)^(N+3))^s)^2)^β ≤ D^37 := by
  let Δ := 1/(2:ℝ)^N
  let ρ := 1/(2:ℝ)^(N+3)
  let A : ℝ := (C.biUnion T).card
  let a := A*(ρ^s)^2
  let x := m*ρ^s
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hρΔ : ρ ≤ Δ := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpot := planarPotentialConstant_pos hst
  have hpotu := planarPotentialConstant_pos hut
  have hbandR : ∀ b ∈ C.biUnion T, (2:ℝ)^k ≤ ((G b).card:ℝ) ∧
      ((G b).card:ℝ) ≤ 2*(2:ℝ)^k := by
    intro b hb
    constructor
    · exact_mod_cast (hband b hb).1
    · have hh : ((G b).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband b hb).2
      simpa only [pow_succ,mul_comm] using hh.le
  have hlocal := local_cell_packet_scale_combination N hN hs hst hD1
    (by positivity : 0 ≤ 1/(D*(Δ^s)^2)) (mul_pos hD0 hm).le
    (by positivity : 0 ≤ (2:ℝ)^k) (hCchart c hc).1 P (C.biUnion T) (T c) U₀ V G hP
    hcell hPball hV (Finset.subset_biUnion_of_mem T hc) (hT c hc).2.1 hcover hbandR htotal
  have hlocal' : a ≤ D^13*x := by
    exact regular_local_ratio_bound hD hΔ hρ hρΔ hs hs1 hpot.le hp
      (Nat.cast_nonneg _) hm.le hsmall (by
        convert hlocal using 1
        simp only [Δ]
        ring)
  have hθ : 0 < 1-β := sub_pos.mpr hβ1
  have hθ1 : 1-β < 1 := by linarith only [hβ]
  have he : s*(1-β)+2*(1-(1-β)) = u := by rw [huEq]; ring
  have hcoarse := planar_interpolated_incidence (N+3) hs hu hut hD1
    (div_pos hm hD0).le hθ hθ1 he C T ⟨c,hc⟩ hCchart hCball hT
  rw [show 1-(1-β) = β by ring] at hcoarse
  have hnorm := normalize_interpolated_incidence hρ hD0 hm hD0.le hD0.le hcoarse
  have hcoef := regular_coarse_coefficient_bound hD hs hs1 hpotu.le hpu hβ.le hβ1.le
  have hcoarse' : x^2 ≤ D^11*a*x^(1-β) := by
    have heq : D*D*80^s = D^2*80^s := by ring
    rw [heq] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by positivity))
      (by positivity))
  have hh := two_scale_ratio_bound (by positivity) (by positivity)
    (pow_nonneg hD0.le 11) (one_le_pow₀ hD1 (n := 13)) hβ hβ1.le hcoarse' hlocal'
  calc
    a^β ≤ D^11*(D^13)^2 := hh
    _ = D^37 := by ring

end Falconer

end OAI
