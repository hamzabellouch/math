import OAI.Geometry.TranslativeCovering.BlockGeometry

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockCount
open Finset Filter BlockGeometry
open scoped Topology
variable {I : Type u_1} [DecidableEq I] [Fintype I]

omit [DecidableEq I] [Fintype I] in
lemma log_absorption {L ζ : ℝ} (hL : 0 < L) (hζ : 0 < ζ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2 := by
  have hlim : Tendsto (fun N : ℕ => Real.log N / N) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := hlim.eventually_lt_const (div_pos hζ (by positivity : (0:ℝ)<2*L))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hev
  refine ⟨max N0 2, le_max_right _ _, ?_⟩
  intro N hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hh := hN0 N (le_trans (le_max_left _ _) hN)
  have hh' := (div_lt_iff₀ hn).mp hh
  have he : L * (ζ/(2*L)*(N:ℝ)) = ζ*N/2 := by field_simp
  rw [← he]
  exact (mul_le_mul_of_nonneg_left hh'.le hL.le)

lemma subfamily_card_union (P : Finpartition (univ : Finset I))
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) : H.card ≤ (H.biUnion id).card := by
  apply card_le_card_biUnion
  · intro S hS T hT hST
    exact P.disjoint (hH hS) (hH hT) hST
  · intro S hS
    exact P.nonempty_of_mem_parts (hH hS)

lemma terminal_count {L ζ R t u : ℝ} (hL : 0 < L) (hζ : 0 < ζ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) (a : Finset I → I) (z : I)
    (ha : ∀ S ∈ H, a S ∈ S)
    (hc : ∀ S ∈ H, d z (a S)^2 ≤ t)
    (hloss : ∀ S ∈ H, loss L d S ≤ u)
    (hR : 8*t+8*u/L ≤ R) :
    (H.card : ℝ) < N0 + (2*L/ζ)*(1+8*t+8*u/L) := by
  by_cases hsmall : H.card < N0
  · have hnonneg : 0 ≤ (2*L/ζ)*(1+8*t+8*u/L) := by positivity
    have hcast : (H.card:ℝ)<N0 := by exact_mod_cast hsmall
    linarith
  · have hN0H : N0 ≤ H.card := by omega
    by_contra! hbig
    have hH2 : 2 ≤ H.card := hN02.trans hN0H
    have hHne : H.Nonempty := card_pos.mp (by omega)
    have hrad := nearby_union_radius hL ht hu d hn hd hs htri H hHne a z ha hc hloss
    have hcard := subfamily_card_union P H hH
    have hN0W := hN0H.trans hcard
    have hlogW := hlog _ hN0W
    have hNc : (H.card:ℝ) ≤ (H.biUnion id).card := by exact_mod_cast hcard
    have hN0nonneg : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
    have hlarge : (2*L/ζ)*(1+8*t+8*u/L) ≤ (H.biUnion id).card := by linarith
    have hm : L*(1+8*t+8*u/L) ≤ ζ*(H.biUnion id).card/2 := by
      have hmul := mul_le_mul_of_nonneg_left hlarge hζ.le
      have he : ζ*((2*L/ζ)*(1+8*t+8*u/L)) = 2*(L*(1+8*t+8*u/L)) := by
        field_simp
      rw [he] at hmul
      linarith
    apply hterm H hH hH2
    refine ⟨hrad.trans hR, ?_⟩
    rw [loss, ite_eq_right (by omega)]
    have hrm := mul_le_mul_of_nonneg_left hrad hL.le
    nlinarith

end BlockCount

end OAI
