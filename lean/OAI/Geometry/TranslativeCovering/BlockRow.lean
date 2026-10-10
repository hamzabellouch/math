import OAI.Geometry.TranslativeCovering.BlockWeights

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

namespace BlockRow
open Finset BlockGeometry BlockCount BlockWeights
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma logarithmic_row {L ζ R C0 c0 q0 : ℝ}
    (hL : 0 < L) (hζ : 0 < ζ) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤ R ∧ loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (a : Finset I → I) (ha : ∀ T ∈ P.parts, a T ∈ T)
    (q : Finset I → ℝ) (hql : ∀ T ∈ P.parts, loss L d T ≤ q T)
    (S : Finset I) (hS : S ∈ P.parts) (hq : q0 ≤ q S)
    (w : Finset I → ℝ) (hw0 : ∀ T ∈ P.parts.erase S, 0 ≤ w T)
    (hw1 : ∀ T ∈ P.parts.erase S, w T ≤ 1)
    (hwt : ∀ T ∈ P.parts.erase S, w T ≤ Real.exp (-|q S-q T|/2))
    (hwa : ∀ T ∈ P.parts.erase S,
      w T ≤ C0*Real.exp ((loss L d S+loss L d T)/2-c0*d (a S) (a T)^2))
    (J : ℕ) (htail : ((P.parts.erase S).card:ℝ)*(1/2:ℝ)^J ≤ 1)
    (hcutoff : ∀ k < J,
      (8*((Real.log C0+2)/c0)+16/L)*(q S+k+1) ≤ R) :
    let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
    Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ (2*C+(1+4*C)/q0)*q S := by
  classical
  dsimp only
  let A := (Real.log C0+2)/c0
  let C := (N0:ℝ)+(2*L/ζ)*(1+8*A+16/L)
  have hA : 0 ≤ A := div_nonneg (by linarith [Real.log_nonneg hC0]) hc0.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply RowGrouping.log_row (P.parts.erase S) w hw0 hw1 hC hq0 hq J htail
  intro k hk
  let H := (P.parts.erase S).filter fun T => (1/2:ℝ)^(k+1)<w T
  let Q := q S+(k:ℝ)+1
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
  have hH : H ⊆ P.parts := fun T hT => mem_of_mem_erase (mem_filter.mp hT).1
  have hparams (T : Finset I) (hT : T ∈ H) :
      loss L d T < 2*Q ∧ d (a S) (a T)^2 ≤ A*Q := by
    obtain ⟨hTP,hbin⟩ := mem_filter.mp hT
    have hb := bin_parameters hC0 hc0 (hq0.le.trans hq) (Nat.cast_nonneg k)
      (hql S hS) (hql T (mem_of_mem_erase hTP)) (hwt T hTP) (hwa T hTP)
      ((binary_above_exp k).trans_lt hbin)
    exact ⟨hb.2.1, hb.2.2⟩
  have hcount := terminal_count hL hζ (mul_nonneg hA (by linarith))
    (show 0 ≤ 2*Q by linarith) d hn hd hs htri P hterm N0 hN02 hlog H hH a (a S)
    (fun T hT => ha T (hH hT)) (fun T hT => (hparams T hT).2)
    (fun T hT => (hparams T hT).1.le) (by
      convert hcutoff k hk using 1
      dsimp [A,Q]
      ring)
  have hN0 : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
  have hmul := mul_nonneg (div_nonneg (by positivity : (0:ℝ) ≤ 2*L) hζ.le)
    (sub_nonneg.mpr hQ)
  have hNQ := mul_nonneg hN0 (sub_nonneg.mpr hQ)
  change (H.card:ℝ) ≤ C*Q
  dsimp [C]
  have he : (2*L/ζ)*(1+8*(A*Q)+8*(2*Q)/L) =
      (2*L/ζ)*((1+8*A+16/L)*Q-(Q-1)) := by ring
  rw [he] at hcount
  nlinarith

end BlockRow

end OAI
