import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordFinite
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceWord
open Filter InitialCharacterScale Construction Preliminaries

private theorem pow_lower {δ : ℝ} (hδ : 0<δ) {m : ℕ} (hm : 1  ≤  m) :
    Real.exp (-(2*|Real.log δ|)*(m:ℝ)) ≤ δ^(m+1) := by
  have hm' : (1:ℝ) ≤  m := by exact_mod_cast hm
  have hb : -|Real.log δ|  ≤ Real.log δ := neg_abs_le _
  have hp : (m:ℝ)+1 ≤ 2*m := by linarith
  have he : -(2*|Real.log δ|)*(m:ℝ) ≤ ((m:ℝ)+1)*Real.log δ := by
    nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ (m:ℝ)+1 by positivity),
      mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.log δ))]
  calc
    _ ≤ Real.exp (((m:ℝ)+1)*Real.log δ) := Real.exp_le_exp.mpr he
    _=δ^(m+1) := by rw [←Nat.cast_add_one,Real.exp_nat_mul,Real.exp_log hδ]

theorem absorb_bin_losses {m : ℕ} (hm : 1  ≤  m) {β δ X N A B v : ℝ}
    (hδ : 0<δ) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hN : N ≤ Real.exp ((2*|β| +1)*(m:ℝ)))
    (hA : Real.sqrt X*Real.exp (-(6*|β| +1)*(m:ℝ)) ≤ A)
    (hAB : A ≤ N*B) (hbin : δ^(m+1) ≤ N*v) :
    Real.sqrt X*Real.exp (-selectionCost β δ*(m:ℝ)) ≤ B ∧
    Real.exp (-selectionCost β δ*(m:ℝ)) ≤ v := by
  have hb : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hCB : 6*|β| +1+(2*|β| +1) ≤ selectionCost β δ := by
    unfold selectionCost
    nlinarith [abs_nonneg β,abs_nonneg (Real.log δ)]
  have hCv : 2*|Real.log δ| +(2*|β| +1) ≤ selectionCost β δ := by
    unfold selectionCost
    nlinarith [abs_nonneg β,abs_nonneg (Real.log δ)]
  have hAB' := hA.trans (hAB.trans (mul_le_mul_of_nonneg_right hN hB))
  have hv' := (pow_lower hδ hm).trans (hbin.trans (mul_le_mul_of_nonneg_right hN hv))
  have hcB := mul_le_mul_of_nonneg_left hAB' (Real.exp_pos (-((2*|β| +1)*(m:ℝ)))).le
  have hcv := mul_le_mul_of_nonneg_left hv' (Real.exp_pos (-((2*|β| +1)*(m:ℝ)))).le
  have hexp : Real.exp (-((2*|β| +1)*(m:ℝ)))*Real.exp ((2*|β| +1)*(m:ℝ))=1 := by
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  simp only [←mul_assoc,hexp,one_mul] at hcB hcv
  constructor
  · calc
      _ ≤ Real.sqrt X*Real.exp (-((6*|β| +1+(2*|β| +1))*(m:ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.sqrt_nonneg _)
      _=Real.exp (-((2*|β| +1)*(m:ℝ)))*
          (Real.sqrt X*Real.exp (-(6*|β| +1)*(m:ℝ))) := by
        rw [mul_left_comm,←Real.exp_add]
        congr 2; ring
      _ ≤ B := by simpa only [mul_assoc] using hcB
  · calc
      _ ≤ Real.exp (-((2*|Real.log δ| +(2*|β| +1))*(m:ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _=Real.exp (-((2*|β| +1)*(m:ℝ)))*Real.exp (-(2*|Real.log δ|)*(m:ℝ)) := by
        rw [←Real.exp_add]; congr 1; ring
      _ ≤ v := hcv

theorem source_word_eventually (k : ℕ) {α γ δ cA : ℝ} (β : ℝ)
    (hα : 0<α) (hγ : 0<γ) (hδ : 0<δ) (hcA : 0<cA) :
    ∀ᶠ L : ℝ in atTop,∀u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      ∀{Q : ℕ} (bulk top : FinitePrior (PrimeUpTo Q))
        (f : PrimeUpTo Q → ℤ → ℂ) (H : Finset ℤ),
      (∀p,bulk.mass p≠0 → Real.log (p.val:ℝ) ≤ Real.exp (u-γ*L)) →
      (∀p,top.mass p≠0 → Real.exp u ≤ Real.log (p.val:ℝ) ∧
        Real.log (p.val:ℝ) ≤ Real.exp 1*Real.exp u) →
      (∀n∈H,δ ≤ (bulk.cmean (fun p=>f p n)).re ∧ δ ≤ (top.cmean (fun p=>f p n)).re) →
      cA*Real.sqrt (higherSourceX k u:ℝ)/(Real.log (higherSourceX k u:ℝ))^3 ≤ (H.card:ℝ) →
      ∃J : ℤ,∃H₀ : Finset ℤ,H₀⊆H ∧
        (9/10:ℝ)*Real.exp u ≤ (J:ℝ) ∧ (J:ℝ) ≤ 4*Real.exp u ∧
        Real.sqrt (higherSourceX k u:ℝ)*
          Real.exp (-selectionCost β δ*(wordSize k L:ℝ)) ≤ (H₀.card:ℝ) ∧
        ∀n∈H₀,Real.exp (-selectionCost β δ*(wordSize k L:ℝ)) ≤ 
          ‖binMean bulk top (wordSize k L) f J n‖ := by
  have ha : Tendsto (fun L : ℝ=>α*L-1) atTop atTop := by
    simpa only [id_eq,sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop hα).atTop_add (tendsto_const_nhds (x:=(-1:ℝ)))
  filter_upwards [bin_scale_eventually k β hα hγ,typical_cost_eventually k β hcA,
    ha.eventually_ge_atTop 0] with L hscale hcost hzero
  intro u hu hU Q bulk top f H hbulk htop hmean hH
  have hs := hscale u hu hU
  have hc := (hcost u (hzero.trans hu) hU).trans hH
  obtain ⟨J,hJ,H₀,hsub,hcard,hgood⟩ := common_bin bulk top (Real.exp_pos u).le hδ.le
    hbulk htop hs.2.2.1 f H hmean
  have hcard' : (H.card:ℝ) ≤ ((bins (Real.exp u)).card:ℝ)*(H₀.card:ℝ) := by exact_mod_cast hcard
  have hloc := bins_location hs.2.1 hJ
  have hh (n : ℤ) (hn : n∈H₀) := absorb_bin_losses hs.1 hδ (Nat.cast_nonneg H₀.card)
    (norm_nonneg (binMean bulk top (wordSize k L) f J n)) hs.2.2.2 hc hcard' (hgood n hn)
  have hmass : Real.sqrt (higherSourceX k u:ℝ)*
      Real.exp (-selectionCost β δ*(wordSize k L:ℝ)) ≤ (H₀.card:ℝ) := by
    have hdummy : δ^(wordSize k L+1) ≤ ((bins (Real.exp u)).card:ℝ)*
        (δ^(wordSize k L+1)/((bins (Real.exp u)).card:ℝ)) := by
      have hpos : 0<((bins (Real.exp u)).card:ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨J,hJ⟩
      rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
    exact (absorb_bin_losses hs.1 hδ (Nat.cast_nonneg H₀.card) (by positivity)
      hs.2.2.2 hc hcard' hdummy).1
  exact ⟨J,H₀,hsub,hloc.1,hloc.2,hmass,fun n hn=>(hh n hn).2⟩

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
