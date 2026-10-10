import OAI.NumberTheory.CubicMoment.Estimates.UpperTailTuple
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupingBounds
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! Actual upper-height prime boxes have a shorter group of size at least
X^(1/3-3κ). The grouping uses one surviving tuple and fixed box scales. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTuple_upper_exponents {i j N : ℕ} {ℓ : ℤ} {ξ H U X κ : ℝ}
    (hX : 1 ≤ X) (hκ : 0 < κ) (hκsmall : κ < 1/12)
    (hlog : 100/κ ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    ∀ a, 0 < largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 2/3+5*κ/2 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < Real.log X := (div_pos (by norm_num) hκ).trans_le hlog
  have hκL : 100 ≤ κ*Real.log X := by
    have hh := (div_le_iff₀ hκ).mp hlog
    nlinarith
  have hL100 : 100 ≤ Real.log X := by nlinarith
  have ht := (mul_ne_zero_iff.mp hne).1
  have hnrange := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)).trans (by norm_num)
  have hln := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hln
  have hlnpos : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  intro a
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (tailPrimeTupleNorm_rough hX hξz hq ht a).le
  rw [Real.log_rpow hXp] at hlo
  have hhi := Real.log_le_log (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (tailPrimeTupleNorm_upper hX hκ.le hξz k hhigh hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (2/3+2*κ)).ne',Real.log_rpow hXp] at hhi
  unfold largePrimeTupleExponent
  refine ⟨div_pos (lt_of_lt_of_le (mul_pos hξ hL) hlo) hlnpos,?_⟩
  apply (div_le_iff₀ hlnpos).mpr
  have hfac : 0 ≤ 2/3+5*κ/2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (show Real.log X-2 ≤
    Real.log (norm (largePrimeTupleProduct q)) by linarith) hfac
  nlinarith

theorem eventually_tailPrimeTuple_upper_grouping (i j : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12) {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ∃ s : Finset (Fin i ⊕ Fin j),
          X^(1/3-3*κ) ≤ largeTupleSubsetScale (fun a => (k a).val) s ∧
          (largeTupleSubsetScale (fun a => (k a).val) s)^2 ≤ 3*X := by
  let σ : ℝ := 1/3-5*κ/2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1/3 := by dsimp [σ]; linarith
  have hgap : 1/3-3*κ < σ := by dsimp [σ]; linarith
  have hconst : 0 < (1/2:ℝ)^σ/2^(i+j) := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (100/κ),
    eventually_rpow_le_const_mul hgap hconst]
    with X hX hlog hscale
  intro ℓ H U N k hhigh q hq hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ht := (mul_ne_zero_iff.mp hne).1
  have hw := (mul_ne_zero_iff.mp hne).2
  have hnrange := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by
    have hκL : 100 ≤ κ*Real.log X := by
      have hh := (div_le_iff₀ hκ).mp hlog
      nlinarith
    have hL100 : 100 ≤ Real.log X := by nlinarith
    have hh := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have ha := tailPrimeTuple_upper_exponents hX hκ hκsmall hlog hξ hξz k hhigh hq hne
  obtain ⟨s,_hs,hlo,hhi⟩ := prime_exponent_short_group Finset.univ
    (largePrimeTupleExponent q) hσ hσ1 (fun a _ => ⟨(ha a).1,by dsimp [σ]; linarith [(ha a).2]⟩)
    (largePrimeTupleExponent_sum hq hln.ne')
  obtain ⟨hgs,hgu⟩ := largePrimeTuplePiece_group_scale k hq hw hnp hln s hlo hhi
  refine ⟨s,?_,?_⟩
  · have hcard : s.card ≤ i+j := by
      simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using s.card_le_univ
    have hpow : (2:ℝ)^s.card ≤ 2^(i+j) := pow_le_pow_right₀ (by norm_num) hcard
    calc
      X^(1/3-3*κ) ≤ ((1/2:ℝ)^σ/2^(i+j))*X^σ := hscale
      _ = (X/2)^σ/2^(i+j) := by
        rw [div_eq_mul_inv X 2,Real.mul_rpow hXp.le (by positivity)]
        simp only [one_div]
        ring
      _ ≤ norm (largePrimeTupleProduct q)^σ/2^(i+j) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hnrange.1 hσ.le) (by positivity)
      _ ≤ norm (largePrimeTupleProduct q)^σ/2^s.card :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hnp.le _) (by positivity) hpow
      _ ≤ _ := hgs
  · have hp := pow_le_pow_left₀ (largeTupleSubsetScale_pos _ s).le hgu 2
    have he : (norm (largePrimeTupleProduct q)^(1/2:ℝ))^2 = norm (largePrimeTupleProduct q) := by
      rw [←Real.rpow_mul_natCast hnp.le]
      norm_num
    exact hp.trans (by rw [he]; exact hnrange.2)

end CubicFirstMoment

end

end OAI
