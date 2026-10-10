import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeScale
import OAI.NumberTheory.CubicMoment.Estimates.SparsePieceSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeIntervals

namespace OAI

/-! The actual final-bin and two-occupancy index set in the stopping
construction has logarithmic size. No complete occupancy vector occurs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

def stoppingFactorLimit (X : ℝ) : ℕ := ⌈Real.log X/Real.log 2⌉₊

def stoppingLabelBox (ρ X : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (geometricBinCount ρ X)).product
    ((Finset.range (stoppingFactorLimit X+1)).product
      (Finset.range (stoppingFactorLimit X+1)))).filter (fun t => 1 ≤ t.2.1)

lemma stoppingFactorLimit_bound {X : ℝ} (hX : 1 ≤ X) :
    (stoppingFactorLimit X:ℝ) ≤ (Real.log 2)⁻¹*Real.log X+1 := by
  have h := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg hX) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le)).le
  simpa only [stoppingFactorLimit,div_eq_mul_inv,mul_comm] using h

lemma stopping_prime_factor_count {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {X : ℝ} (hX : 1 ≤ X) (hnX : norm n ≤ X) :
    s.card ≤ stoppingFactorLimit X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log X/Real.log 2))
  have hlarge : X < (2:ℝ)^(stoppingFactorLimit X+1) := by
    apply (Real.lt_pow_iff_log_lt hXp (by norm_num : (0:ℝ) < 2)).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    change Real.log X ≤ (stoppingFactorLimit X:ℝ)*Real.log 2 at hc
    nlinarith
  have hslt := primary_factor_subset_card_lt hn hs hsub (by norm_num : (1:ℝ) ≤ 2)
    (fun p hp => primaryPrime_norm_ge_two (primaryPrimeFactor_spec hn (hsub hp)).1)
    (hnX.trans_lt hlarge)
  omega

lemma stoppingLabelBox_card (ρ X : ℝ) :
    (stoppingLabelBox ρ X).card ≤ geometricBinCount ρ X*(stoppingFactorLimit X+1)^2 := by
  unfold stoppingLabelBox
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,pow_two] using
    (Finset.card_filter_le
      ((Finset.range (geometricBinCount ρ X)).product
        ((Finset.range (stoppingFactorLimit X+1)).product
          (Finset.range (stoppingFactorLimit X+1))))
      (fun t : ℕ × ℕ × ℕ => 1 ≤ t.2.1))

lemma stoppingLabelBox_card_logarithmic {X δ : ℝ} {J : ℕ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-(J:ℝ)) ≤ δ) :
    ((stoppingLabelBox (1+δ) X).card:ℝ) ≤
      (3*((Real.log 2)⁻¹+2)^2)*(1+Real.log X)^(J+3) := by
  have hXone : 1 ≤ X := by
    by_contra h
    have hlt := Real.log_neg hX (lt_of_not_ge h)
    linarith
  have hlog0 := Real.log_nonneg hXone
  have hfac := stoppingFactorLimit_bound hXone
  have hstep := geometricBinCount_logarithmic_width hX hL hXone
    (show X ≤ X^(1:ℝ) by rw [Real.rpow_one]) (by norm_num : (0:ℝ) ≤ 1)
    (Nat.cast_nonneg J) hδ hδone hwidth
  have hb : (geometricBinCount (1+δ) X:ℝ) ≤ 3*(1+Real.log X)^(J+1) := by
    have he : (Real.log X)^((J:ℝ)+1) = (Real.log X)^(J+1) := by
      rw [show (J:ℝ)+1 = ((J+1:ℕ):ℝ) by simp,Real.rpow_natCast]
    rw [show 2*(1:ℝ)+1 = 3 by norm_num,he] at hstep
    exact hstep.trans (by gcongr; linarith)
  have hf : ((stoppingFactorLimit X+1:ℕ):ℝ) ≤
      ((Real.log 2)⁻¹+2)*(1+Real.log X) := by
    simp only [Nat.cast_add,Nat.cast_one]
    have hlog2 : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
    nlinarith
  have hcard : ((stoppingLabelBox (1+δ) X).card:ℝ) ≤
      (geometricBinCount (1+δ) X:ℝ)*((stoppingFactorLimit X+1:ℕ):ℝ)^2 := by
    exact_mod_cast stoppingLabelBox_card (1+δ) X
  apply hcard.trans
  calc
    _ ≤ (3*(1+Real.log X)^(J+1))*
        (((Real.log 2)⁻¹+2)*(1+Real.log X))^2 := by gcongr
    _ = _ := by rw [mul_pow,show J+3 = (J+1)+2 by omega,pow_add]; ring

/-- The exact remaining-side predicate in the stopping split. -/
def stoppingRemainingTest (bin : Eisenstein → ℕ) (j l : ℕ) (e : Eisenstein) : Prop :=
  (∀ p ∈ primaryPrimeFactors e, j ≤ bin p) ∧
    (primeBin (primaryPrimeFactors e) bin j).card = l

lemma actual_stopping_label_mem_box {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) {d e r : Eisenstein} (hd : primary d) (hsd : Squarefree d)
    (he : primary e) (hse : Squarefree e) (hdX : norm d ≤ X) (heX : norm e ≤ X)
    {j k l : ℕ} (hk : 1 ≤ k) {Z : ℝ}
    (hselected : stoppingSideTest (geometricPrimeBin ρ X)
      (geometricBinLower ρ X) j k Z r d)
    (hremaining : stoppingRemainingTest (geometricPrimeBin ρ X) j l e) :
    (j,k,l) ∈ stoppingLabelBox ρ X := by
  have hcard : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ X) j).card = k :=
    hselected.2.1
  have hj : j < geometricBinCount ρ X := by
    have hn : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ X) j).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨p,hp⟩ := hn
    have hp' := Finset.mem_filter.mp hp
    have hspec := primaryPrimeFactor_spec hd hp'.1
    have hnorm := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
    simpa only [hp'.2] using geometricPrimeBin_index hρ hρ₂ hspec.1 hnorm
  have hkb : k ≤ stoppingFactorLimit X := by
    rw [←hcard]
    exact stopping_prime_factor_count hd hsd (Finset.filter_subset _ _) hX hdX
  have hlb : l ≤ stoppingFactorLimit X := by
    rw [←hremaining.2]
    exact stopping_prime_factor_count he hse (Finset.filter_subset _ _) hX heX
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkb),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hlb)⟩⟩,hk⟩

lemma stopping_scalar_norm_le_one (k l : ℕ) :
    ‖((Nat.choose (k+l) k:ℂ)⁻¹)‖ ≤ 1 := by
  have hp : 0 < Nat.choose (k+l) k := Nat.choose_pos (by omega)
  have hc : (1:ℝ) ≤ Nat.choose (k+l) k := by exact_mod_cast hp
  rw [norm_inv,Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ hc

end CubicFirstMoment

end

end OAI
