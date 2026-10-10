import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughSupport
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingLogBoundary

namespace OAI

/-! Actual selected-side size bounds. A nonzero cutoff bounds the final
selected prime, while the stopping inequalities and geometric distortion
bound the complete coefficient scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_norm_lt {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0) {w : ℝ} (hw : 0 < w)
    {d p : Eisenstein} (hp : p ∈ primaryPrimeFactors d)
    (hne : cutoffMoebius ψ w d ≠ 0) : norm p < 2*w := by
  have hprod := (mul_ne_zero_iff.mp hne).2
  change (∏ p ∈ primaryPrimeFactors d, (ψ (norm p/w):ℂ)) ≠ 0 at hprod
  have hterm := (Finset.prod_ne_zero_iff.mp hprod) p hp
  by_contra h
  have hx : 2 ≤ norm p/w := (le_div_iff₀ hw).mpr (by linarith)
  apply hterm
  simp only [hψ (norm p/w) hx,Complex.ofReal_zero]

lemma geometric_selected_norm_distortion {ρ X ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    {d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X) :
    norm d ≤ X^ε * primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  let s := primaryPrimeFactors d
  have hcell (p : Eisenstein) (hp : p ∈ s) :
      0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) ∧
        geometricBinLower ρ X (geometricPrimeBin ρ X p) ≤ norm p ∧
          norm p ≤ ρ*geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
    have hspec := primaryPrimeFactor_spec hd hp
    have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
    exact ⟨pow_nonneg (zero_lt_one.trans hρ).le _,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).2.le⟩
  have hnorm := (primeSurrogate_norm_bounds s (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) (zero_lt_one.trans hρ).le hcell).2
  have hprod : (∏ p ∈ s, p) = d := primaryPrimeFactors_prod hd hs
  rw [hprod] at hnorm
  have hcount : (2:ℝ)^s.card ≤ X :=
    (primary_prime_subset_two_pow_le hd hs (Finset.Subset.refl _)).trans hdX
  have hpower : ρ^s.card ≤ X^ε := by
    calc
      _ ≤ ((2:ℝ)^ε)^s.card := pow_le_pow_left₀ (zero_lt_one.trans hρ).le hsmall _
      _ = ((2:ℝ)^s.card)^ε := by
        rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_natCast_mul (by norm_num),mul_comm]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hcount hε
  exact hnorm.trans (mul_le_mul_of_nonneg_right hpower
    (Finset.prod_nonneg (fun p _ => pow_nonneg (zero_lt_one.trans hρ).le _)))

theorem stoppingSideTest_norm_bounds {ρ X Z w ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hZ : 0 < Z) (hw : 0 < w) {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {r d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hstop : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hne : cutoffMoebius ψ w d ≠ 0) :
    Z ≤ norm (r*d) ∧ norm (r*d) ≤ 2*X^ε*w*Z := by
  have hX : 0 ≤ X := (norm_nonneg d).trans hdX
  have hbin : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ X) j).Nonempty :=
    Finset.card_pos.mp (by rw [hstop.2.1]; omega)
  obtain ⟨p,hp⟩ := hbin
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hspec := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
  have hell : geometricBinLower ρ X j < 2*w := by
    have hlower := (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1
    rw [hpj] at hlower
    exact hlower.trans_lt (cutoffMoebius_prime_norm_lt hψ hw hpd hne)
  have hellp : 0 < geometricBinLower ρ X j := pow_pos (zero_lt_one.trans hρ) _
  have hbefore := (div_lt_iff₀ hellp).mp hstop.2.2.1
  have hsur : primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) ≤ norm d := by
    calc
      _ ≤ ∏ p ∈ primaryPrimeFactors d, norm p := by
        apply Finset.prod_le_prod₀
        · intro p _hp
          exact pow_nonneg (zero_lt_one.trans hρ).le _
        · intro p hp
          have hpp := primaryPrimeFactor_spec hd hp
          exact (geometricPrimeBin_cell hρ hρ₂ hpp.1
            ((norm_le_of_dvd (primary_ne_zero hd) hpp.2).trans hdX)).1
      _ = norm (∏ p ∈ primaryPrimeFactors d, p) := (norm_finset_prod _ _).symm
      _ = norm d := by rw [primaryPrimeFactors_prod hd hs]
  rw [norm_mul_eq]
  refine ⟨hstop.2.2.2.trans (mul_le_mul_of_nonneg_left hsur (norm_nonneg r)),?_⟩
  calc
    _ ≤ norm r*(X^ε * primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) :=
      mul_le_mul_of_nonneg_left (geometric_selected_norm_distortion hρ hρ₂ hε hsmall hd hs hdX)
        (norm_nonneg r)
    _ = X^ε*(norm r*primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) := by ring
    _ ≤ X^ε*(Z*geometricBinLower ρ X j) :=
      mul_le_mul_of_nonneg_left hbefore.le (Real.rpow_nonneg hX _)
    _ ≤ X^ε*(Z*(2*w)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hell.le hZ.le) (Real.rpow_nonneg hX _)
    _ = _ := by ring

theorem stoppedBeta_norm_bounds (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {ρ X Z Q w ε : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hZ : 0 < Z) (hw : 0 < w)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool) {b : Eisenstein}
    (hs : Squarefree b)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h Z Q early) b ≠ 0) :
    Z ≤ norm b ∧ norm b ≤ 2*X^ε*w*Z := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early p.1 p.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hcut := (mul_ne_zero_iff.mp hterm).2
  have hsq : Squarefree (p.1*p.2) := by rwa [hprod]
  have hh := stoppingSideTest_norm_bounds hρ hρ₂ hε hsmall hZ hw hψ
    (hD p.2 hd).1 hsq.of_mul_right (hD p.2 hd).2 hk hsel.1 hcut
  rwa [hprod] at hh

theorem eventually_two_stage_stopped_dyad_range {ξ ε : ℝ}
    (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (b Z N : ℝ),
      (Z = X^(36/100:ℝ) ∨ Z = X^(38/100:ℝ)) →
      Z ≤ N → N ≤ 2*X^ε*X^ξ*Z → b/2 ≤ N → N ≤ b →
      X^(35/100:ℝ) ≤ b ∧ b ≤ X^(39/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show ε+ξ+38/100 < (39/100:ℝ) by linarith) 4]
    with X hX hlarge
  intro b Z N hZ hZN hN hbN hNb
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hZlo : X^(35/100:ℝ) ≤ Z := by
    rcases hZ with rfl | rfl
    all_goals exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hZhi : Z ≤ X^(38/100:ℝ) := by
    rcases hZ with rfl | rfl
    · exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    · exact le_rfl
  refine ⟨hZlo.trans (hZN.trans hNb),?_⟩
  have hh : 2*N ≤ X^(39/100:ℝ) := by
    calc
      2*N ≤ 4*X^ε*X^ξ*Z := by linarith
      _ ≤ 4*X^ε*X^ξ*X^(38/100:ℝ) :=
        mul_le_mul_of_nonneg_left hZhi (by positivity)
      _ = 4*X^(ε+ξ+38/100:ℝ) := by
        rw [mul_assoc (4:ℝ) (X^ε) (X^ξ),←Real.rpow_add hXp,
          mul_assoc (4:ℝ),←Real.rpow_add hXp]
      _ ≤ _ := hlarge
  linarith

/-- A fixed ambient dilation has the same strict selected-scale range.
The cutoff parameter remains X^ξ while the geometric distortion is
measured on the actual ambient envelope C*X. -/
theorem eventually_two_stage_stopped_dyad_range_dilation {ξ ε C : ℝ}
    (hC : 0 < C) (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (b Z N : ℝ),
      (Z = X^(36/100:ℝ) ∨ Z = X^(38/100:ℝ)) →
      Z ≤ N → N ≤ 2*(C*X)^ε*X^ξ*Z → b/2 ≤ N → N ≤ b →
      X^(35/100:ℝ) ≤ b ∧ b ≤ X^(39/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show ε+ξ+38/100 < (39/100:ℝ) by linarith)
      (4*C^ε)] with X hX hlarge
  intro b Z N hZ hZN hN hbN hNb
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hZlo : X^(35/100:ℝ) ≤ Z := by
    rcases hZ with rfl | rfl
    all_goals exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hZhi : Z ≤ X^(38/100:ℝ) := by
    rcases hZ with rfl | rfl
    · exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    · exact le_rfl
  refine ⟨hZlo.trans (hZN.trans hNb),?_⟩
  have hh : 2*N ≤ X^(39/100:ℝ) := by
    calc
      2*N ≤ 4*(C*X)^ε*X^ξ*Z := by linarith
      _ ≤ 4*(C*X)^ε*X^ξ*X^(38/100:ℝ) :=
        mul_le_mul_of_nonneg_left hZhi (by positivity)
      _ = (4*C^ε)*X^(ε+ξ+38/100:ℝ) := by
        rw [Real.mul_rpow hC.le hXp.le,
          Real.rpow_add hXp,Real.rpow_add hXp]
        ring
      _ ≤ _ := hlarge
  linarith

end CubicFirstMoment

end

end OAI
