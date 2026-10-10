import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingSplit
import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins

namespace OAI

/-! Uniqueness of the actual first crossing bin and the selected count.
This supplies the missing uniqueness direction for the finite stop sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

lemma crossing_index_unique (f : ℕ → ℝ) (hf : Monotone f) {Z : ℝ} {j k : ℕ}
    (hj : f j < Z ∧ Z ≤ f (j+1)) (hk : f k < Z ∧ Z ≤ f (k+1)) : j = k := by
  apply le_antisymm
  · by_contra h
    have hkj : k+1 ≤ j := by omega
    exact (not_lt_of_ge (hk.2.trans (hf hkj))) hj.1
  · by_contra h
    have hjk : j+1 ≤ k := by omega
    exact (not_lt_of_ge (hj.2.trans (hf hjk))) hk.1

lemma bin_count_predecessor {R ell : ℝ} (hell : ell ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    R*ell^k/ell = R*ell^(k-1) := by
  have he : k = (k-1)+1 := by omega
  conv_lhs => rw [he,pow_succ]
  rw [←mul_assoc,mul_div_cancel_right₀ _ hell]

lemma first_bin_count_unique {R ell Z : ℝ} (hR : 0 ≤ R) (hell : 1 ≤ ell)
    {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hjl : R*ell^j/ell < Z) (hju : Z ≤ R*ell^j)
    (hkl : R*ell^k/ell < Z) (hku : Z ≤ R*ell^k) : j = k := by
  have hell0 : ell ≠ 0 := ne_of_gt (zero_lt_one.trans_le hell)
  have hmono : Monotone (fun n : ℕ => R*ell^n) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hell hab) hR
  have hj' : R*ell^(j-1) < Z ∧ Z ≤ R*ell^((j-1)+1) := by
    rw [Nat.sub_add_cancel hj]
    exact ⟨by rwa [bin_count_predecessor hell0 hj] at hjl,hju⟩
  have hk' : R*ell^(k-1) < Z ∧ Z ≤ R*ell^((k-1)+1) := by
    rw [Nat.sub_add_cancel hk]
    exact ⟨by rwa [bin_count_predecessor hell0 hk] at hkl,hku⟩
  have h := crossing_index_unique _ hmono hj' hk'
  omega

lemma partial_count_bin_crossing {R ell Z : ℝ} (hR : 0 ≤ R) (hell : 1 ≤ ell)
    {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    (hprev : R*ell^k/ell < Z) (hhit : Z ≤ R*ell^k) :
    R < Z ∧ Z ≤ R*ell^N := by
  have hellp : 0 < ell := zero_lt_one.trans_le hell
  have hpow : ell ≤ ell^k := by simpa using pow_le_pow_right₀ hell hk
  have hlo : R ≤ R*ell^k/ell := (le_div_iff₀ hellp).mpr
    (mul_le_mul_of_nonneg_left hpow hR)
  exact ⟨hlo.trans_lt hprev,hhit.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hell hkN) hR)⟩

lemma prime_prefix_monotone (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j) {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun j => R*primeSurrogate (primeBinPrefix s bin j) bin ell) := by
  apply monotone_nat_of_le_succ
  intro j
  have hp : 0 ≤ primeSurrogate (primeBinPrefix s bin j) bin ell :=
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p)))
  have hpow : 1 ≤ (ell j)^(primeBin s bin j).card := one_le_pow₀ (hell j)
  rw [primeSurrogate_prefix_succ]
  calc
    _ ≤ (R*primeSurrogate (primeBinPrefix s bin j) bin ell)*
        (ell j)^(primeBin s bin j).card := le_mul_of_one_le_right (mul_nonneg hR hp) hpow
    _ = _ := by ring

lemma selected_crossing_implies_bin_crossing (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j k : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    R*primeSurrogate (primeBinPrefix s bin j) bin ell < Z ∧
      Z ≤ R*primeSurrogate (primeBinPrefix s bin (j+1)) bin ell := by
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  have hbase : 0 ≤ R*primeSurrogate (primeBinPrefix s bin j) bin ell :=
    mul_nonneg hR (Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p))))
  have hp : R*primeSurrogate (stoppingSelected s bin j t) bin ell =
      (R*primeSurrogate (primeBinPrefix s bin j) bin ell)*(ell j)^k := by
    rw [stoppingSelected_surrogate ell hsub,hcard]
    ring
  rw [hp] at hprev hhit
  have hkN : k ≤ (primeBin s bin j).card := by
    rw [←hcard]
    exact Finset.card_le_card hsub
  have hcross := partial_count_bin_crossing hbase (hell j) hk hkN hprev hhit
  refine ⟨hcross.1,?_⟩
  simpa only [primeSurrogate_prefix_succ,mul_assoc] using hcross.2

lemma selected_crossing_bin_unique (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j₀ j k₀ k : ℕ} {t₀ t : Finset Eisenstein}
    (ht₀ : t₀ ∈ (primeBin s bin j₀).powersetCard k₀) (hk₀ : 1 ≤ k₀)
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hc₀ : R*primeSurrogate (stoppingSelected s bin j₀ t₀) bin ell/ell j₀ < Z ∧
      Z ≤ R*primeSurrogate (stoppingSelected s bin j₀ t₀) bin ell)
    (hc : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
      Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) : j = j₀ := by
  exact crossing_index_unique _ (prime_prefix_monotone s bin ell hell hR)
    (selected_crossing_implies_bin_crossing s bin ell hell hR ht hk hc.1 hc.2)
    (selected_crossing_implies_bin_crossing s bin ell hell hR ht₀ hk₀ hc₀.1 hc₀.2)

lemma selected_crossing_indices_unique (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j₀ k₀ j k : ℕ}
    (hk₀ : 1 ≤ k₀) (hk₀N : k₀ ≤ (primeBin s bin j₀).card)
    (hprev₀ : (R*primeSurrogate (primeBinPrefix s bin j₀) bin ell)*ell j₀^k₀/ell j₀ < Z)
    (hhit₀ : Z ≤ (R*primeSurrogate (primeBinPrefix s bin j₀) bin ell)*ell j₀^k₀)
    {t : Finset Eisenstein} (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    j = j₀ ∧ k = k₀ := by
  have hbase (i : ℕ) : 0 ≤ R*primeSurrogate (primeBinPrefix s bin i) bin ell :=
    mul_nonneg hR (Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p))))
  have hcross₀ := partial_count_bin_crossing (hbase j₀) (hell j₀) hk₀ hk₀N hprev₀ hhit₀
  have hwhole₀ : R*primeSurrogate (primeBinPrefix s bin j₀) bin ell < Z ∧
      Z ≤ R*primeSurrogate (primeBinPrefix s bin (j₀+1)) bin ell := by
    refine ⟨hcross₀.1,?_⟩
    simpa only [primeSurrogate_prefix_succ,mul_assoc] using hcross₀.2
  have hj := crossing_index_unique _ (prime_prefix_monotone s bin ell hell hR)
    (selected_crossing_implies_bin_crossing s bin ell hell hR ht hk hprev hhit) hwhole₀
  refine ⟨hj,?_⟩
  subst j
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  rw [stoppingSelected_surrogate ell hsub,hcard] at hprev hhit
  rw [←mul_assoc] at hprev hhit
  exact first_bin_count_unique (hbase j₀) (hell j₀) hk hk₀ hprev hhit hprev₀ hhit₀

/-- Every original term is restored by summing the actual possible last
bin and selected count. Uniqueness makes all other labels vanish. -/
theorem prime_bin_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {m : ℕ} (hbin : ∀ p ∈ s, bin p < m) (hell : ∀ j, 1 ≤ ell j)
    (hell' : ∀ j < m, 1 < ell j) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s bin ell) (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card,
      ∑ t ∈ (primeBin s bin j).powersetCard k,
        if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
          ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  obtain ⟨j₀,hj₀,k₀,hk₀,hk₀N,hprev₀,hhit₀⟩ := first_prime_bin s bin ell hbin
    hell' hR hstart hend
  let F := fun j k => ∑ t ∈ (primeBin s bin j).powersetCard k,
    if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
      ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
        (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
         cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
    else 0
  have hmemj : j₀ ∈ Finset.range m := Finset.mem_range.mpr hj₀
  have hmemk : k₀ ∈ Finset.Icc 1 s.card := Finset.mem_Icc.mpr
    ⟨hk₀,hk₀N.trans (Finset.card_filter_le _ _)⟩
  have hindices {j k : ℕ} {t : Finset Eisenstein}
      (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
      (hc : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
      j = j₀ ∧ k = k₀ :=
    selected_crossing_indices_unique s bin ell hell hR.le
      hk₀ hk₀N hprev₀ hhit₀ ht hk hc.1 hc.2
  have houter : (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card, F j k) =
      ∑ k ∈ Finset.Icc 1 s.card, F j₀ k := by
    apply Finset.sum_eq_single j₀
    · intro j _hj hjne
      apply Finset.sum_eq_zero
      intro k hk
      dsimp only [F]
      apply Finset.sum_eq_zero
      intro t ht
      apply ite_eq_right
      intro hc
      exact hjne (hindices ht (Finset.mem_Icc.mp hk).1 hc).1
    · exact fun h => (h hmemj).elim
  have hinner : (∑ k ∈ Finset.Icc 1 s.card, F j₀ k) = F j₀ k₀ := by
    apply Finset.sum_eq_single k₀
    · intro k hk hkne
      dsimp only [F]
      apply Finset.sum_eq_zero
      intro t ht
      apply ite_eq_right
      intro hc
      exact hkne (hindices ht (Finset.mem_Icc.mp hk).1 hc).2
    · exact fun h => (h hmemk).elim
  change (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card, F j k) = _
  rw [houter,hinner]
  calc
    F j₀ k₀ = ∑ _t ∈ (primeBin s bin j₀).powersetCard k₀,
        ((primeBin s bin j₀).card.choose k₀:ℂ)⁻¹*cutoffMoebius ψ w (∏ p ∈ s, p) := by
      dsimp only [F]
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
      have hc : R*primeSurrogate (stoppingSelected s bin j₀ t) bin ell/ell j₀ < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s bin j₀ t) bin ell := by
        rw [stoppingSelected_surrogate ell hsub,hcard,←mul_assoc]
        exact ⟨hprev₀,hhit₀⟩
      rw [ite_eq_left hc,cutoffMoebius_stoppingSelected ψ w hs hsub]
    _ = _ := by
      rw [←Finset.sum_mul,stopping_bin_weights_sum (primeBin s bin j₀) k₀ hk₀N,one_mul]

theorem geometric_bin_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : ∀ p ∈ s, norm p ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ j ∈ Finset.range (geometricBinCount ρ X), ∑ k ∈ Finset.Icc 1 s.card,
      ∑ t ∈ (primeBin s (geometricPrimeBin ρ X) j).powersetCard k,
        if R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) j t)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X)/geometricBinLower ρ X j < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) j t)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
          ((primeBin s (geometricPrimeBin ρ X) j).card.choose k:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s (geometricPrimeBin ρ X) j t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s (geometricPrimeBin ρ X) j t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  apply prime_bin_stopping_sum s hs
    (geometricPrimeBin ρ X) (geometricBinLower ρ X) _ _ _ hR hstart hend ψ w
  · exact fun p hp => geometricPrimeBin_index hρ hρ₂ (hs p hp) (hX p hp)
  · exact fun j => one_le_pow₀ hρ.le
  · exact fun j hj => geometricBinLower_gt_one hρ hj

end CubicFirstMoment

end

end OAI
