import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingUnique
import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppingLabels

namespace OAI

/-! Exact stopping reconstruction in the three labels occurring in the
manuscript: final bin, selected occupancy, and remaining occupancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The independent side predicates recover the exact selected subset. -/
lemma stoppingSelected_of_separated_bins (d e : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (j : ℕ)
    (hd : ∀ p ∈ d, bin p ≤ j) (he : ∀ p ∈ e, j ≤ bin p) :
    stoppingSelected (d ∪ e) bin j (primeBin d bin j) = d := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hp,hpj⟩ := Finset.mem_filter.mp hp
      rcases Finset.mem_union.mp hp with hpd | hpe
      · exact hpd
      · exact (not_lt_of_ge (he p hpe) hpj).elim
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    by_cases hpj : bin p < j
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hp,hpj⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hp,by have := hd p hp; omega⟩)

lemma stoppingRemainder_of_separated_bins (d e : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (j : ℕ) (hde : Disjoint d e)
    (hd : ∀ p ∈ d, bin p ≤ j) (he : ∀ p ∈ e, j ≤ bin p) :
    stoppingRemainder (d ∪ e) bin j (primeBin d bin j) = e := by
  rw [stoppingRemainder,stoppingSelected_of_separated_bins d e bin j hd he]
  ext p
  have hdis := Finset.disjoint_left.mp hde
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨hp,hnd⟩
    exact hp.resolve_left hnd
  · intro hp
    exact ⟨Or.inr hp,fun hpd => hdis hpd hp⟩

lemma stopping_occupancies_add {s : Finset Eisenstein} {bin : Eisenstein → ℕ}
    {j k : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) :
    k+(primeBin (stoppingRemainder s bin j t) bin j).card =
      (primeBin s bin j).card := by
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  change k+((stoppingRemainder s bin j t).filter (fun p => bin p = j)).card = _
  rw [stoppingRemainder_bin_count hsub,←hcard,Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Inserting the remaining occupancy changes neither the actual finite
sum nor its inverse-binomial coefficient. -/
lemma stopping_insert_remaining_count (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k M : ℕ)
    (hM : s.card ≤ M) (R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ l ∈ Finset.range (M+1), ∑ t ∈ (primeBin s bin j).powersetCard k,
      if (primeBin (stoppingRemainder s bin j t) bin j).card = l ∧
          (R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) then
        (Nat.choose (k+l) k:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
           cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
      else 0) =
    ∑ t ∈ (primeBin s bin j).powersetCard k,
      if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
        ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
           cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
      else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  let l := (primeBin (stoppingRemainder s bin j t) bin j).card
  have hl : l ∈ Finset.range (M+1) := by
    apply Finset.mem_range.mpr
    have hr : stoppingRemainder s bin j t ⊆ s := Finset.sdiff_subset
    have hc : l ≤ s.card := (Finset.card_filter_le _ _).trans (Finset.card_le_card hr)
    omega
  rw [Finset.sum_eq_single l]
  · have he := stopping_occupancies_add ht
    dsimp only [l] at *
    simp only [true_and,he]
  · intro l' _hl' hne
    apply ite_eq_right
    exact fun h => hne h.1.symm
  · exact fun h => (h hl).elim

/-- The complete three-label stopping sum, with no assumed reconstruction
identity and no hidden choice of the first bin. -/
theorem geometric_label_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm (∏ p ∈ s, p) ≤ X)
    (hpX : ∀ p ∈ s, norm p ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ q ∈ stoppingLabelBox ρ X,
      ∑ t ∈ (primeBin s (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
        if (primeBin (stoppingRemainder s (geometricPrimeBin ρ X) q.1 t)
              (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
            (R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) q.1 t)
                (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
                  geometricBinLower ρ X q.1 < Z ∧
              Z ≤ R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) q.1 t)
                (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
          (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s (geometricPrimeBin ρ X) q.1 t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s (geometricPrimeBin ρ X) q.1 t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  have hprim : primary (∏ p ∈ s, p) := primary_finset_prod s (fun p => p) (fun p hp => (hs p hp).1)
  have hsf := primaryPrime_product_squarefree s hs
  have hM : s.card ≤ stoppingFactorLimit X := by
    apply stopping_prime_factor_count hprim hsf _ hX hnorm
    rw [primaryPrimeFactors_finset_prod s hs]
  let M := stoppingFactorLimit X
  let bin := geometricPrimeBin ρ X
  let ell := geometricBinLower ρ X
  let F := fun j k => ∑ t ∈ (primeBin s bin j).powersetCard k,
    if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
      ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
        (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
         cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
    else 0
  simp only [stoppingLabelBox,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  calc
    _ = ∑ j ∈ Finset.range (geometricBinCount ρ X),
        ∑ k ∈ (Finset.range (M+1)).filter (fun k => 1 ≤ k), F j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkpos : 1 ≤ k
      · simp only [hkpos,ite_true]
        exact stopping_insert_remaining_count s bin ell j k M hM R Z ψ w
      · simp only [hkpos,ite_false,Finset.sum_const_zero]
    _ = ∑ j ∈ Finset.range (geometricBinCount ρ X),
        ∑ k ∈ Finset.Icc 1 s.card, F j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      apply Finset.sum_subset
      · intro k hk
        obtain ⟨hklo,hkhi⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [M]; omega),hklo⟩
      · intro k hk hnot
        have hklo := (Finset.mem_filter.mp hk).2
        have hkhi : s.card < k := by
          by_contra hn
          exact hnot (Finset.mem_Icc.mpr ⟨hklo,by omega⟩)
        have hempty : (primeBin s bin j).powersetCard k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
          have hc := (Finset.card_le_card hsub).trans (Finset.card_filter_le _ _)
          omega
        simp only [F,hempty,Finset.sum_empty]
    _ = _ := geometric_bin_stopping_sum s hs hρ hρ₂ hpX hR hstart hend ψ w

end CubicFirstMoment

end

end OAI
