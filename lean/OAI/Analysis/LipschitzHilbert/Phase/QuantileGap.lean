import OAI.Analysis.LipschitzHilbert.Trees.EventMass
import OAI.Analysis.LipschitzHilbert.Phase.FrequencyQuantiles

namespace OAI

/-!
# Quantitative fourth-moment gap

The complete combinatorial lemma `phase:quantile-gap` in §7 of
*A uniform Hilbert transform estimate for Lipschitz directions*.
This is a supporting lemma, not the paper's main Hilbert-transform theorem.
-/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*}

theorem separated_injective {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) : Function.Injective frequency := by
  intro i j hij
  by_contra hne
  have hs := hsep hne
  rw [hij, sub_self, abs_zero] at hs
  linarith

/-- The precise strict gap, uniform in the number and positions of frequencies. -/
theorem quantile_gap [Fintype ι] {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hatom : ∀ i, x i ≤ 1 - κ) :
    resonanceSum frequency gap x ≤ 1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096 := by
  classical
  obtain ⟨a, b, hab, ha, hb, hc⟩ := frequency_quantiles x frequency hx hsum
    (separated_injective hgap hsep) hκ hκ1 hatom
  have habgap : gap ≤ frequency b - frequency a := by
    have hne : a ≠ b := by intro h; subst b; exact lt_irrefl _ hab
    have hs := hsep hne
    rwa [abs_of_neg (sub_neg.mpr hab), neg_sub] at hs
  obtain ⟨e, h, hae, heh, hhb, hlen, hmass⟩ :=
    exists_heavy_half x frequency hx hab.le hc
  let I := Finset.univ.filter (fun i => frequency b ≤ frequency i)
  let K := Finset.univ.filter (fun i => frequency i ≤ frequency a)
  let L := Finset.univ.filter (fun i => frequency i ≤ h)
  let J := Finset.univ.filter (fun i => frequency i < e)
  have hJL : J ⊆ L := by
    intro i hi
    simp only [J, L, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.le.trans heh
  have hI : κ / 4 ≤ ∑ i ∈ I, x i := by simpa [I, Finset.sum_filter] using hb
  have hK : κ / 4 ≤ ∑ i ∈ K, x i := by simpa [K, Finset.sum_filter] using ha
  have hcentral : (1 - κ / 2) / 2 ≤ ∑ i ∈ L \ J, x i := by
    have hset : L \ J = Finset.univ.filter (fun i => e ≤ frequency i ∧ frequency i ≤ h) := by
      ext i
      simp only [L, J, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi, hj⟩
        exact ⟨le_of_not_gt hj, hi⟩
      · rintro ⟨hi, hj⟩
        exact ⟨hj, not_lt.mpr hi⟩
    rw [hset, Finset.sum_filter]
    exact hmass
  exact quantitative_gap_of_event_mass_bounds hgap hsep hκ hκ1 x hx hsum
    I K L J hJL (threshold_event_completion hgap habgap hlen.le) hI hK hcentral

/-- The simplified numerical lower bound for the gap in the manuscript. -/
theorem quantile_gap_simplified [Fintype ι] {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hatom : ∀ i, x i ≤ 1 - κ) :
    resonanceSum frequency gap x ≤ 1 - κ ^ 4 / 16384 := by
  have h := quantile_gap hgap hsep hκ hκ1 x hx hsum hatom
  have hs : (1 / 2 : ℝ) ^ 2 ≤ (1 - κ / 2) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hκ.le 4)
  nlinarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
