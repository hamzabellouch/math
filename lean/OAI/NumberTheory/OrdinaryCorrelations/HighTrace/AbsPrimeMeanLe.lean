import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ClosedLine

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {p ℓ : ℕ} [NeZero p]

lemma abs_primeMean_le (f : ZMod p → ℝ) :
    |primeMean f| ≤ primeMean (fun a => |f a|) := by
  rw [primeMean, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem singleton_abs_mean_le (b : Fin ℓ → ℤ) (d : Fin ℓ → ℕ)
    (e : Fin ℓ) (he : ∀ i, p ∣ d i ↔ i = e) (k : ℕ)
    (hk : k ≤ departureCount b (activeResidue b e : ZMod p)) :
    primeMean (fun a : ZMod p => |centerPrimeFactor b d a|) ≤ (betaZ ^ k + theta) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast NeZero.pos p
  have hb0 : 0 ≤ betaZ := by norm_num
  have hb1 : betaZ ≤ 1 := by norm_num
  have ht0 : 0 ≤ theta / (p : ℝ) := div_nonneg (by norm_num) hp.le
  have ht1 : theta / (p : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    simpa only [one_mul] using (show theta ≤ (1 : ℝ) by norm_num).trans hp1
  let a₀ : ZMod p := activeResidue b e
  let G : ZMod p → ℝ := fun a => if a = a₀ then betaZ ^ k else theta / p
  have hpoint (a : ZMod p) : |centerPrimeFactor b d a| ≤ G a := by
    rw [centerPrimeFactor_singleton b d e he, abs_mul,
      abs_of_nonneg (pow_nonneg hb0 _)]
    by_cases ha : a = a₀
    · rw [ha]
      change |(if a₀ = a₀ then (1 : ℝ) else 0) - theta / p| *
        betaZ ^ departureCount b a₀ ≤ if a₀ = a₀ then betaZ ^ k else theta / p
      simp only [ite_true]
      rw [abs_of_nonneg (sub_nonneg.mpr ht1)]
      calc
        _ ≤ 1 * betaZ ^ departureCount b a₀ :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb0 _)
        _ = betaZ ^ departureCount b a₀ := one_mul _
        _ ≤ betaZ ^ k := pow_le_pow_of_le_one hb0 hb1 hk
    · change |(if a = a₀ then (1 : ℝ) else 0) - theta / p| *
        betaZ ^ departureCount b a ≤ G a
      rw [ite_eq_right ha, zero_sub, abs_neg, abs_of_nonneg ht0]
      change theta / (p : ℝ) * betaZ ^ departureCount b a ≤ if a = a₀ then _ else _
      rw [ite_eq_right ha]
      calc
        _ ≤ theta / (p : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hb0 hb1) ht0
        _ = _ := mul_one _
  calc
    _ ≤ primeMean G := mul_le_mul_of_nonneg_left
      (sum_le_sum (fun a _ => hpoint a)) (inv_nonneg.mpr hp.le)
    _ = (betaZ ^ k + theta - theta / (p : ℝ)) / p := by
      have hg (a : ZMod p) : G a = theta / (p : ℝ) +
          (if a = a₀ then betaZ ^ k - theta / (p : ℝ) else 0) := by
        simp only [G]
        split_ifs <;> ring
      simp only [primeMean, hg, sum_add_distrib, sum_const, card_univ, ZMod.card,
        nsmul_eq_mul]
      simp only [sum_ite_eq', mem_univ, ite_true]
      field_simp
      ring
    _ ≤ (betaZ ^ k + theta) / p :=
      div_le_div_of_nonneg_right (by linarith) hp.le

namespace ClosedLine
variable {h : ℕ}

omit [NeZero p] in
lemma departureCount_ge_endpoint_children (w : ClosedLine h ℓ) (hh : 0 < h)
    (e : Fin ℓ) (he : p ∣ w.label e) :
    w.children (w.offset e.castSucc) + w.children (w.offset e.succ) ≤
      departureCount w.departures (activeResidue w.departures e : ZMod p) := by
  let u := w.offset e.castSucc
  let v := w.offset e.succ
  let su := w.treeSteps.filter (fun i => w.offset i.castSucc = u)
  let sv := w.treeSteps.filter (fun i => w.offset i.castSucc = v)
  have huv : u ≠ v := w.endpoints_ne hh e
  have hres : (v : ZMod p) = (u : ZMod p) := w.label_residue_eq e he
  have hdis : Disjoint su sv := disjoint_left.mpr (by
    intro i hi hj
    exact huv ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))
  have hsub : su ∪ sv ⊆ univ.filter (fun i =>
      (activeResidue w.departures e : ZMod p) = activeResidue w.departures i) := by
    intro i hi
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hi with hi | hi
    · have hi' := (mem_filter.mp hi).2
      simp only [activeResidue, departures, hi']
      rfl
    · have hi' := (mem_filter.mp hi).2
      simp only [activeResidue, departures, hi']
      change -(u : ZMod p) = -(v : ZMod p)
      rw [hres]
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hc
  exact hc

end ClosedLine
end OrdinaryCorrelations.SignedTrace

end

end OAI
