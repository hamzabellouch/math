import Mathlib

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem scaled_weightedOrder_subst
    (w : σ → ℕ) (v : τ → ℕ) (A B : ℕ) (hB : 0 < B)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (N : ℕ∞) (hf : N ≤ f.weightedOrder w)
    (hcontact : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (a i).weightedOrder v) :
    (A : ℕ∞) * N ≤ (B : ℕ∞) * (f.subst a).weightedOrder v := by
  have hB0 : (B : ℕ∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  apply le_trans _ (mul_le_mul_right (le_weightedOrder_subst v ha f) (B : ℕ∞))
  rw [ENat.mul_iInf_of_ne hB0]
  apply le_iInf
  intro d
  rw [ENat.mul_iInf_of_ne hB0]
  apply le_iInf
  intro hd
  calc
    (A : ℕ∞) * N ≤ (A : ℕ∞) * (d.weight w : ℕ∞) :=
      mul_le_mul_right (hf.trans (weightedOrder_le w hd)) _
    _ ≤ (B : ℕ∞) * d.weight (weightedOrder v ∘ a) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
        Nat.cast_sum, Nat.cast_mul, Nat.cast_id, Finset.mul_sum, Function.comp_apply]
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc, mul_left_comm] using
        mul_le_mul_right (hcontact i) (d i : ℕ∞)

theorem scaled_order_subst
    (w : σ → ℕ) (A B : ℕ) (hB : 0 < B)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (N : ℕ∞) (hf : N ≤ f.weightedOrder w)
    (hcontact : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (a i).order) :
    (A : ℕ∞) * N ≤ (B : ℕ∞) * (f.subst a).order :=
  scaled_weightedOrder_subst w (fun _ => 1) A B hB f a ha N hf hcontact

theorem scaled_order_subst_of_jet_vanishing
    (w : σ → ℕ) (A B : ℕ) (hB : 0 < B)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (N : ℕ∞)
    (hjet : ∀ d : σ →₀ ℕ, (d.weight w : ℕ∞) < N → coeff d f = 0)
    (hcontact : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (a i).order) :
    (A : ℕ∞) * N ≤ (B : ℕ∞) * (f.subst a).order :=
  scaled_order_subst w A B hB f a ha N (le_weightedOrder w hjet) hcontact

theorem order_add_high_tail (f t : MvPowerSeries τ S) (ht : f.order < t.order) :
    (f + t).order = f.order := by
  rw [order_add_of_order_ne ht.ne, inf_eq_left.mpr ht.le]

theorem scaled_order_add_lower_bound (A B : ℕ) (n : ℕ)
    (f t : MvPowerSeries τ S)
    (hf : (A : ℕ∞) * n ≤ (B : ℕ∞) * f.order)
    (ht : (A : ℕ∞) * n ≤ (B : ℕ∞) * t.order) :
    (A : ℕ∞) * n ≤ (B : ℕ∞) * (f + t).order := by
  calc
    (A : ℕ∞) * n ≤ min ((B : ℕ∞) * f.order) ((B : ℕ∞) * t.order) :=
      le_min hf ht
    _ = (B : ℕ∞) * min f.order t.order := (mul_min _ _ _).symm
    _ ≤ (B : ℕ∞) * (f + t).order := mul_le_mul_right min_order_le_add _

theorem scaled_powerSeries_order_subst
    (w : σ → ℕ) (A B : ℕ) (hB : 0 < B)
    (f : MvPowerSeries σ R) (a : σ → PowerSeries S)
    (ha : HasSubst a) (N : ℕ∞) (hf : N ≤ f.weightedOrder w)
    (hcontact : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (a i).order) :
    (A : ℕ∞) * N ≤ (B : ℕ∞) * PowerSeries.order (f.subst a) := by
  simp only [PowerSeries.order_eq_order] at hcontact ⊢
  exact scaled_order_subst w A B hB f a ha N hf hcontact

theorem scaled_order_subst_add_tail
    (w : σ → ℕ) (A B : ℕ) (hB : 0 < B)
    (f : MvPowerSeries σ R) (a t : σ → MvPowerSeries τ S)
    (hat : HasSubst (fun i => a i + t i)) (N : ℕ∞)
    (hf : N ≤ f.weightedOrder w)
    (ha : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (a i).order)
    (ht : ∀ i, (A : ℕ∞) * w i ≤ (B : ℕ∞) * (t i).order) :
    (A : ℕ∞) * N ≤ (B : ℕ∞) * (f.subst (fun i => a i + t i)).order := by
  apply scaled_order_subst w A B hB f _ hat N hf
  intro i
  exact scaled_order_add_lower_bound A B (w i) (a i) (t i) (ha i) (ht i)

theorem minimum_order_add_high_tail [Nonempty σ]
    (a t : σ → MvPowerSeries τ S)
    (ht : ∀ i, (⨅ j, (a j).order) < (t i).order) :
    (⨅ i, (a i + t i).order) = ⨅ i, (a i).order := by
  obtain ⟨i, hi⟩ := ENat.exists_eq_iInf (fun i => (a i).order)
  apply le_antisymm
  · calc
      (⨅ j, (a j + t j).order) ≤ (a i + t i).order := iInf_le _ i
      _ = (a i).order := order_add_high_tail _ _ (hi ▸ ht i)
      _ = ⨅ j, (a j).order := hi
  · apply le_iInf
    intro j
    exact (le_min (iInf_le _ j) (ht j).le).trans min_order_le_add

theorem minimum_scaled_order_add_high_tail [Nonempty σ]
    (c : σ → ℕ) (hc : ∀ i, 0 < c i) (a t : σ → MvPowerSeries τ S)
    (ht : ∀ i, (⨅ j, (c j : ℕ∞) * (a j).order) < (c i : ℕ∞) * (t i).order) :
    (⨅ i, (c i : ℕ∞) * (a i + t i).order) =
      ⨅ i, (c i : ℕ∞) * (a i).order := by
  obtain ⟨i, hi⟩ := ENat.exists_eq_iInf (fun i => (c i : ℕ∞) * (a i).order)
  apply le_antisymm
  · have hc0 : (c i : ℕ∞) ≠ 0 := by exact_mod_cast (hc i).ne'
    have hlt : (c i : ℕ∞) * (a i).order < (c i : ℕ∞) * (t i).order := by
      rw [hi]
      exact ht i
    have hord : (a i).order < (t i).order :=
      (ENat.mul_right_strictMono hc0 (by simp)).lt_iff_lt.mp hlt
    calc
      (⨅ j, (c j : ℕ∞) * (a j + t j).order) ≤
          (c i : ℕ∞) * (a i + t i).order := iInf_le _ i
      _ = (c i : ℕ∞) * (a i).order := by rw [order_add_high_tail _ _ hord]
      _ = ⨅ j, (c j : ℕ∞) * (a j).order := hi
  · apply le_iInf
    intro j
    calc
      (⨅ i, (c i : ℕ∞) * (a i).order) ≤
          min ((c j : ℕ∞) * (a j).order) ((c j : ℕ∞) * (t j).order) :=
        le_min (iInf_le _ j) (ht j).le
      _ = (c j : ℕ∞) * min (a j).order (t j).order := (mul_min _ _ _).symm
      _ ≤ (c j : ℕ∞) * (a j + t j).order := mul_le_mul_right min_order_le_add _

end PiExponent.FormalBranchOrder

end

end OAI
