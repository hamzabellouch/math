import OAI.Probability.Ising.PinnedMarginal

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Covariance of the two canonical spins of a positive two-spin table. -/
noncomputable def tableCovariance (w : Bool → Bool → ℝ) : ℝ :=
  tableExpectation w (fun s t => spin s * spin t) -
    tableExpectation w (fun s _ => spin s) *
      tableExpectation w (fun _ t => spin t)

/-- Multiplying by terminal fields does not change the effective interaction. -/
noncomputable def tiltTable (w : Bool → Bool → ℝ) (A B : ℝ) (s t : Bool) : ℝ :=
  w s t * Real.exp (A * spin s + B * spin t)

lemma tableCoupling_tilt (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (A B : ℝ) : tableCoupling (tiltTable w A B) = tableCoupling w := by
  simp only [tableCoupling, tiltTable, Real.log_mul (ne_of_gt (hw _ _))
    (Real.exp_ne_zero _), Real.log_exp, spin_true, spin_false]
  ring

lemma tableCovariance_formula (w : Bool → Bool → ℝ)
    (hZ : (∑ s, ∑ t, w s t) ≠ 0) :
    tableCovariance w =
      4 * (w true true * w false false - w true false * w false true) /
        (∑ s, ∑ t, w s t) ^ 2 := by
  simp only [tableCovariance, tableExpectation, Fintype.sum_bool, spin_true, spin_false] at *
  field_simp
  ring

lemma balancedTable_partition_le (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t) :
    (∑ s, ∑ t, balancedTable w s t) ≤ ∑ s, ∑ t, w s t := by
  have hexp : ∀ x : ℝ, 2 ≤ Real.exp x + Real.exp (-x) := by
    intro x
    have H := Real.one_le_cosh x
    rw [Real.cosh_eq] at H
    linarith
  have hA' := mul_le_mul_of_nonneg_left (hexp (tableFieldLeft w + tableFieldRight w))
    (Real.exp_pos (tableConstant w + tableCoupling w)).le
  have hB' := mul_le_mul_of_nonneg_left (hexp (tableFieldLeft w - tableFieldRight w))
    (Real.exp_pos (tableConstant w - tableCoupling w)).le
  simp only [Fintype.sum_bool, balancedTable_eq w hw, table_expansion w hw,
    spin_true, spin_false, mul_one, mul_neg_one]
  convert add_le_add hA' hB' using 1 <;> first
  | rfl
  | (simp only [Real.exp_add, Real.exp_sub, Real.exp_neg, mul_inv_rev, inv_inv, div_eq_mul_inv]; ring)

lemma tableCovariance_le_balanced (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (hdet : 0 ≤ w true true * w false false - w true false * w false true) :
    tableCovariance w ≤ tableCovariance (balancedTable w) := by
  have hb : ∀ s t, 0 < balancedTable w s t := by
    intro s t
    exact mul_pos (hw s t) (Real.exp_pos _)
  have hZ : 0 < ∑ s, ∑ t, w s t := by
    exact Finset.sum_pos (fun s _ => Finset.sum_pos (fun t _ => hw s t) Finset.univ_nonempty)
      Finset.univ_nonempty
  have hZb : 0 < ∑ s, ∑ t, balancedTable w s t := by
    exact Finset.sum_pos (fun s _ => Finset.sum_pos (fun t _ => hb s t) Finset.univ_nonempty)
      Finset.univ_nonempty
  have hprod : ∀ s t, balancedTable w s t * balancedTable w (!s) (!t) =
      w s t * w (!s) (!t) := by
    intro s t
    simp only [balancedTable, spin_not]
    calc
      _ = (w s t * w (!s) (!t)) *
        (Real.exp (-tableFieldLeft w * spin s - tableFieldRight w * spin t) *
          Real.exp (-tableFieldLeft w * -spin s - tableFieldRight w * -spin t)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        have hz : -tableFieldLeft w * spin s - tableFieldRight w * spin t +
          (-tableFieldLeft w * -spin s - tableFieldRight w * -spin t) = 0 := by ring
        rw [hz, Real.exp_zero, mul_one]
  rw [tableCovariance_formula w hZ.ne', tableCovariance_formula _ hZb.ne']
  have hp1 := hprod true true
  have hp2 := hprod true false
  simp only [Bool.not_true, Bool.not_false] at hp1 hp2
  rw [hp1, hp2]
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hdet)
    (sq_pos_of_pos hZb) (sq_le_sq₀ hZb.le hZ.le |>.mpr (balancedTable_partition_le w hw))

lemma tableCovariance_le_tanh (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (hdet : 0 ≤ w true true * w false false - w true false * w false true) :
    tableCovariance w ≤ Real.tanh (tableCoupling w) := by
  have H := tableCovariance_le_balanced w hw hdet
  have hm := balancedTable_means w hw
  simpa only [tableCovariance, hm.1, hm.2, zero_mul, sub_zero,
    balancedTable_correlation w hw] using H

/-- Actual addition of two (possibly mixed-sign) finite external fields. -/
def addTerminalFields {n : ℕ} (h : Fin n → ℝ) (u v : Fin n) (A B : ℝ)
    (x : Fin n) : ℝ := h x + (if x = u then A else 0) + (if x = v then B else 0)

lemma energy_addTerminalFields {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (u v : Fin n) (A B : ℝ) (σ : Spins n) :
    energy G (addTerminalFields h u v A B) σ =
      energy G h σ + A * spin (σ u) + B * spin (σ v) := by
  simp [energy, addTerminalFields, add_mul, Finset.sum_add_distrib, ite_mul]
  ring

lemma weight_addTerminalFields {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (u v : Fin n) (A B : ℝ) (σ : Spins n) :
    weight G (addTerminalFields h u v A B) σ =
      weight G h σ * Real.exp (A * spin (σ u) + B * spin (σ v)) := by
  unfold weight
  rw [energy_addTerminalFields, ← Real.exp_add]
  congr 1
  ring

lemma pairTable_addTerminalFields {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (u v : Fin n) (A B : ℝ) (s t : Bool) :
    pairTable (weight G (addTerminalFields h u v A B)) u v s t =
      tiltTable (pairTable (weight G h) u v) A B s t := by
  classical
  unfold pairTable tiltTable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hc : σ u = s ∧ σ v = t
  · rw [ite_eq_left hc, ite_eq_left hc, weight_addTerminalFields, hc.1, hc.2]
  · rw [ite_eq_right hc, ite_eq_right hc, zero_mul]

lemma pairTable_weight_pos {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ)
    (u v : Fin n) (huv : u ≠ v) (s t : Bool) :
    0 < pairTable (weight G h) u v s t := by
  classical
  unfold pairTable
  apply Finset.sum_pos'
  · intro σ _
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · refine ⟨fun x => if x = u then s else t, Finset.mem_univ _, ?_⟩
    simp only [ite_eq_right (Ne.symm huv), and_self, ite_true]
    exact weight_pos G h _

lemma pairTable_weight_eq_jointWeight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (u v : Fin n) (s t : Bool) :
    pairTable (weight G h) u v s t =
      jointWeight G h {u} {v} ∅ (fun _ => false) (fun _ => s) (fun _ => t) := by
  classical
  simp [pairTable, jointWeight, constrainedSum, AgreesOn]

lemma pairTable_weight_det_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (u v : Fin n) :
    0 ≤ pairTable (weight G h) u v true true * pairTable (weight G h) u v false false -
      pairTable (weight G h) u v true false * pairTable (weight G h) u v false true := by
  have H := jointWeight_logSupermodular G h {u} {v} ∅ (fun _ => false) ⊤ ⊥ ⊥ ⊤
  simp only [inf_bot_eq, bot_inf_eq, sup_bot_eq, bot_sup_eq] at H
  simp only [pairTable_weight_eq_jointWeight]
  change 0 ≤ jointWeight G h {u} {v} ∅ (fun _ => false) ⊤ ⊤ *
    jointWeight G h {u} {v} ∅ (fun _ => false) ⊥ ⊥ -
    jointWeight G h {u} {v} ∅ (fun _ => false) ⊤ ⊥ *
    jointWeight G h {u} {v} ∅ (fun _ => false) ⊥ ⊤
  linarith

lemma pairTable_weight_covariance {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (u v : Fin n) :
    tableCovariance (pairTable (weight G h) u v) =
      expectation G h (fun σ => spin (σ u) * spin (σ v)) -
        expectation G h (fun σ => spin (σ u)) * expectation G h (fun σ => spin (σ v)) := by
  simp only [tableCovariance, pairTable_expectation, expectation]

/-- Balancing a marginal is realized by external fields on the SAME graph. -/
lemma pairTable_balancedGraph {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (u v : Fin n) :
    pairTable (weight G (addTerminalFields h u v
      (-tableFieldLeft (pairTable (weight G h) u v))
      (-tableFieldRight (pairTable (weight G h) u v)))) u v =
      balancedTable (pairTable (weight G h) u v) := by
  funext s t
  rw [pairTable_addTerminalFields]
  simp only [tiltTable, balancedTable, sub_eq_add_neg, neg_mul]

lemma weight_zero_spinFlip {n m : ℕ} (G : FiniteGraph n m) (σ : Spins n) :
    weight G (fun _ => 0) (fun v => !σ v) = weight G (fun _ => 0) σ := by
  unfold weight energy
  simp only [spin_not, mul_neg, neg_mul, neg_neg, zero_mul, neg_zero]

lemma zero_pairTable_correlation {n m : ℕ} (G : FiniteGraph n m)
    (u v : Fin n) (huv : u ≠ v) :
    expectation G (fun _ => 0) (fun σ => spin (σ u) * spin (σ v)) =
      Real.tanh (tableCoupling (pairTable (weight G (fun _ => 0)) u v)) := by
  rw [← symmetricTable_correlation _ (pairTable_weight_pos G (fun _ => 0) u v huv)
    (pairTable_flip _ (weight_zero_spinFlip G) u v), pairTable_expectation]
  rfl

lemma tanh_le_tanh_iff (x y : ℝ) : Real.tanh x ≤ Real.tanh y ↔ x ≤ y := by
  have H := Real.artanh_le_artanh_iff
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  simpa only [Real.artanh_tanh] using H.symm

/-- External fields do not increase the two-terminal effective coupling. -/
def EffectiveCouplingBound : Prop :=
  ∀ (n m : ℕ) (G : FiniteGraph n m) (h : Fin n → ℝ) (u v : Fin n), u ≠ v →
    tableCoupling (pairTable (weight G h) u v) ≤
      tableCoupling (pairTable (weight G (fun _ => 0)) u v)

lemma expectation_one {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ) :
    expectation G h (fun _ => 1) = 1 := by
  have hZ : 0 < ∑ σ, weight G h σ :=
    Finset.sum_pos (fun σ _ => weight_pos G h σ) Finset.univ_nonempty
  simp only [expectation, mul_one]
  exact div_self hZ.ne'

/-- For finite ferromagnetic graphs, the arbitrary-field covariance bound and zero-field maximality of the effective coupling are equivalent. -/
theorem covarianceBound_iff_effectiveCouplingBound :
    ArbitraryFieldCovarianceBound ↔ EffectiveCouplingBound := by
  constructor
  · intro H n m G h u v huv
    let w := pairTable (weight G h) u v
    have hw : ∀ s t, 0 < w s t := pairTable_weight_pos G h u v huv
    have HC := H n m G (addTerminalFields h u v (-tableFieldLeft w) (-tableFieldRight w)) u v
    rw [← pairTable_weight_covariance, pairTable_balancedGraph] at HC
    have hm := balancedTable_means w hw
    change tableCovariance (balancedTable w) ≤ _ at HC
    simp only [tableCovariance, hm.1, hm.2, zero_mul, sub_zero,
      balancedTable_correlation w hw] at HC
    rw [zero_pairTable_correlation G u v huv] at HC
    exact (tanh_le_tanh_iff _ _).mp HC
  · intro H n m G h u v
    by_cases huv : u = v
    · subst v
      simp only [spin_sq, expectation_one]
      nlinarith [sq_nonneg (expectation G h (fun σ => spin (σ u)))]
    · rw [← pairTable_weight_covariance, zero_pairTable_correlation G u v huv]
      exact (tableCovariance_le_tanh _ (pairTable_weight_pos G h u v huv)
        (pairTable_weight_det_nonneg G h u v)).trans ((tanh_le_tanh_iff _ _).mpr (H n m G h u v huv))

end BufferedIsing

end OAI
