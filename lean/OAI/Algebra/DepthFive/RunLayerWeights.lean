import OAI.Algebra.DepthFive.RunBlocks
import OAI.Algebra.DepthFive.RunWeights

namespace OAI

/-! Concrete layer weights combined with contiguous true-run decomposition. -/

open scoped BigOperators

namespace Problem335.RunLayerWeights

variable {ι : Type*}

/-- A product of two possible layer weights depends only on the two layer counts. -/
theorem prod_ite_eq_powers {R : Type*} [CommMonoid R]
    (p : ι → Bool) (l : List ι) (a b : R) :
    (l.map (fun i => if p i then a else b)).prod =
      a ^ l.countP p * b ^ l.countP (fun i => !p i) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp [hp, ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The derivative/multiplication layer product in the notation of the manuscript. -/
theorem layer_product_eq (p : ι → Bool) (l : List ι) (α β : ℝ) (hα : 0 < α) :
    (l.map (fun i => if p i then α⁻¹ else β)).prod =
      α ^ (-(l.countP p : ℝ)) * β ^ l.countP (fun i => !p i) := by
  rw [prod_ite_eq_powers]
  congr 1
  rw [Real.rpow_neg hα.le, Real.rpow_natCast, inv_pow]

/-- The rounding loss counts only multiplication layers. -/
theorem layer_loss_sum_eq (p : ι → Bool) (l : List ι) (ε : ℝ) :
    (l.map (fun i => if p i then 0 else ε)).sum =
      ε * (l.countP (fun i => !p i) : ℝ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp [hp, ih, Nat.cast_add, mul_add, add_comm]

/-- An interval discrepancy bound gives the required majorant on each true block. -/
theorem selected_layer_product_le {n : ℕ}
    (isV w : Fin (n + 1) → Bool) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP isV : ℝ) - ρ * b.countP (fun i => !isV i) ≤ 1 + ρ) :
    ((((List.ofFn id).filter w).map (fun i => if isV i then α⁻¹ else β))).prod ≤
      N ^ WordRuns.runCount w *
        Real.exp (ε * (((List.ofFn id).filter w).countP (fun i => !isV i) : ℝ)) := by
  have h := WordRuns.selected_prod_le_pow_runCount_mul_exp w
    (fun i => if isV i then α⁻¹ else β) (fun i => if isV i then 0 else ε) N
    (by intro i; split <;> positivity) ?_
  · simpa only [layer_loss_sum_eq] using h
  · intro b hb
    rw [layer_product_eq isV b α β hα, layer_loss_sum_eq]
    exact RunWeights.interval_weight_le hα hα1 hβ hβupper hscale _ _
      (hdiscrepancy b (WordRuns.trueBlocks_infix w (List.ofFn id) hb))

/-- The total rounding cost is bounded by the length of the entire word. -/
theorem selected_layer_product_le_length {n : ℕ}
    (isV w : Fin (n + 1) → Bool) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP isV : ℝ) - ρ * b.countP (fun i => !isV i) ≤ 1 + ρ) :
    ((((List.ofFn id).filter w).map (fun i => if isV i then α⁻¹ else β))).prod ≤
      N ^ WordRuns.runCount w * Real.exp (ε * (n + 1 : ℕ)) := by
  have hN : 0 ≤ N := (Real.rpow_nonneg hα.le _).trans hscale
  apply (selected_layer_product_le isV w hα hα1 hβ hβupper hscale hdiscrepancy).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hε
  exact_mod_cast (List.countP_le_length.trans (List.length_filter_le _ _)).trans
    (by simp : (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).length ≤ n + 1)

/-- Transfer discrepancy bounds from a Boolean layer schedule to lists of its positions. -/
theorem indexed_discrepancy_of_word_discrepancy {n : ℕ}
    (isV : Fin n → Bool) (ρ : ℝ)
    (h : ∀ l : List Bool, l <:+: List.ofFn isV →
      (l.count true : ℝ) - ρ * l.count false ≤ 1 + ρ) :
    ∀ b : List (Fin n), b <:+: List.ofFn id →
      (b.countP isV : ℝ) - ρ * b.countP (fun i => !isV i) ≤ 1 + ρ := by
  intro b hb
  have hm : b.map isV <:+: List.ofFn isV := by
    simpa using hb.map isV
  have hh := h (b.map isV) hm
  have ht : (b.map isV).count true = b.countP isV := by
    clear hb hm hh h
    induction b with
    | nil => simp
    | cons i b ih => cases hi : isV i <;> simp [hi, ih]
  have hf : (b.map isV).count false = b.countP (fun i => !isV i) := by
    clear hb hm hh ht h
    induction b with
    | nil => simp
    | cons i b ih => cases hi : isV i <;> simp [hi, ih]
  simpa only [ht, hf] using hh

/-- List counts on the selected positions coincide with the finite-set cardinality. -/
theorem selected_countP_eq_card {n : ℕ} (w : Fin n → Bool) (V : Finset (Fin n)) :
    ((List.ofFn id).filter w).countP (fun i => decide (i ∈ V)) =
      (V.filter (fun i => w i = true)).card := by
  rw [List.countP_eq_length_filter]
  have hn : (((List.ofFn (id : Fin n → Fin n)).filter w).filter
      (fun i => decide (i ∈ V))).Nodup :=
    ((List.nodup_ofFn.mpr Function.injective_id).filter _).filter _
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext i
  simp [and_comm]

/-- The local layer product is exactly the count-based weight used by isolated flipping. -/
theorem selected_layer_product_eq_powers {n : ℕ} (w : Fin n → Bool)
    (V : Finset (Fin n)) (A B : ℝ) :
    ((((List.ofFn id).filter w).map (fun i => if i ∈ V then A else B))).prod =
      A ^ (V.filter (fun i => w i = true)).card *
        B ^ ((Finset.univ \ V).filter (fun i => w i = true)).card := by
  have hp := prod_ite_eq_powers (fun i : Fin n => decide (i ∈ V))
    ((List.ofFn id).filter w) A B
  have hV := selected_countP_eq_card w V
  have hU := selected_countP_eq_card w (Finset.univ \ V)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not] at hU
  simpa only [decide_eq_true_eq, hV, hU] using hp

/-- Exact count-based per-word estimate consumed by the corrected word-sum proof. -/
theorem count_weight_le_exp_mul_runCount {n : ℕ} (w : Fin (n + 1) → Bool)
    (V : Finset (Fin (n + 1))) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP (fun i => decide (i ∈ V)) : ℝ) -
        ρ * b.countP (fun i => !decide (i ∈ V)) ≤ 1 + ρ) :
    (α⁻¹) ^ (V.filter (fun i => w i = true)).card *
        β ^ ((Finset.univ \ V).filter (fun i => w i = true)).card ≤
      Real.exp (ε * (n + 1 : ℕ)) * N ^ WordRuns.runCount w := by
  have h := selected_layer_product_le_length (fun i => decide (i ∈ V)) w
    hα hα1 hβ hε hβupper hscale hdiscrepancy
  simp only [decide_eq_true_eq] at h
  rw [selected_layer_product_eq_powers] at h
  simpa only [mul_comm] using h

end Problem335.RunLayerWeights

end OAI
