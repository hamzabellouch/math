import OAI.Probability.SwitchChain.FiniteVarianceDecomposition
import OAI.Probability.SwitchChain.FixedBlockCount
import OAI.Probability.SwitchChain.TripleCountGram

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.VariableBlockVariance
open FixedBlockMarginal (average)
open TripleCountLaw (Triple)

variable (U W : Type*) [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

def sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) (i : Fin 3) : ℕ :=
  (x.val i).val + o i

abbrev Fiber (m : ℕ) (u w : Fin 3 → ℕ) (x : Triple m) :=
  FixedBlockVariance.State (α := U) (β := W) (sizes u x) (sizes w x)

abbrev Family (m : ℕ) (u w : Fin 3 → ℕ) :=
  Σ x : Triple m, Fiber U W m u w x

variable {U W}

theorem sum_sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    ∑ i, sizes o x i = m + ∑ i, o i := by
  simp only [sizes, Finset.sum_add_distrib, x.property]

theorem fiber_nonempty (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W) (x : Triple m) :
    Nonempty (Fiber U W m u w x) := by
  obtain ⟨c⟩ := FixedBlock.partition_nonempty (α := U) (sizes u x)
    ((sum_sizes u x).trans hU)
  obtain ⟨d⟩ := FixedBlock.partition_nonempty (α := W) (sizes w x)
    ((sum_sizes w x).trans hW)
  exact ⟨(c, d)⟩

theorem pairSizeWeight_eq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0) (x : Triple m) :
    FixedBlock.pairSizeWeight (sizes u x) (sizes w x) =
      TripleCountLaw.weight (fun i => u i + w i) x := by
  unfold FixedBlock.pairSizeWeight TripleCountLaw.weight
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases hsep i with hu | hw
  · simp [sizes, hu, CountCoupling.countWeight, one_div]
  · simp [sizes, hw, CountCoupling.countWeight, one_div, mul_comm]

theorem family_average (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (f : Family U W m u w → ℝ) :
    average f = ∑ x : Triple m, TripleCountLaw.probability (fun i => u i + w i) x *
      average (fun z : Fiber U W m u w x => f ⟨x, z⟩) := by
  have h := FixedBlock.uniform_family_expectation (α := U) (β := W)
    (sizes u : Triple m → Fin 3 → ℕ) (sizes w)
    (fun x => (sum_sizes u x).trans hU) (fun x => (sum_sizes w x).trans hW)
    (fun x z => f ⟨x, z⟩)
  change average f = _ at h
  simp_rw [pairSizeWeight_eq m u w hsep] at h
  rw [h]
  simp only [TripleCountLaw.probability, TripleCountLaw.totalWeight,
    div_mul_eq_mul_div, ← Finset.sum_div, average]

def rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3)
    (x : Triple m) (z : Fiber U W m u w x) : ℝ :=
  g i (FixedBlock.row z.1.val i) (FixedBlock.row z.2.val i)

def rowMean (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  average (fun z : FixedBlockMarginal.Subsets (α := U) (t.val + u i) ×
      FixedBlockMarginal.Subsets (α := W) (t.val + w i) => g i z.1.val z.2.val)

theorem average_rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (x : Triple m) :
    average (rowFunction m u w g i x) = rowMean m u w g i (x.val i) := by
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x
  exact FixedBlockMarginal.row_function_average_eq_subset_average i z.1 z.2 (g i)

theorem marginal_expectation (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (b : Fin (m + 1) → ℝ) :
    (∑ t, TripleCountLaw.marginal a m i t * b t) =
      ∑ x : Triple m, TripleCountLaw.probability a x * b (x.val i) := by
  classical
  unfold TripleCountLaw.marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem centered_row_average_sq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ)
    (hcenter : ∀ i, average (fun z : Family U W m u w =>
      rowFunction m u w g i z.1 z.2) = 0) :
    average (fun z : Family U W m u w =>
      (∑ i, rowFunction m u w g i z.1 z.2) ^ 2) ≤
      2 * ∑ i, average (fun z : Family U W m u w =>
        (rowFunction m u w g i z.1 z.2) ^ 2) := by
  let (x : Triple m) : Nonempty (Fiber U W m u w x) :=
    fiber_nonempty m u w hU hW x
  have hb (i : Fin 3) : ∑ t, TripleCountLaw.marginal (fun j => u j + w j) m i t *
      rowMean m u w g i t = 0 := by
    rw [marginal_expectation]
    have hc := hcenter i
    rw [family_average m u w hsep hU hW] at hc
    simpa only [average_rowFunction m u w hU hW g i] using hc
  have hmean := TripleCountLaw.count_row_variance_le_two
    (fun i => u i + w i) m (rowMean m u w g) hb
  simp_rw [marginal_expectation] at hmean
  simp_rw [family_average m u w hsep hU hW]
  apply FiniteVariance.mixture_centered_row_bound (Fiber U W m u w)
    (TripleCountLaw.probability (fun i => u i + w i))
    (fun x => (TripleCountLaw.probability_pos _ x).le)
    (rowFunction m u w g)
  · intro x
    exact FixedBlockVariance.variance_sum_row_functions (sizes u x) (sizes w x) g
  · simpa only [average_rowFunction m u w hU hW] using hmean

theorem row_variance_bound (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun z : Family U W m u w =>
      ∑ i, rowFunction m u w g i z.1 z.2) ≤
      2 * ∑ i, FiniteVariance.variance (fun z : Family U W m u w =>
        rowFunction m u w g i z.1 z.2) := by
  obtain ⟨x⟩ := TripleCountLaw.fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x.val
  let : Nonempty (Family U W m u w) := ⟨⟨x.val, z⟩⟩
  let c (i : Fin 3) := average (fun z : Family U W m u w =>
    rowFunction m u w g i z.1 z.2)
  let g' (i : Fin 3) (s : Finset U) (t : Finset W) := g i s t - c i
  have he (i : Fin 3) (z : Family U W m u w) :
      rowFunction m u w g' i z.1 z.2 = rowFunction m u w g i z.1 z.2 - c i := rfl
  have hc (i : Fin 3) : average (fun z : Family U W m u w =>
      rowFunction m u w g' i z.1 z.2) = 0 := by
    simp_rw [he]
    exact FiniteVariance.average_center _
  have h := centered_row_average_sq m u w hsep hU hW g' hc
  simp_rw [he, Finset.sum_sub_distrib] at h
  unfold FiniteVariance.variance
  rw [FiniteVariance.average_sum]
  exact h

end Problem315.VariableBlockVariance

end

end OAI
