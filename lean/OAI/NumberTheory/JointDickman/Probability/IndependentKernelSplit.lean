import OAI.NumberTheory.JointDickman.Probability.FairSplitChannel
import OAI.NumberTheory.JointDickman.Probability.LowExclusiveKernel
import OAI.NumberTheory.JointDickman.Probability.FlatExclusiveKernel

namespace OAI

/-!
# The independent common/exclusive model and its cutoff

The three independent category bits are reindexed as three independent
Boolean prime subsets. Their products are the common product and the two
exclusive products. The low-exclusive union is separated exactly; the
complement is the product of the two high-exclusive cell probabilities.
-/

namespace JointDickman

open scoped BigOperators

def categoryToTriple (S : SplitCategories) : Bool × Bool × Bool :=
  (decide ((0 : Fin 3) ∈ S.val), decide ((1 : Fin 3) ∈ S.val),
    decide ((2 : Fin 3) ∈ S.val))

def tripleToCategory (b : Bool × Bool × Bool) : SplitCategories :=
  ⟨Finset.univ.filter (fun j : Fin 3 =>
    (if j = 0 then b.1 else if j = 1 then b.2.1 else b.2.2) = true),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

theorem tripleToCategory_categoryToTriple (S : SplitCategories) :
    tripleToCategory (categoryToTriple S) = S := by
  apply Subtype.ext
  apply Finset.ext
  intro j
  fin_cases j <;> simp [tripleToCategory, categoryToTriple]

theorem categoryToTriple_tripleToCategory (b : Bool × Bool × Bool) :
    categoryToTriple (tripleToCategory b) = b := by
  rcases b with ⟨b₀, b₁, b₂⟩
  cases b₀ <;> cases b₁ <;> cases b₂ <;> rfl

/-- Three category bits at each site are exactly three Boolean vectors. -/
def categoryTripleEquiv (ι : Type*) :
    (ι → SplitCategories) ≃ (ι → Bool) × (ι → Bool) × (ι → Bool) where
  toFun y := (fun i => (categoryToTriple (y i)).1,
    fun i => (categoryToTriple (y i)).2.1, fun i => (categoryToTriple (y i)).2.2)
  invFun x i := tripleToCategory (x.1 i, x.2.1 i, x.2.2 i)
  left_inv y := by
    funext i
    exact tripleToCategory_categoryToTriple (y i)
  right_inv x := by
    rcases x with ⟨c, e₁, e₂⟩
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))
    · apply Prod.ext <;> funext i
      · exact congrArg (fun b => b.2.1) (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))
      · exact congrArg (fun b => b.2.2) (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))

/-- The independent category weight factors into the three actual
Bernoulli subset weights, without a coupling assumption. -/
theorem independentCategoryMass_triple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → SplitCategories) :
    bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y =
      bernoulliSiteMass q ((categoryTripleEquiv ι y).1) *
      bernoulliSiteMass q ((categoryTripleEquiv ι y).2.1) *
      bernoulliSiteMass q ((categoryTripleEquiv ι y).2.2) :=
  independentCategoryProductMass_factor q y

/-- Exact real-test pushforward to the independent triple law. -/
theorem independentCategory_triple_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (F : (ι → Bool) → (ι → Bool) → (ι → Bool) → ℝ) :
    (∑ y, bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y *
      F ((categoryTripleEquiv ι y).1) ((categoryTripleEquiv ι y).2.1)
        ((categoryTripleEquiv ι y).2.2)) =
      ∑ c, ∑ e₁, ∑ e₂,
        bernoulliSiteMass q c * bernoulliSiteMass q e₁ * bernoulliSiteMass q e₂ * F c e₁ e₂ := by
  simp_rw [independentCategoryMass_triple]
  rw [(categoryTripleEquiv ι).sum_comp
    (fun x => bernoulliSiteMass q x.1 * bernoulliSiteMass q x.2.1 *
      bernoulliSiteMass q x.2.2 * F x.1 x.2.1 x.2.2)]
  simp only [Fintype.sum_prod_type]

theorem categoryPrimeProduct_eq_retained (Q : Finset ℕ) (y : Q → SplitCategories) :
    independentSplitProducts Q y =
      (retainedPrimeProduct Q ((categoryTripleEquiv Q y).1) *
        retainedPrimeProduct Q ((categoryTripleEquiv Q y).2.1),
       retainedPrimeProduct Q ((categoryTripleEquiv Q y).1) *
        retainedPrimeProduct Q ((categoryTripleEquiv Q y).2.2)) := by
  simp [independentSplitProducts, categoryPrimeProduct, retainedPrimeProduct,
    categoryTripleEquiv, categoryToTriple]

section Cutoff

variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

noncomputable def independentPairMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a b : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a * optionCellMass v (cell c) b

theorem independentPairMass_eq_triple (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a b : A) :
    independentPairMass w v cell a b =
      ∑ c, ∑ e₁, ∑ e₂,
        if cell c e₁ = some a ∧ cell c e₂ = some b then w c * v e₁ * v e₂ else 0 := by
  unfold independentPairMass optionCellMass
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e₁ _
  apply Finset.sum_congr rfl
  intro e₂ _
  by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [ha, hb]

/-- The discarded mass is the genuine union event, so overlap is counted once. -/
noncomputable def lowUnionExclusiveMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) : ℝ :=
  ∑ c, ∑ e₁, ∑ e₂,
    if (low e₁ ∨ low e₂) ∧ cell c e₁ = some a ∧ cell c e₂ = some b
      then w c * v e₁ * v e₂ else 0

/-- Conditional cell probability retaining only high exclusive products. -/
noncomputable def highExclusiveCell (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (c : C) (a : A) : ℝ :=
  optionCellMass (fun e => if low e then 0 else v e) (cell c) a

omit [Fintype C] in
theorem highExclusiveCell_eq_sum (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (c : C) (a : A) :
    highExclusiveCell v cell low c a =
      ∑ e, if ¬low e ∧ cell c e = some a then v e else 0 := by
  unfold highExclusiveCell optionCellMass
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : low e <;> by_cases hc : cell c e = some a <;> simp [hl, hc]

omit [Fintype C] in
theorem highExclusiveCell_nonneg (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (hv : ∀ e, 0 ≤ v e) (c : C) (a : A) :
    0 ≤ highExclusiveCell v cell low c a := by
  apply optionCellMass_nonneg
  intro e
  split_ifs <;> [exact le_rfl; exact hv e]

omit [Fintype C] in
theorem highExclusiveCell_le_one (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    (c : C) (a : A) : highExclusiveCell v cell low c a ≤ 1 := by
  rw [highExclusiveCell_eq_sum, ← hv1]
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> [exact le_rfl; exact hv e]

/-- The high-high complement factors after conditioning on the common variable. -/
theorem independentPairMass_cutoff (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) :
    independentPairMass w v cell a b = lowUnionExclusiveMass w v cell low a b +
      ∑ c, w c * highExclusiveCell v cell low c a * highExclusiveCell v cell low c b := by
  rw [independentPairMass_eq_triple]
  unfold lowUnionExclusiveMass
  simp_rw [highExclusiveCell_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm (f := fun e₂ e₁ =>
    w c * (if ¬low e₁ ∧ cell c e₁ = some a then v e₁ else 0) *
      (if ¬low e₂ ∧ cell c e₂ = some b then v e₂ else 0))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e₂ _
  by_cases hl₁ : low e₁ <;> by_cases hl₂ : low e₂ <;>
    by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [hl₁, hl₂, ha, hb]

theorem lowUnionExclusiveMass_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a b : A) :
    0 ≤ lowUnionExclusiveMass w v cell low a b := by
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro e₁ _
  apply Finset.sum_nonneg
  intro e₂ _
  split_ifs <;> [exact mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂); exact le_rfl]

/-- The low union is dominated by the two one-sided low kernels. -/
theorem lowUnionExclusiveMass_le_sides (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a b : A) :
    lowUnionExclusiveMass w v cell low a b ≤
      lowExclusiveMass w v cell low a b + lowExclusiveMass w v cell low b a := by
  rw [lowExclusiveMass_eq_triple, lowExclusiveMass_eq_triple]
  unfold lowUnionExclusiveMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.sum_comm (f := fun e₂ e₁ =>
    if low e₂ ∧ cell c e₁ = some a ∧ cell c e₂ = some b then w c * v e₁ * v e₂ else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e₂ _
  have h := mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)
  by_cases hl₁ : low e₁ <;> by_cases hl₂ : low e₂ <;>
    by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [hl₁, hl₂, ha, hb] <;> nlinarith

noncomputable def lowUnionExclusiveKernel (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (μ : A → ℝ) (a b : A) : ℝ := lowUnionExclusiveMass w v cell low a b / (μ a * μ b)

theorem lowUnionExclusiveKernel_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (μ : A → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hμ : ∀ a, 0 ≤ μ a) (a b : A) :
    0 ≤ lowUnionExclusiveKernel w v cell low μ a b :=
  div_nonneg (lowUnionExclusiveMass_nonneg w v cell low hw hv a b)
    (mul_nonneg (hμ a) (hμ b))

/-- Local marginal and conditional common-cell bounds control the actual
union kernel, including the overlap of its two low-exclusive events. -/
theorem lowUnionExclusiveKernel_weighted_rows [Fintype A]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {m H : ℝ} (hm : 0 < m)
    (hmarginal : ∀ a, independentCellMarginal w v cell a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H * m)
    (a : A) :
    (∑ b, m * lowUnionExclusiveKernel w v cell low (fun _ => m) a b) ≤
      2 * lowExclusiveProbability v low * H := by
  have hσ := lowExclusiveProbability_nonneg v low hv
  have he (b : A) : m * lowUnionExclusiveKernel w v cell low (fun _ => m) a b =
      lowUnionExclusiveMass w v cell low a b / m := by
    unfold lowUnionExclusiveKernel
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div]
  have hsum : (∑ b, lowUnionExclusiveMass w v cell low a b) ≤
      lowExclusiveProbability v low * independentCellMarginal w v cell a +
        lowExclusiveProbability v low * (H * m) := by
    calc
      _ ≤ ∑ b, (lowExclusiveMass w v cell low a b + lowExclusiveMass w v cell low b a) :=
        Finset.sum_le_sum fun b _ => lowUnionExclusiveMass_le_sides w v cell low hw hv a b
      _ = (∑ b, lowExclusiveMass w v cell low a b) +
          ∑ b, lowExclusiveMass w v cell low b a := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (lowExclusiveMass_row w v cell low hw hv a)
        (lowExclusiveMass_column w v cell low hw hv hv1 hcommon a)
  calc
    _ ≤ (lowExclusiveProbability v low * independentCellMarginal w v cell a +
        lowExclusiveProbability v low * (H * m)) / m := div_le_div_of_nonneg_right hsum hm.le
    _ ≤ (lowExclusiveProbability v low * (H * m) +
        lowExclusiveProbability v low * (H * m)) / m :=
      div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left (hmarginal a) hσ) le_rfl) hm.le
    _ = _ := by field_simp; ring

end Cutoff

noncomputable def primeProductCell {A : Type*} (Q : Finset ℕ) (cell : ℕ → Option A)
    (c e : Q → Bool) : Option A := cell (retainedPrimeProduct Q c * retainedPrimeProduct Q e)

/-- Exact cell-pair probabilities under the independent prime-category law. -/
theorem independentPrimeCellMass_eq_pair {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → Option A) (a b : A) :
    (∑ y, if cell (independentSplitProducts Q y).1 = some a ∧
        cell (independentSplitProducts Q y).2 = some b then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) =
      independentPairMass (bernoulliSiteMass q) (bernoulliSiteMass q)
        (primeProductCell Q cell) a b := by
  have h := independentCategory_triple_test q
    (fun c e₁ e₂ => if primeProductCell Q cell c e₁ = some a ∧
      primeProductCell Q cell c e₂ = some b then 1 else 0)
  rw [independentPairMass_eq_triple]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro y _
    rw [categoryPrimeProduct_eq_retained]
    change (if primeProductCell Q cell ((categoryTripleEquiv Q y).1)
        ((categoryTripleEquiv Q y).2.1) = some a ∧
      primeProductCell Q cell ((categoryTripleEquiv Q y).1)
        ((categoryTripleEquiv Q y).2.2) = some b then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) = _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro e₁ _
    apply Finset.sum_congr rfl
    intro e₂ _
    simp only [mul_ite, mul_one, mul_zero]

/-- Normalize the exact cutoff identity by the actual output cell masses. -/
theorem independentPairKernel_cutoff {C E D R : Type*}
    [Fintype C] [Fintype E] [DecidableEq D] [DecidableEq R]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option (D × R))
    (low : E → Prop) [DecidablePred low] (μ : D → ℝ) (a b : D × R) :
    independentPairMass w v cell a b / (μ a.1 * μ b.1) =
      lowUnionExclusiveKernel w v cell low (fun a : D × R => μ a.1) a b +
      exclusiveProductKernel w μ (highExclusiveCell v cell low) a b := by
  rw [independentPairMass_cutoff w v cell low a b]
  exact add_div _ _ _

/-- The independent category kernel has exactly the low-union plus
high-exclusive-product decomposition needed by residue flattening. -/
theorem independentPrimeKernel_cutoff {D R : Type*} [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → Option (D × R))
    (low : (Q → Bool) → Prop) [DecidablePred low] (μ : D → ℝ) (a b : D × R) :
    (∑ y, if cell (independentSplitProducts Q y).1 = some a ∧
        cell (independentSplitProducts Q y).2 = some b then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) /
        (μ a.1 * μ b.1) =
      lowUnionExclusiveKernel (bernoulliSiteMass q) (bernoulliSiteMass q)
        (primeProductCell Q cell) low (fun a : D × R => μ a.1) a b +
      exclusiveProductKernel (bernoulliSiteMass q) μ
        (highExclusiveCell (bernoulliSiteMass q) (primeProductCell Q cell) low) a b := by
  rw [independentPrimeCellMass_eq_pair]
  exact independentPairKernel_cutoff _ _ _ _ _ _ _

end JointDickman

end OAI
