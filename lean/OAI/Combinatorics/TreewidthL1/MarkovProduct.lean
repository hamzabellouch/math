import OAI.Combinatorics.TreewidthL1.ReservedTests

namespace OAI

universe treewidthLevel1

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]
abbrev History (n : ℕ) := (i : Fin (n+1)) → L i.val
noncomputable def weight (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (x : History L n) : ℝ :=
  p (x 0) * ∏ i : Fin n, K i.val (x i.castSucc) (x i.succ)
noncomputable def forward (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ) :
    (n : ℕ) → L n → ℝ
  | 0 => p
  | n+1 => fun b => ∑ a, forward p K n a * K n a b

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

lemma weight_snoc
    (L : ℕ → Type treewidthLevel1) [(i : ℕ) → Fintype (L i)]
    (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (x : History L n) (b : L (n+1)) :
    weight L p K (n+1) (Fin.snoc x b) = weight L p K n x * K n (x (Fin.last n)) b := by
  classical
  unfold weight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_last, Fin.snoc_last, ← Fin.castSucc_succ,
    Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last]
  change p (@Fin.snoc (n+1) (fun i : Fin (n+2) => L i.val) x b ((0 : Fin (n+1)).castSucc)) * _ = _
  rw [Fin.snoc_castSucc]
  ring

lemma sum_history_snoc (n : ℕ) (f : History L (n+1) → ℝ) :
    (∑ x, f x) = ∑ b : L (n+1), ∑ x : History L n, f (Fin.snoc x b) := by
  classical
  rw [← (Fin.snocEquiv (fun i : Fin (n+2) => L i.val)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

lemma terminal_marginal (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (b : L n) :
    (∑ x : History L n, if x (Fin.last n) = b then weight L p K n x else 0) =
      forward L p K n b := by
  classical
  induction n with
  | zero =>
    let he : L 0 ≃ History L 0 := (Equiv.piUnique (fun i : Fin 1 => L i.val)).symm
    rw [← he.sum_comp]
    simp [he, weight, forward, Equiv.piUnique, uniqueElim]
  | succ n ih =>
    rw [sum_history_snoc]
    simp only [Fin.snoc_last, weight_snoc]
    have h : (∑ c : L (n+1), ∑ x : History L n,
        if c = b then weight L p K n x * K n (x (Fin.last n)) c else 0) =
        ∑ x : History L n, weight L p K n x * K n (x (Fin.last n)) b := by simp
    rw [h]
    unfold forward
    conv_rhs =>
      simp only [← ih, Finset.sum_mul]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [ite_mul, zero_mul]
    simp

lemma forward_total (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hK₁ : ∀ i a, (∑ b, K i a b) = 1) (n : ℕ) :
    (∑ a, forward L p K n a) = ∑ a, p a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [forward]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hK₁, mul_one]
    exact ih

/-- Normalization and the exact terminal marginal of the product measure. -/
theorem product_law (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : (∑ a, p a) = 1)
    (hK : ∀ i a b, 0 ≤ K i a b) (hK₁ : ∀ i a, (∑ b, K i a b) = 1) (n : ℕ) :
    (∀ x, 0 ≤ weight L p K n x) ∧ (∑ x, weight L p K n x) = 1 ∧
      ∀ b : L n, (∑ x : History L n, if x (Fin.last n) = b then weight L p K n x else 0) =
        forward L p K n b := by
  classical
  refine ⟨fun x => mul_nonneg (hp _) (Finset.prod_nonneg fun _ _ => hK _ _ _), ?_,
    terminal_marginal L p K n⟩
  have ht := forward_total L p K hK₁ n
  simp_rw [← terminal_marginal L p K n] at ht
  rw [Finset.sum_comm] at ht
  simpa [hp₁] using ht

/-- The product has its prescribed final adjacent-pair marginal, including
zero-probability states and transitions. -/
theorem last_pair (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (a : L n) (b : L (n+1)) :
    (∑ x : History L (n+1),
      if x (Fin.last n).castSucc = a ∧ x (Fin.last (n+1)) = b
      then weight L p K (n+1) x else 0) = forward L p K n a * K n a b := by
  classical
  rw [sum_history_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, weight_snoc]
  rw [Finset.sum_comm]
  have hc (x : History L n) :
      (∑ c : L (n+1), if x (Fin.last n) = a ∧ c = b
        then weight L p K n x * K n (x (Fin.last n)) c else 0) =
      (if x (Fin.last n) = a then weight L p K n x else 0) * K n a b := by
    by_cases h : x (Fin.last n) = a <;> simp [h]
  simp only [hc, ← Finset.sum_mul, terminal_marginal]

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

/-- Transition obtained from a prescribed adjacent-pair marginal. A zero-mass
row is filled with the next marginal; the row is never visited. -/
noncomputable def couplingKernel (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (i : ℕ) (a : L i) (b : L (i+1)) : ℝ :=
  if μ i a = 0 then μ (i+1) b else J i a b / μ i a

noncomputable def historyPrefix (m n : ℕ) (h : m ≤ n) (x : History L n) : History L m :=
  fun i => x (i.castLE (Nat.succ_le_succ h))

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

lemma joint_zero_row (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (i : ℕ) (a : L i) (ha : μ i a = 0) (b : L (i+1)) : J i a b = 0 := by
  have hle : J i a b ≤ ∑ c, J i a c :=
    Finset.single_le_sum (fun c _ => hJ i a c) (Finset.mem_univ b)
  rw [hrow, ha] at hle
  exact le_antisymm hle (hJ i a b)

lemma couplingKernel_stochastic (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a) :
    (∀ i a b, 0 ≤ couplingKernel L μ J i a b) ∧
      ∀ i a, (∑ b, couplingKernel L μ J i a b) = 1 := by
  constructor
  · intro i a b
    unfold couplingKernel
    split
    · exact hμ _ _
    · exact div_nonneg (hJ _ _ _) (hμ _ _)
  · intro i a
    by_cases ha : μ i a = 0
    · simp [couplingKernel, ha, hμ₁]
    · simp [couplingKernel, ha, ← Finset.sum_div, hrow]

lemma couplingKernel_balance (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (i : ℕ) (a : L i) (b : L (i+1)) :
    μ i a * couplingKernel L μ J i a b = J i a b := by
  by_cases ha : μ i a = 0
  · simp [couplingKernel, ha, joint_zero_row L μ J hJ hrow i a ha b]
  · simp [couplingKernel, ha, field]

lemma coupling_forward (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (hcol : ∀ i b, (∑ a, J i a b) = μ (i+1) b) :
    ∀ n a, forward L (μ 0) (couplingKernel L μ J) n a = μ n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro b
    simp only [forward, ih, couplingKernel_balance L μ J hJ hrow]
    exact hcol n b

lemma prefix_snoc
    (L : ℕ → Type treewidthLevel1) [(i : ℕ) → Fintype (L i)]
    {m n : ℕ} (h : m ≤ n) (x : History L n) (b : L (n+1)) :
    historyPrefix L m (n+1) (h.trans (Nat.le_succ n)) (Fin.snoc x b) = historyPrefix L m n h x := by
  funext i
  change (@Fin.snoc (n+1) (fun j : Fin (n+2) => L j.val) x b)
    (Fin.castSucc (i.castLE (Nat.succ_le_succ h))) = _
  rw [Fin.snoc_castSucc]
  rfl

/-- Integrating out a stochastic suffix preserves the complete historyPrefix law,
not only one-coordinate marginals. -/
lemma prefix_expectation (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hK₁ : ∀ i a, (∑ b, K i a b) = 1)
    (m n : ℕ) (hmn : m ≤ n) (f : History L m → ℝ) :
    (∑ x : History L n, weight L p K n x * f (historyPrefix L m n hmn x)) =
      ∑ x : History L m, weight L p K m x * f x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    rw [sum_history_snoc]
    simp only [weight_snoc, prefix_snoc L h]
    rw [Finset.sum_comm]
    have hs (x : History L n) :
        (∑ b : L (n+1), weight L p K n x * K n (x (Fin.last n)) b *
          f (historyPrefix L m n h x)) = weight L p K n x * f (historyPrefix L m n h x) := by
      simp_rw [mul_assoc, mul_comm (K n (x (Fin.last n)) _), ← mul_assoc]
      rw [← Finset.mul_sum, hK₁, mul_one]
    simp only [hs]
    exact ih

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

theorem coupling_chain (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (hcol : ∀ i b, (∑ a, J i a b) = μ (i+1) b) (n : ℕ) :
    (∀ x, 0 ≤ weight L (μ 0) (couplingKernel L μ J) n x) ∧
    (∑ x, weight L (μ 0) (couplingKernel L μ J) n x) = 1 ∧
    ∀ i : Fin n, ∀ a : L i.val, ∀ b : L (i.val+1),
      (∑ x : History L n,
        if x i.castSucc = a ∧ x i.succ = b
        then weight L (μ 0) (couplingKernel L μ J) n x else 0) = J i.val a b := by
  have hK := couplingKernel_stochastic L μ J hμ hμ₁ hJ hrow
  have hlaw := product_law L (μ 0) (couplingKernel L μ J) (hμ 0) (hμ₁ 0) hK.1 hK.2 n
  refine ⟨hlaw.1, hlaw.2.1, ?_⟩
  intro i a b
  let f : History L (i.val+1) → ℝ := fun x =>
    if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b then 1 else 0
  have he := prefix_expectation L (μ 0) (couplingKernel L μ J) hK.2
    (i.val+1) n i.isLt f
  have he' :
      (∑ x : History L n, if x i.castSucc = a ∧ x i.succ = b
        then weight L (μ 0) (couplingKernel L μ J) n x else 0) =
      ∑ x : History L (i.val+1),
        if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b
        then weight L (μ 0) (couplingKernel L μ J) (i.val+1) x else 0 := by
    change (∑ x : History L n, weight L (μ 0) (couplingKernel L μ J) n x *
      (if x i.castSucc = a ∧ x i.succ = b then 1 else 0)) =
      (∑ x : History L (i.val+1), weight L (μ 0) (couplingKernel L μ J) (i.val+1) x *
      (if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b then 1 else 0)) at he
    simpa only [mul_ite, mul_one, mul_zero] using he
  rw [he', last_pair, coupling_forward L μ J hJ hrow hcol]
  exact couplingKernel_balance L μ J hJ hrow i.val a b

end BoundedTreewidthL1.MarkovProduct

end OAI
