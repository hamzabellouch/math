import OAI.Combinatorics.TreewidthL1.ExpandedPaths

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1.ExpandedTree
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I A : Type*} [Fintype I] [Fintype A]

noncomputable def marginalLaw (M : ℝ) (μ : I → A → ℝ) : I → A → ℝ := fun i a => μ i a/M
noncomputable def jointLaw (M : ℝ) (J : I → I → A → A → ℝ) := fun i j a b => J i j a b/M
lemma jointLaw_symm
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    (M : ℝ) (J : I → I → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : I => A) J) :
    TreeMarkov.Symmetric (fun _ : I => A) (jointLaw M J) := by
  intro i j a b
  unfold jointLaw
  rw [hs]
noncomputable def law (T : SimpleGraph I) (M : ℝ) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J) (x : I → A) : ℝ :=
  M * TreeMarkov.density (fun _ : I => A) T (marginalLaw M μ)
    (TreeMarkov.interaction (fun _ : I => A) (marginalLaw M μ) (jointLaw M J))
    (TreeMarkov.interaction_symmetric (fun _ : I => A) (marginalLaw M μ) (jointLaw M J) (jointLaw_symm M J hs)) x

lemma normalized (T : SimpleGraph I) (M : ℝ) (hM : 0 < M) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a) :
    TreeMarkov.Normalized (fun _ : I => A) T (marginalLaw M μ)
      (TreeMarkov.interaction (fun _ : I => A) (marginalLaw M μ) (jointLaw M J)) := by
  apply TreeMarkov.interaction_normalized
  · intro i a
    exact div_nonneg (hμ i a) hM.le
  · intro i
    simp only [marginalLaw, ← Finset.sum_div, hmass i, div_self (ne_of_gt hM)]
  · exact jointLaw_symm M J hs
  · intro i j hij a b
    exact div_nonneg (hJ i j hij a b) hM.le
  · intro i j hij a
    simp only [jointLaw, marginalLaw, ← Finset.sum_div, hrow i j hij a]

/-- The expanded-state law is an actual finite tree law of the original common
mass. All local state marginals are as prescribed; no gluing existence is assumed. -/
theorem law_marginals (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a) :
    (∀ x, 0 ≤ law T M μ J hs x) ∧ (∑ x, law T M μ J hs x) = M ∧
      ∀ i a, (∑ x : I → A, if x i = a then law T M μ J hs x else 0) = μ i a := by
  let ν := marginalLaw M μ
  let R := TreeMarkov.interaction (fun _ : I => A) ν (jointLaw M J)
  let hR := TreeMarkov.interaction_symmetric (fun _ : I => A) ν (jointLaw M J) (jointLaw_symm M J hs)
  have hn := normalized T M hM μ J hs hμ hmass hJ hrow
  obtain ⟨hw,ht,hm⟩ := TreeMarkov.tree_density (fun _ : I => A) T hT ν R hR hn
  refine ⟨fun x => mul_nonneg hM.le (hw x), ?_, ?_⟩
  · simp only [law, ← Finset.mul_sum]
    change M * (∑ x, TreeMarkov.density (fun _ : I => A) T ν R hR x) = M
    rw [ht,mul_one]
  · intro i a
    have he : (∑ x : I → A, if x i = a then law T M μ J hs x else 0) =
        M * (∑ x : I → A, if x i = a then TreeMarkov.density (fun _ : I => A) T ν R hR x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [law,ν,R]
    rw [he,hm]
    exact mul_div_cancel₀ (μ i a) (ne_of_gt hM)

lemma path_expectation (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a)
    {K : Type*} [Fintype K] (e : K ↪ I) (hc : (T.comap e).Connected) (f : (K → A) → ℝ) :
    (∑ x : I → A, law T M μ J hs x * f (x ∘ e)) =
      ∑ x : K → A, law (T.comap e) M (fun i => μ (e i)) (fun i j => J (e i) (e j))
        (fun i j => hs (e i) (e j)) x * f x := by
  unfold law
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  exact TreeMarkov.expectation_comap (fun _ : I => A) T hT (marginalLaw M μ) _ _
    (normalized T M hM μ J hs hμ hmass hJ hrow) e hc f

lemma support_joint (T : SimpleGraph I) (M : ℝ) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (x : I → A) (hx : law T M μ J hs x ≠ 0) (i j : I) (hij : T.Adj i j) :
    J i j (x i) (x j) ≠ 0 := by
  have hp := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2).2
  have he : s(i,j) ∈ T.edgeFinset := by simpa using hij
  have hz := Finset.prod_ne_zero_iff.mp hp _ he
  change J i j (x i) (x j) / M / ((μ i (x i)/M)*(μ j (x j)/M)) ≠ 0 at hz
  exact (div_ne_zero_iff.mp (div_ne_zero_iff.mp hz).1).1

/-- Gluing of GLOBAL state labels along the running-intersection bags. -/
noncomputable def assemble {V : Type*} (B : I → Set V) (hcover : ∀ v, ∃ i, v ∈ B i)
    (label : A → V → Bool) (x : I → A) : V → Bool :=
  fun v => label (x (Classical.choose (hcover v))) v

lemma assembled_label
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    {V : Type*} (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (label : A → V → Bool) (x : I → A)
    (hx : ∀ i j, T.Adj i j → ∀ v, v ∈ B i → v ∈ B j → label (x i) v = label (x j) v)
    (i : I) (v : V) (hv : v ∈ B i) : assemble B hcover label x v = label (x i) v := by
  obtain ⟨p⟩ := hrun v ⟨Classical.choose (hcover v),Classical.choose_spec (hcover v)⟩ ⟨i,hv⟩
  have hc : ∀ {a b : {i | v ∈ B i}} (q : (T.induce {i | v ∈ B i}).Walk a b),
      label (x a) v = label (x b) v := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a b c hab q ih => exact (hx a b hab v a.2 b.2).trans ih
  exact hc p

lemma law_labels {V : Type*} (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (M : ℝ) (μ : I → A → ℝ) (J : I → I → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : I => A) J) (label : A → V → Bool)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, J i j a b ≠ 0 →
      ∀ v, v ∈ B i → v ∈ B j → label a v = label b v)
    (x : I → A) (hx : law T M μ J hs x ≠ 0) (i : I) (v : V) (hv : v ∈ B i) :
    assemble B hcover label x v = label (x i) v := by
  exact assembled_label T B hcover hrun label x
    (fun i j hij => hcomp i j hij (x i) (x j) (support_joint T M μ J hs x hx i j hij)) i v hv

end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1.ExpandedTree
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A : Type*} [Fintype A]

/-- On every actual bag-tree path, the law is the genuine product of the
prescribed expanded couplings, even though their common mass is not one. -/
theorem law_path_product (M : ℝ) (hM : 0 < M) (μ : ℕ → A → ℝ)
    (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n a b, 0 ≤ Q n a b)
    (_ : ∀ n a, (∑ b, Q n a b) = μ n a)
    (hcol : ∀ n b, (∑ a, Q n a b) = μ (n+1) b)
    (n : ℕ) (J : Fin (n+1) → Fin (n+1) → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : Fin (n+1) => A) J)
    (hJ : ∀ (i : Fin n) a b, J i.castSucc i.succ a b = Q i.val a b) (x : Fin (n+1) → A) :
    law (SimpleGraph.pathGraph (n+1)) M (fun i => μ i.val) J hs x =
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x := by
  unfold law
  rw [TreeMarkov.path_density]
  let m : Fin (n+1) → ℝ := fun i => μ i.val (x i)/M
  let q : Fin n → ℝ := fun i =>
    TreeMarkov.interaction (fun _ : Fin (n+1) => A) (marginalLaw M (fun i => μ i.val))
      (jointLaw M J) i.castSucc i.succ (x i.castSucc) (x i.succ)
  let k : Fin n → ℝ := fun i => MarkovProduct.couplingKernel (fun _ => A) μ Q i.val
    (x i.castSucc) (x i.succ)
  have hk (i : Fin n) (hi : m i.castSucc ≠ 0) : k i = m i.succ * q i := by
    have hi' : μ i.val (x i.castSucc) ≠ 0 := by
      intro hz
      exact hi (by simp [m,hz])
    by_cases hj : μ (i.val+1) (x i.succ) = 0
    · have hz : Q i.val (x i.castSucc) (x i.succ) = 0 := by
        have hh := hcol i.val (x i.succ)
        rw [hj] at hh
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hQ i.val a (x i.succ))).mp hh _ (Finset.mem_univ _)
      simp [k, MarkovProduct.couplingKernel,hi',hz,m,hj]
    · dsimp [k,m,q]
      simp only [MarkovProduct.couplingKernel, hi', ↓reduceIte, TreeMarkov.interaction,
        marginalLaw, jointLaw, hJ, Fin.val_castSucc, Fin.val_succ]
      field_simp [hi',hj,ne_of_gt hM]
  have he := TreeMarkov.product_factorization n m q k hk
  change M * ((∏ i, m i)*(∏ i, q i)) = _
  rw [he]
  unfold MarkovProduct.weight
  change M * ((μ 0 (x 0)/M) * ∏ i, k i) = μ 0 (x 0) * ∏ i, k i
  rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hM)]
end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1
open MeasureTheory
open scoped ENNReal

theorem averaged_cut_realization {Ω V A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) (w : Ω → A → ℝ) (cut : A → V → Bool)
    (hw : ∀ ω a, 0 ≤ w ω a)
    (hint : ∀ a, Integrable (fun ω => w ω a) μ) :
    ∃ n : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      ∀ u v, ‖F u - F v‖ = ∫ ω, cutDistance (w ω) cut u v ∂μ := by
  let W : A → ℝ := fun a => ∫ ω, w ω a ∂μ
  have hW : ∀ a, 0 ≤ W a := fun a => integral_nonneg (fun ω => hw ω a)
  obtain ⟨n,F,hF⟩ := finite_cut_realization W cut hW
  refine ⟨n,F,?_⟩
  intro u v
  rw [hF]
  unfold cutDistance
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases he : cut a u = cut a v <;> simp [he, W]
  · intro a ha
    by_cases he : cut a u = cut a v
    · simp only [he, ite_true]
      exact integrable_zero Ω ℝ μ
    · simpa only [he, ite_false] using hint a
end BoundedTreewidthL1

end OAI
