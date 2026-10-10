import OAI.Probability.DilutedSpin.HistoryGeometry
import OAI.Probability.DilutedSpin.ShapeMean

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance instDecidableSplitDepthContinuity
    (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Divergence from one referenced leaf, with every old child retained. -/
noncomputable def pairDivergence : {n : ℕ} → (S : PrescribedTree n) →
    S.Leaf → (d : ℕ) → d < n → Divergence S
  | _+1, .node _ _, a, 0, _ => .here {a.1}
  | _+1, .node _ C, a, d+1, hd => .descend a.1 (pairDivergence (C a.1) a.2 d (by omega))

lemma pairDivergence_coefficient {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (pairDivergence S a d hd).coefficient m =
      m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero => simp [pairDivergence,Divergence.coefficient]
    | succ d => exact ih a.1 a.2 d (by omega) (fun j => m j.succ)

lemma pairDivergence_old {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).oldAllowed b ↔ splitDepth S a b = d := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    cases d with
    | zero =>
      change j ∉ ({i} : Finset (Fin k)) ↔ _
      simp only [Finset.mem_singleton]
      by_cases h : i = j
      · subst j; rw [splitDepth_same_child]; simp
      · rw [splitDepth_diff_child C i j h]; simp [Ne.symm h]
    | succ d =>
      change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).oldAllowed (h ▸ b)) ↔ _
      by_cases h : j = i
      · subst j
        simp only [exists_const,splitDepth_same_child]
        rw [ih i a b d (by omega)]
        omega
      · rw [splitDepth_diff_child C i j (Ne.symm h)]
        constructor
        · rintro ⟨he,_⟩; exact (h he).elim
        · intro he; omega

lemma pairDivergence_fresh {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (v : S.Internal) (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).freshAllowed v ↔ freshSplitDepth S v a = d := by
  induction S generalizing d with
  | leaf => exact v.elim
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    change Option ((j : Fin k) × (C j).Internal) at v
    cases d with
    | zero =>
      cases v with
      | none => change True ↔ 0 = 0; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change j ∉ ({i} : Finset (Fin k)) ↔ _
        simp only [Finset.mem_singleton]
        exact ne_comm.trans (freshSplitDepth_node_zero C j v ⟨i,a⟩).symm
    | succ d =>
      cases v with
      | none => change False ↔ 0 = d+1; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).freshAllowed (h ▸ v)) ↔ _
        by_cases h : j = i
        · subst j
          simp only [exists_const,freshSplitDepth_same_child]
          rw [ih i a v d (by omega)]
          omega
        · rw [freshSplitDepth_diff_child C j i (Ne.symm h)]
          constructor
          · rintro ⟨he,_⟩; exact (h he).elim
          · intro he; omega

/-- Exact signed total of every path splitting from the anchor at d. -/
theorem pair_choice_total {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0) +
      (∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
        then gamma S m v else 0) = m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  simp_rw [splitDepth_symm (grow S _) (oldLeaf S _ a),splitDepth_new_old,
    ← pairDivergence_old S a _ d hd,← pairDivergence_fresh S a _ d hd]
  rw [divergence_choice_total _ m hend,pairDivergence_coefficient]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- Add an actual unary initial stem, preserving all descendant geometry. -/
def stem (S : PrescribedTree n) : (r : ℕ) → PrescribedTree (n+r)
  | 0 => S
  | r+1 => unary (stem S r)

/-- A literal family with one ranged split. The child shapes and all their
later branching depths are fixed. Moving d delays only this split. -/
def splitFamily (k : ℕ+) (C : Fin k → PrescribedTree n) :
    (r : ℕ) → Fin (r+1) → PrescribedTree (n+r+1)
  | 0, _ => .node k C
  | r+1, d => Fin.cases (.node k (fun i => stem (C i) (r+1)))
      (fun j => unary (splitFamily k C r j)) d

@[simp] lemma splitFamily_zero (k : ℕ+) (C : Fin k → PrescribedTree n) (r : ℕ) :
    splitFamily k C r 0 = .node k (fun i => stem (C i) r) := by
  cases r <;> rfl

@[simp] lemma splitFamily_succ (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (d : Fin (r+1)) : splitFamily k C (r+1) d.succ = unary (splitFamily k C r d) := rfl

/-- On one real kernel path, retain its prefix and compute the true mean of
its descendant shape. Omitted sampled branches have integrated to one. -/
noncomputable def tailMean (S : PrescribedTree n) : (r : ℕ) → KernelTower Ω (n+r) →
    (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0, T, f, _ => treeMean S T f
  | r+1, T, f, x => tailMean S r (T.2 x.1) (fun y => f (x.1,y)) x.2

lemma tailMean_bound (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : FinitePath Ω (n+r)) :
    |tailMean S r T f x| ≤ 1 := by
  induction r with
  | zero => exact treeMean_bound S T hf
  | succ r ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

lemma tailMean_expect (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) :
    (KernelTower.law (n+r) T).expect (tailMean S r T f) = treeMean (stem S r) T f := by
  induction r with
  | zero => exact FiniteLaw.expect_const _ _
  | succ r ih =>
    have he := KernelTower.law_succ_expect (Ω := Ω) (n+r) T (tailMean S (r+1) T f)
    calc
      _ = _ := he
      _ = _ := by
        simp only [stem,treeMean_unary,tailMean]
        exact T.1.expect_congr (fun a => ih (T.2 a) (fun y => f (a,y)))

noncomputable def tailVariance (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) : ℝ :=
  (KernelTower.law (n+r) T).covariance (tailMean S r T f) (tailMean S r T f)

lemma tailVariance_nonneg (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) : 0 ≤ tailVariance S r T f :=
  FiniteLaw.covariance_self_nonneg _ _

lemma tailVariance_le_one (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x| ≤ 1) : tailVariance S r T f ≤ 1 :=
  FiniteLaw.covariance_self_le_one _ (tailMean_bound S r T f hf)

lemma tailVariance_step (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r+1))
    (f : FinitePath Ω (n+r+1) → ℝ) :
    tailVariance S (r+1) T f =
      T.1.covariance (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y))) +
      T.1.expect (fun a => tailVariance S r (T.2 a) (fun y => f (a,y))) := by
  have h := T.1.variance_bind (fun a => KernelTower.law (n+r) (T.2 a)) (tailMean S (r+1) T f)
  change tailVariance S (r+1) T f = _ at h
  simp only [tailMean,tailMean_expect] at h
  convert h using 1
  rw [add_comm]
  rfl

/-- The sum of squared changes of the actual descendant mean when one split
is ranged over ALL available depths, with arbitrary fixed later child shapes. -/
noncomputable def splitShiftEnergy (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) : ℝ :=
  ∑ d : Fin r, (treeMean (splitFamily k C r d.castSucc) T f -
    treeMean (splitFamily k C r d.succ) T f)^2

lemma splitShiftEnergy_step_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+2)) (f : FinitePath Ω (n+r+2) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    splitShiftEnergy k C (r+1) T f ≤
      (k:ℝ)*∑ i, T.1.covariance
        (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y))) +
      T.1.expect (fun a => splitShiftEnergy k C r (T.2 a) (fun y => f (a,y))) := by
  unfold splitShiftEnergy
  rw [Fin.sum_univ_succ]
  have hi := treeMean_one_vertex_shift k (fun i => stem (C i) r) T f hf
  apply add_le_add
  · simp only [Fin.castSucc_zero,splitFamily_zero,splitFamily_succ,stem]
    convert hi using 1
  · rw [FiniteLaw.expect_fintype_sum]
    apply Finset.sum_le_sum
    intro d _
    simp only [Fin.castSucc_succ,splitFamily_succ,treeMean_unary]
    have h := T.1.sq_expect_le_expect_sq (fun a =>
      treeMean (splitFamily k C r d.castSucc) (T.2 a) (fun y => f (a,y)) -
      treeMean (splitFamily k C r d.succ) (T.2 a) (fun y => f (a,y)))
    rwa [FiniteLaw.expect_sub] at h

 
theorem splitShiftEnergy_le_variance (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    splitShiftEnergy k C r T f ≤ (k:ℝ)*∑ i, tailVariance (C i) (r+1) T f := by
  induction r with
  | zero =>
    simp only [splitShiftEnergy,Finset.univ_eq_empty,Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => tailVariance_nonneg _ _ _ _))
  | succ r ih =>
    calc
      _ ≤ _ := splitShiftEnergy_step_le k C r T f hf
      _ ≤ (k:ℝ)*∑ i, T.1.covariance
          (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y)))
          (fun a => treeMean (stem (C i) (r+1)) (T.2 a) (fun y => f (a,y))) +
          T.1.expect (fun a => (k:ℝ)*∑ i, tailVariance (C i) (r+1) (T.2 a) (fun y => f (a,y))) :=
        add_le_add le_rfl (T.1.expect_mono (fun a => ih (T.2 a) (fun y => f (a,y))
          (fun y => hf (a,y))))
      _ = _ := by
        conv_rhs => arg 2; arg 2; ext i; rw [tailVariance_step (C i) (r+1)]
        rw [Finset.sum_add_distrib,FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum,mul_add]

theorem splitShiftEnergy_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : splitShiftEnergy k C r T f ≤ (k:ℝ)^2 := by
  refine (splitShiftEnergy_le_variance k C r T f hf).trans ?_
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => tailVariance_le_one (C i) (r+1) T f hf))
    (show (0:ℝ) ≤ k by positivity)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,pow_two] using h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
