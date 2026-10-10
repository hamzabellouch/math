import OAI.Probability.DilutedSpin.ProperChildScheduleContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Conditional scheduled-tree mean after a genuine sampled prefix. The
terminal reserve n is held fixed and the evaluation depth ranges over the
first r transitions. No unobserved ancestral variable is resampled. -/
noncomputable def scheduledPrefixMean (n : ℕ) : (r d : ℕ) → Fin (r+1) →
    (S : ReducedTopology) → (S.Vertex → ℕ) → KernelTower Ω (n+r) →
    (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0,d,_,S,q,T,f,_ => PrescribedTree.treeMean (realize n d S q) T f
  | r+1,d,e,S,q,T,f,x => Fin.cases
      (PrescribedTree.treeMean (realize (n+r+1) d S q) T f)
      (fun e => scheduledPrefixMean n r (d+1) e S q (T.2 x.1) (fun y => f (x.1,y)) x.2) e

@[simp] lemma scheduledPrefixMean_zero (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    scheduledPrefixMean n r d 0 S q T f x=PrescribedTree.treeMean (realize (n+r) d S q) T f := by
  cases r <;> rfl

/-- Before the first child branching the literal scheduled conditional mean
is exactly the martingale used in the energy theorem. All later assigned
depths stay fixed in this identity. -/
lemma scheduledPrefixMean_eq_stemMeanAt (n r d : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (hq : ∀ v, d+r≤q v) (e : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    scheduledPrefixMean n r d e S q T f x=
      PrescribedTree.stemMeanAt (realize n (d+r) S q) r e T f x := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · rw [scheduledPrefixMean_zero,PrescribedTree.stemMeanAt_zero,realize_stem n (r+1) d S q hq]
    · change scheduledPrefixMean n r (d+1) e S q (T.2 x.1) (fun y => f (x.1,y)) x.2=
        PrescribedTree.stemMeanAt (realize n (d+(r+1)) S q) r e (T.2 x.1) (fun y => f (x.1,y)) x.2
      have hh := ih (d+1) (fun v => by have := hq v; omega) e (T.2 x.1) (fun y => f (x.1,y)) x.2
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Ranged proper-child conditional product in the actual scheduled shape. -/
noncomputable def scheduledProductMean {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (e : Fin (r+1)) (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ)
    (x : FinitePath Ω (n+r)) (i : Fin N) : ℝ :=
  ∏ j, scheduledPrefixMean n r d e (C j) (q j) T (fun y => f y i) x

lemma scheduledProductMean_eq {ι : Type*} [Fintype ι]
    (n r d : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (hq : ∀ j v, d+r≤q j v) (e : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    scheduledProductMean n r d C q e T f=
      PrescribedTree.productStemMeanAt (fun j => realize n (d+r) (C j) (q j)) r e T f := by
  funext x i
  unfold scheduledProductMean PrescribedTree.productStemMeanAt
  apply Finset.prod_congr rfl
  intro j _
  exact scheduledPrefixMean_eq_stemMeanAt n r d (C j) (q j) (hq j) e T _ x

/-- The evaluation component of h_N on the exact scheduled proper-child
family, with later branching depths fixed and arbitrary allowed evaluation
subsets. Targets and anchors may vary with the evaluation coordinate. -/
theorem scheduled_target_evaluation_cost_le {ι : Type*} [Fintype ι]
    (n r d L : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (hq : ∀ j v, d+r≤q j v) (U : Finset (Fin r))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Target : Fin r → PrescribedTree (n+r)) (a b : (e : Fin r) → (Target e).Leaf) :
    (∑ e ∈ U, PrescribedTree.targetContractionChangeSq (Target e) T (a e) (b e)
      (scheduledProductMean n r d C q e.succ T f)
      (scheduledProductMean n r d C q e.castSucc T f))/(L:ℝ) ≤
      4*(Fintype.card ι:ℝ)^2/(L:ℝ) := by
  simp_rw [scheduledProductMean_eq n r d C q hq]
  exact PrescribedTree.averaged_target_evaluation_change_le
    (fun j => realize n (d+r) (C j) (q j)) r L U T f hf Target a b

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
