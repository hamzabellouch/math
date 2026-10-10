import OAI.Probability.DilutedSpin.ActualNegligible
import OAI.Probability.DilutedSpin.HistorySelector
import OAI.Probability.DilutedSpin.LabeledColorHistory
import OAI.Probability.DilutedSpin.SelectorPolarization
import OAI.Probability.DilutedSpin.ShapeCharging

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

omit [Fintype Ω] in
lemma labeledHistory_add (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => V S pos f + W S pos f) cs S U loc pos f =
      labeledHistory m V cs S U loc pos f + labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_add,Finset.sum_add_distrib]
    ring

omit [Fintype Ω] in
lemma labeledHistory_mul_left (m : Fin (n+1) → ℝ) (t : ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => t * V S pos f) cs S U loc pos f =
      t * labeledHistory m V cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring

omit [Fintype Ω] in
lemma labeledHistory_zero (m : Fin (n+1) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun _ _ _ => 0) cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih => simp only [labeledHistory,ih,mul_zero,Finset.sum_const_zero,add_zero]

omit [Fintype Ω] in
lemma labeledHistory_sum {J : Type} (F : Finset J) (m : Fin (n+1) → ℝ)
    (V : J → (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => ∑ j ∈ F, V j S pos f) cs S U loc pos f =
      ∑ j ∈ F, labeledHistory m (V j) cs S U loc pos f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,labeledHistory_zero]
  | @insert j F hj ih => simp only [Finset.sum_insert hj,labeledHistory_add,ih]

/-- Averaging the independent insertion site gives exactly the multioverlap
inside each signed history, with no distinct-site restriction. -/
theorem constrainedHistory_site_average {k : ℕ} {R J : Type} [Fintype R] [DecidableEq R]
    [Fintype J] (weights : J → ℝ) (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : J → Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) (f : Sample Ω S → ℝ) :
    (∑ i, weights i * constrainedHistory T m a b d (spinColor i) S anchor f) =
    labeledHistory m (fun S pos f =>
      (S.sampleLaw T).expect
        (fun x => f x * ∑ i, weights i * ∏ c, spinColor i c (S.pathAt (pos c) x)) *
      ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
      (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S
      (Finset.univ.erase anchor) id (fun _ => anchor) f := by
  classical
  unfold constrainedHistory
  simp_rw [← labeledHistory_mul_left]
  rw [← labeledHistory_sum]
  apply congrArg (fun V => labeledHistory m V _ S (Finset.univ.erase anchor) id (fun _ => anchor) f)
  funext S pos f
  simp only [Finset.mul_sum,FiniteLaw.expect_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← FiniteLaw.expect_mul_left]
  congr 1
  apply FiniteLaw.expect_congr
  intro x
  ring

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype Ω] [Fintype C] in
lemma labeledHistory_sub (m : Fin (L+1) → ℝ)
    (V W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos g-W R pos g) cs S U loc pos f =
      labeledHistory m V cs S U loc pos f-labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_sub,Finset.sum_sub_distrib]
    ring

/-- The genuine signed history of an L2 projection error has the exact
small-L charging cost. The target error need only be small under its own
single-copy law; it may be correlated with every old path and old test. -/
theorem projection_history_cost (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (D : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*D (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  refine prescribed_history_charging_bound hL Q T S q hq hS _ _
    (FiniteLaw.l2_nonneg _ _) ?_ cs U loc pos f hf hU
  intro R pos g hg h
  exact matrix_weighted_error T R q hq pos h K D g hg

/-- Direct comparison of an actual target overlap with its projected
observable inside the full signed ordered extension sum. -/
theorem projection_history_difference (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (A B : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f -
     labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => A (fun c => T.pathAt (q c) x)-B (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  rw [← labeledHistory_sub]
  have he : (fun (R : PrescribedTree L) (pos : C → R.Leaf) (g : Sample Ω R → ℝ) =>
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)-
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)) =
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*(A (fun c => R.pathAt (pos c) x)-
          B (fun c => R.pathAt (pos c) x))) else 0) := by
    funext R pos g
    split_ifs <;> simp only [sub_self,mul_sub,FiniteLaw.expect_sub]
  rw [he]
  exact projection_history_cost hL Q T S q hq hS K (fun x => A x-B x) cs U loc pos f hf hU

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
lemma expect_pi_three (P : (i : ι) → FiniteLaw (α i)) (i j k : ι)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) (f : α i → α j → α k → ℝ) :
    (pi P).expect (fun x => f (x i) (x j) (x k)) =
      (P i).expect (fun x => (P j).expect (fun y => (P k).expect (f x y))) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hji,dite_eq_right hki]
  exact expect_pi_pair (fun t : {t // t ≠ i} => P t) ⟨j,hji⟩ ⟨k,hki⟩
    (fun he => hkj (congrArg Subtype.val he)) (f x)
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
noncomputable def tripleExpectAt : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, F => F () () ()
  | n+1, T, 0, F => (law (n+1) T).expect (fun x => (law (n+1) T).expect
      (fun y => (law (n+1) T).expect (F x y)))
  | n+1, T, d+1, F => T.1.expect (fun z => tripleExpectAt n (T.2 z) d
      (fun x y w => F (z,x) (z,y) (z,w)))

lemma tripleExpectAt_eq (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (F : FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → ℝ) :
    tripleExpectAt (h+1+d) T d F = tripleExpect h d T F := by
  induction d with
  | zero => rfl
  | succ d ih => exact T.1.expect_congr (fun z => ih (T.2 z) (fun x y w => F (z,x) (z,y) (z,w)))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
lemma branch_leaf_marginal {n : ℕ} (C : PrescribedTree n) (μ : FiniteLaw Ω)
    (K : Ω → KernelTower Ω n) (a : C.Leaf) (F : FinitePath Ω (n+1) → ℝ) :
    (μ.bind (fun z => C.sampleLaw (K z))).expect
      (fun x => F (x.1,C.pathAt a x.2)) = (KernelTower.law (n+1) (μ,K)).expect F := by
  erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect n (μ,K)]
  exact μ.expect_congr (fun z => leaf_marginal C (K z) a (fun y => F (z,y)))

/-- Every uncontracted tree with three positional pairwise split depths equal
to d has the genuine three-copy conditional marginal. All other branches are
integrated out, irrespective of their number or depths. -/
theorem triple_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b c : S.Leaf) (d : ℕ) (hd : d < n)
    (hab : splitDepth S a b = d) (hac : splitDepth S a c = d)
    (hbc : splitDepth S b c = d)
    (F : FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => F (S.pathAt a x) (S.pathAt b x) (S.pathAt c x)) =
      KernelTower.tripleExpectAt n T d F := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    rcases c with ⟨l,c⟩
    cases d with
    | zero =>
      have hji : j ≠ i := by
        intro hj; subst j
        rw [splitDepth_same_child] at hab
        omega
      have hli : l ≠ i := by
        intro hl; subst l
        rw [splitDepth_same_child] at hac
        omega
      have hlj : l ≠ j := by
        intro hl; subst l
        rw [splitDepth_same_child] at hbc
        omega
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)
          ((x l).1,(C l).pathAt c (x l).2)) = _
      refine (FiniteLaw.expect_pi_three
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j l hji hli hlj
        (fun x y z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2)
          (z.1,(C l).pathAt c z.2))).trans ?_
      change _ = (KernelTower.law (n+1) (μ,K)).expect (fun x =>
        (KernelTower.law (n+1) (μ,K)).expect (fun y =>
          (KernelTower.law (n+1) (μ,K)).expect (F x y)))
      calc
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (μ.bind (fun z => sampleLaw (C j) (K z))).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z =>
              F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z))) := by
          apply FiniteLaw.expect_congr; intro x
          apply FiniteLaw.expect_congr; intro y
          exact branch_leaf_marginal (C l) μ K c
            (fun z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z)
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))) := by
          apply FiniteLaw.expect_congr; intro x
          exact branch_leaf_marginal (C j) μ K b (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))
        _ = _ := branch_leaf_marginal (C i) μ K a (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (F x y)))
    | succ d =>
      have hji : j = i := by
        by_contra hj
        rw [splitDepth_diff_child C i j (Ne.symm hj)] at hab
        omega
      have hli : l = i := by
        by_contra hl
        rw [splitDepth_diff_child C i l (Ne.symm hl)] at hac
        omega
      subst j; subst l
      rw [splitDepth_same_child] at hab hac hbc
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)
          ((x i).1,(C i).pathAt c (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => F (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2)
          (x.1,(C i).pathAt c x.2))).trans ?_
      rw [FiniteLaw.expect_bind]
      exact μ.expect_congr (fun z => ih i (K z) a b c d (by omega) (by omega) (by omega)
        (by omega) (fun x y w => F (z,x) (z,y) (z,w)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
