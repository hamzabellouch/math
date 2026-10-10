import OAI.Probability.DilutedSpin.ActualCharging
import OAI.Probability.DilutedSpin.LabeledColorHistory
import OAI.Probability.DilutedSpin.ShapeMarginal
import OAI.Probability.DilutedSpin.TreeSampleProjection

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ : Type}

/-- Exact transport of the finite history expansion through an old-sample
projection which commutes with deleting the newly grown branch. -/
lemma labeledHistory_projection {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]
    (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample (Ω×Λ) S → ℝ) → ℝ)
    (W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hVW : ∀ S pos f, V S pos (fun x => f (sampleFst S x)) = W S pos f)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos (fun x => f (sampleFst S x)) =
      labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => exact hVW S pos f
  | cons c cs ih =>
    simp only [labeledHistory]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => ih S (U.erase i) loc (Function.update pos c (loc i)) f)
    · apply Finset.sum_congr rfl
      intro v _
      apply congrArg (gamma S m v * ·)
      simp_rw [sampleFst_oldSample]
      exact ih (grow S v) U (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

variable [Fintype Ω]

/-- Mark integration selects the specified sharing constraints, history by
history, without changing any signed coefficients or the old reservoir. -/
theorem labeledHistory_mark_selector {n : ℕ} {C R ι : Type}
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R] [DecidableEq ι]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (a b : R → C) (d : R → Fin n) (spinColor : C → FinitePath Ω n → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f =>
      (S.sampleLaw (KernelTower.prod n T
        (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher))))).expect
      (fun x => f x * ∏ c, spinColor c (KernelTower.pathFst n (S.pathAt (pos c) x)) *
        MarkSelector.pathColor a b d c (KernelTower.pathSnd n (S.pathAt (pos c) x))))
      cs S U loc pos (fun x => f (sampleFst S x)) =
    labeledHistory m (fun S pos f =>
      (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
      cs S U loc pos f := by
  apply labeledHistory_projection
  intro S pos f
  simp_rw [Finset.prod_mul_distrib,← pathAt_sampleFst,← mul_assoc]
  exact actual_tree_selector_prod S T a b d pos
    (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x))

 
theorem coloredAt_mark_selector {n : ℕ} {C R ι : Type}
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R] [DecidableEq ι]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (a b : R → C) (d : R → Fin n) (spinColor : C → FinitePath Ω n → ℝ)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    let D := fun c (y : FinitePath (Ω × (R→Bool)) n) =>
      spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
    coloredAt (KernelTower.prod n T
        (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher))))
      m (cs.map D) S U (fun i => S.pathAt (loc i))
      (fun x => f (sampleFst S x) * ∏ c ∈ P, D c (S.pathAt (pos c) x)) (fun _ => 1) =
    labeledHistory m (fun S pos f =>
      (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
      cs S U loc pos f := by
  dsimp only
  rw [coloredAt_labeledHistory _ m hm _ cs hcs P hdis hfull]
  exact labeledHistory_mark_selector T m a b d spinColor cs S U loc pos f

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ}

lemma historyMass_mul (F : PrescribedTree L → ℝ) (E : ℝ) (k : ℕ)
    (S : PrescribedTree L) (a : ℕ) :
    historyMass (fun T => E*F T) k S a = E*historyMass F k S a := by
  induction k generalizing S a with
  | zero => rfl
  | succ k ih =>
    simp only [historyMass,ih]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v _
      ring

variable {Ω C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Every literal labeled extension contributes its actual absolute coefficient.
The domination retains all old tests rather than replacing the sampled law by
an unsigned or independently resampled one. -/
theorem labeledHistory_abs_le_mass (F : PrescribedTree L → ℝ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hV : ∀ S pos f, (∀ x, |f x| ≤ 1) → |V S pos f| ≤ F S)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤ historyMass F cs.length S U.card := by
  induction cs generalizing S U with
  | nil => exact hV S pos f hf
  | cons c cs ih =>
    simp only [labeledHistory,List.length_cons,historyMass]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · calc
        _ ≤ ∑ i ∈ U, |labeledHistory (grid L 0 L) V cs S (U.erase i) loc
            (Function.update pos c (loc i)) f| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ U, historyMass F cs.length S (U.card-1) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := ih S (U.erase i) loc (Function.update pos c (loc i)) f hf
          simpa only [Finset.card_erase_of_mem hi] using h
        _ = _ := by simp [nsmul_eq_mul]
    · calc
        _ ≤ ∑ v : S.Internal, |gamma S (grid L 0 L) v *
            labeledHistory (grid L 0 L) V cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact ih (grow S v) U _ _ _ (fun x => hf (oldSample S v x))

/-- Charging estimate for an actual labeled terminal observable. Restricting
the allowed splitting matrices and inserting a uniformly bounded projection
error are both handled in this single estimate. -/
theorem labeledHistory_charging_bound (hL : 0 < L) (Q : Finset ℕ) (b : ℕ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E) (cs : List C) (S : PrescribedTree L)
    (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S)
    (hV : ∀ T pos g, (∀ x, |g x| ≤ 1) → |V T pos g| ≤ E *
      (if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0)) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length b * (L:ℝ)⁻¹^b) := by
  have h := labeledHistory_abs_le_mass
    (fun T => E*(if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0))
    V hV cs S U loc pos f hf
  rw [historyMass_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (charging_final_shape hL Q cs.length b U.card S hU) hE)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω C : Type} [Fintype Ω] {n : ℕ}

/-- Complete positional splitting matrices determine the full joint path law,
not just pair overlaps. The enumerating colors may repeat leaf positions. -/
theorem matrix_paths_expect (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (F : (C → FinitePath Ω n) → ℝ) :
    (S.sampleLaw K).expect (fun x => F (fun c => S.pathAt (pos c) x)) =
      (T.sampleLaw K).expect (fun x => F (fun c => T.pathAt (q c) x)) := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  have he (c : C) : e.leaf (q c) = pos c := by
    apply (splitDepth_eq_height S _ _).mp
    exact (h (Function.surjInv hq (q c)) c).trans
      ((congrArg (fun z => splitDepth T z (q c)) (Function.surjInv_eq hq (q c))).trans
        (splitDepth_self T (q c)))
  have hm := e.expect_paths K (fun x => F (fun c => x (q c)))
  simpa only [he] using hm

/-- An arbitrary correlated old test bounded by one costs at most the actual
single-target L2 error, since the entire target marginal is fixed. -/
theorem matrix_weighted_error (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (D : (C → FinitePath Ω n) → ℝ)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.sampleLaw K).expect (fun x => f x * D (fun c => S.pathAt (pos c) x))| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) := by
  let P := S.sampleLaw K
  let g := fun x : Sample Ω S => D (fun c => S.pathAt (pos c) x)
  have hsq := P.expect_mul_sq_le f g
  have hf2 : P.expect (fun x => f x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        have hx : f x^2 ≤ (1:ℝ)^2 := sq_le_sq.mpr (by simpa using hf x)
        simpa using hx)
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => g x^2) =
      (T.sampleLaw K).expect (fun x => D (fun c => T.pathAt (q c) x)^2) :=
    matrix_paths_expect T S q hq pos h K (fun x => D x^2)
  have hd := (T.sampleLaw K).l2_nonneg (fun x => D (fun c => T.pathAt (q c) x))
  apply (sq_le_sq₀ (abs_nonneg _) hd).mp
  rw [sq_abs,FiniteLaw.l2_sq,← he]
  exact hsq.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (g x))])

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
