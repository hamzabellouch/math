import OAI.Probability.DilutedSpin.ActualNegligible
import OAI.Probability.DilutedSpin.ActualPrefix
import OAI.Probability.DilutedSpin.PairSquare

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance generalPairSquareDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- The exact nonnegative-square identity before root averaging. It follows
from actual two-path marginals and complete old-law projectivity. -/
theorem pair_square_identity_general (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) (hsplit : splitDepth S a b = d)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      R (S.pathAt a x) (S.pathAt c x) = R (S.pathAt a x) (S.pathAt b x)) :
    (1/2:ℝ) * ∑ v : S.Internal, pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x =>
        (R (S.pathAt a (oldSample S v x)) (S.pathAt b (oldSample S v x)) -
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))^2) =
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x => R (S.pathAt a x) (S.pathAt b x)^2) +
      pairObservableHistory T m S a d R (fun x => R (S.pathAt a x) (S.pathAt b x)) := by
  classical
  let X := fun x : Sample Ω S => R (S.pathAt a x) (S.pathAt b x)
  let Y := fun (v : S.Internal) (x : Sample Ω (grow S v)) =>
    R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)
  let A := (S.sampleLaw T).expect (fun x => X x^2)
  let Q := fun v : S.Internal => ((grow S v).sampleLaw T).expect
    (fun x => X (oldSample S v x)*Y v x)
  let e := m ⟨d,by omega⟩-m ⟨d+1,by omega⟩
  let q : ℝ := ∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
    if splitDepth S a c = d then 1 else 0
  have hsum : (∑ v : S.Internal, pairFreshCost S m a d v) = q-e := by
    have hh := pair_choice_total S a d hd m hend
    rw [← pair_univ_erase S a d hd] at hh
    have hn (v : S.Internal) : pairFreshCost S m a d v =
        -(if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then gamma S m v else 0) := by
      unfold pairFreshCost; split_ifs <;> simp
    simp_rw [hn,Finset.sum_neg_distrib]
    dsimp only [e]
    linarith
  have hsq (v : S.Internal)
      (hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d) :
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
        2*A-2*Q v := by
    have hy : ((grow S v).sampleLaw T).expect (fun x => Y v x^2) = A := by
      exact pair_marginal_eq (grow S v) S T (oldLeaf S v a) (newLeaf S v) a b
        (hv.trans hsplit.symm) (fun x y => R x y^2)
    calc
      _ = ((grow S v).sampleLaw T).expect (fun x =>
        X (oldSample S v x)^2 - 2*(X (oldSample S v x)*Y v x) + Y v x^2) :=
          FiniteLaw.expect_congr _ (fun _ => by ring)
      _ = _ := by
        rw [FiniteLaw.expect_add,FiniteLaw.expect_sub,FiniteLaw.expect_mul_left,
          grow_projectivity S T v (fun x => X x^2),hy]
        change A-2*Q v+A = 2*A-2*Q v
        ring
  have hterm (v : S.Internal) : pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
      2*(pairFreshCost S m a d v*A) - 2*(pairFreshCost S m a d v*Q v) := by
    by_cases hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
    · rw [hsq v hv]; ring
    · simp only [pairFreshCost,hv,ite_false,zero_mul,mul_zero,sub_zero]
  have hhist : pairObservableHistory T m S a d R X = q*A - ∑ v : S.Internal,
      pairFreshCost S m a d v*Q v := by
    unfold pairObservableHistory
    have ha : (∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
        if splitDepth S a c = d then (S.sampleLaw T).expect
          (fun x => X x * R (S.pathAt a x) (S.pathAt c x)) else 0) = q*A := by
      dsimp only [q]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs with hs
      · rw [one_mul]
        apply FiniteLaw.expect_congr
        intro x
        rw [hOld c hs x]
        change X x * X x = X x^2
        ring
      · simp
    rw [ha,sub_eq_add_neg,← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    unfold pairFreshCost
    split_ifs
    · change gamma S m v * Q v = -(-gamma S m v * Q v)
      ring
    · simp
  have hminus : m ⟨d+1,by omega⟩ - m ⟨d,by omega⟩ = -e := by dsimp [e]; ring
  rw [hminus]
  change (1/2:ℝ)*(∑ v, pairFreshCost S m a d v *
    ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2)) =
    (-e)*A+pairObservableHistory T m S a d R X
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,hsum,hhist]
  ring


end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma fork_two_positions (h d : ℕ) (a : (fork h 2 d).Leaf) :
    a = forkLeaf h 2 d 0 ∨ a = forkLeaf h 2 d 1 := by
  obtain ⟨i,rfl⟩ := forkLeaf_surjective h 2 d a
  have hi : i = 0 ∨ i = 1 := by
    have hb : i.val < 2 := i.isLt
    apply (show i.val = 0 ∨ i.val = 1 by omega).imp
    · intro h; exact Fin.ext h
    · intro h; exact Fin.ext h
  rcases hi with rfl|rfl <;> simp

 
theorem singleton_decorrelation_bound (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (m : Fin (h+1+d+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last (h+1+d)) = 1)
    (X : FinitePath Ω (h+1+d) → Fin N → ℝ) :
    (2*m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*KernelTower.prefixCovarianceEnergy h d T X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        ((fork h 2 d).sampleLaw T).expect (fun x =>
          FiniteLaw.dot (X ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
            (X ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x)) ^2) +
      pairObservableHistory T m (fork h 2 d) (forkLeaf h 2 d 0) d
        (fun x y => FiniteLaw.dot (X x) (X y))
        (fun x => FiniteLaw.dot (X ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
          (X ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))) := by
  classical
  let S := fork h 2 d
  let a := forkLeaf h 2 d 0
  let b := forkLeaf h 2 d 1
  let v := forkVertex h 2 d
  let R := fun x y => FiniteLaw.dot (X x) (X y)
  let D := fun w : S.Internal => ((grow S w).sampleLaw T).expect (fun x =>
    (R (S.pathAt a (oldSample S w x)) (S.pathAt b (oldSample S w x)) -
      R ((grow S w).pathAt (oldLeaf S w a) x) ((grow S w).pathAt (newLeaf S w) x))^2)
  have hab : a ≠ b := fun he => (by norm_num : (0:Fin (2:ℕ+)) ≠ 1)
    (forkLeaf_injective h 2 d he)
  have hsplit : splitDepth S a b = d := fork_split 0 1 (by decide)
  have hsum := pair_square_identity T m hend S a b hab (fork_two_positions h d)
    d (by omega) hsplit R
  have hnonneg (w : S.Internal) : 0 ≤ pairFreshCost S m a d w * D w :=
    mul_nonneg (pairFreshCost_nonneg S m hm hp a d w)
      (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hone : pairFreshCost S m a d v * D v ≤ ∑ w : S.Internal, pairFreshCost S m a d w * D w :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hcost : pairFreshCost S m a d v = 2*m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := by
    unfold pairFreshCost
    have hs : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d := by
      rw [splitDepth_symm,splitDepth_new_old]
      exact fork_fresh_split h d 2 0
    rw [ite_eq_left hs]
    change -gamma (fork h 2 d) m (forkVertex h 2 d) = _
    rw [fork_gamma]
    norm_num
  have hD : D v = KernelTower.tripleExpect h d T
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
    dsimp only [D,R]
    simp_rw [pathAt_oldLeaf,pathAt_newLeaf]
    exact fork_three_joint h d T (fun x y z =>
      (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)
  have h3 := KernelTower.prefix_three_copy_bound h d T X
  rw [← hD] at h3
  have hc : 0 ≤ pairFreshCost S m a d v := pairFreshCost_nonneg S m hm hp a d v
  have hmul := mul_le_mul_of_nonneg_left h3 hc
  rw [hcost] at hmul hone
  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
