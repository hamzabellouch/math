import OAI.Probability.DilutedSpin.FullThermalAverage
import OAI.Probability.DilutedSpin.FullTreeScore
import OAI.Probability.DilutedSpin.GeneralPairSquare
import OAI.Probability.DilutedSpin.MatrixPair
import OAI.Probability.DilutedSpin.PairSquare
import OAI.Probability.DilutedSpin.PhysicalSelectedConcentration

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
lemma abs_expect_mul_le_l2 (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hg : ∀ x, |g x| ≤ 1) : |P.expect (fun x => f x*g x)| ≤ P.l2 f := by
  have hs := P.expect_mul_sq_le f g
  have hg2 : P.expect (fun x => g x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using (sq_le_sq.mpr (show |g x| ≤ |(1:ℝ)| by simpa using hg x)))
      _ = _ := P.expect_const 1
  apply (sq_le_sq₀ (abs_nonneg _) (P.l2_nonneg _)).mp
  rw [sq_abs,l2_sq]
  exact hs.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (f x))])
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance singletonRootPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {n : ℕ}

lemma grow_l2 (S : PrescribedTree n) (v : S.Internal) (K : KernelTower Ω n)
    (f : Sample Ω S → ℝ) :
    ((grow S v).sampleLaw K).l2 (fun x => f (oldSample S v x)) = (S.sampleLaw K).l2 f := by
  unfold FiniteLaw.l2
  exact congrArg Real.sqrt (grow_projectivity S K v (fun x => f x^2))

lemma pairObservableHistory_sub_test (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f g : Sample Ω S → ℝ) :
    pairObservableHistory K m S a d R (fun x => f x-g x) =
      pairObservableHistory K m S a d R f-pairObservableHistory K m S a d R g := by
  unfold pairObservableHistory
  simp only [sub_mul,FiniteLaw.expect_sub,mul_sub]
  have p (b : S.Leaf) :
      (if splitDepth S a b = d then
        (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) -
        (S.sampleLaw K).expect (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) =
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0) -
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) := by split_ifs <;> ring
  have q (v : S.Internal) :
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))-
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) =
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0)-
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) := by split_ifs <;> ring
  simp_rw [p,q]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Changing the old test has its original L2 cost, not a sup norm cost; fresh
branches preserve its entire old marginal. -/
theorem pairObservableHistory_l2 (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ)
    (hR : ∀ x y, |R x y| ≤ 1) :
    |pairObservableHistory K m S a d R f| ≤ pairHistoryMass S m a*(S.sampleLaw K).l2 f := by
  let B := (S.sampleLaw K).l2 f
  have hB : 0 ≤ B := FiniteLaw.l2_nonneg _ _
  unfold pairObservableHistory pairHistoryMass
  calc
    _ ≤ (∑ b ∈ (Finset.univ : Finset S.Leaf).erase a,
      |if splitDepth S a b = d then (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0|) +
      ∑ v : S.Internal, |if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _b ∈ (Finset.univ : Finset S.Leaf).erase a, B) + ∑ v : S.Internal, |gamma S m v| * B := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro b _
        split_ifs
        · exact FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)
        · simpa using hB
      · apply Finset.sum_le_sum; intro v _
        split_ifs
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)).trans_eq (grow_l2 S v K f)
        · simpa using mul_nonneg (abs_nonneg (gamma S m v)) hB
    _ = _ := by simp [B,← Finset.sum_mul,add_mul]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The nonnegative three-copy argument on an ARBITRARY old tree. Only the
geometric grouping of eligible paths is needed; all old paths and the test
are retained. This applies to the projected means of multi-leaf shapes. -/
theorem general_decorrelation_bound_at (n d : ℕ) (hd : d < n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1)
    (S : PrescribedTree n) (a b : S.Leaf) (v : S.Internal)
    (hab : splitDepth S a b = d)
    (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (X : FinitePath Ω n → Fin N → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      X (S.pathAt c x) = X (S.pathAt b x)) :
    (-gamma S m v)*KernelTower.prefixEnergyAt n T d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x =>
          FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))^2) +
      pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y))
        (fun x => FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))) := by
  classical
  let R := fun x y => FiniteLaw.dot (X x) (X y)
  let D := fun w : S.Internal => ((grow S w).sampleLaw T).expect (fun x =>
    (R (S.pathAt a (oldSample S w x)) (S.pathAt b (oldSample S w x)) -
      R ((grow S w).pathAt (oldLeaf S w a) x) ((grow S w).pathAt (newLeaf S w) x))^2)
  have hsum := pair_square_identity_general T m hend S a b d (by omega) hab R
    (fun c hc x => congrArg (FiniteLaw.dot (X (S.pathAt a x))) (hOld c hc x))
  have hnonneg (w : S.Internal) : 0 ≤ pairFreshCost S m a d w * D w :=
    mul_nonneg (pairFreshCost_nonneg S m hm hp a d w)
      (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hone : pairFreshCost S m a d v * D v ≤ ∑ w : S.Internal, pairFreshCost S m a d w * D w :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hcost : pairFreshCost S m a d v = -gamma S m v := by
    unfold pairFreshCost
    rw [splitDepth_symm,splitDepth_new_old,hav,ite_eq_left rfl]
  have hD : D v = KernelTower.tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
    have q := triple_marginal (grow S v) T (oldLeaf S v a) (oldLeaf S v b) (newLeaf S v)
      d (by omega) (by simpa only [splitDepth_old_old] using hab)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v a),splitDepth_new_old] using hav)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v b),splitDepth_new_old] using hbv)
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)
    simpa only [D,R,pathAt_oldLeaf,pathAt_newLeaf] using q
  have h3 := KernelTower.prefix_three_copy_bound_at n T d hd X
  rw [← hD] at h3
  have hmul := mul_le_mul_of_nonneg_left h3 (pairFreshCost_nonneg S m hm hp a d v)
  rw [hcost] at hmul hone
  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  linarith


end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
lemma abs_dot_le_one {N : ℕ} (x y : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) : |dot x y| ≤ 1 := by
  by_cases hN : N = 0
  · subst N; simp [dot]
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [dot,abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul]
  calc
    _ ≤ ∑ i, |x i*y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hy i))
    _ = _ := by simp
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (h d N : ℕ)
    (T : (z : Z) → KernelTower (Ω z) (h+1+d))
    (X : (z : Z) → FinitePath (Ω z) (h+1+d) → Fin N → ℝ)
    (m : Fin (h+1+d+1) → ℝ)

noncomputable def rootPairMean : ℝ :=
  ∫ z, ((fork h 2 d).sampleLaw (T z)).expect (fun x =>
    FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
      (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))) ∂μ

noncomputable def rootPairSecond : ℝ :=
  ∫ z, ((fork h 2 d).sampleLaw (T z)).expect (fun x =>
    FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
      (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))^2) ∂μ

noncomputable def rootPairCovariance : ℝ :=
  (∫ z, pairObservableHistory (T z) m (fork h 2 d) (forkLeaf h 2 d 0) d
    (fun x y => FiniteLaw.dot (X z x) (X z y))
    (fun x => FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
      (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))) ∂μ) -
  rootPairMean μ Ω h d N T X *
    (∫ z, pairObservableHistory (T z) m (fork h 2 d) (forkLeaf h 2 d 0) d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) (fun _ => 1) ∂μ)

omit [IsProbabilityMeasure μ] in
lemma rootPairCovariance_center (hend : m (Fin.last (h+1+d)) = 1) :
    rootPairCovariance μ Ω h d N T X m =
      (∫ z, pairObservableHistory (T z) m (fork h 2 d) (forkLeaf h 2 d 0) d
        (fun x y => FiniteLaw.dot (X z x) (X z y))
        (fun x => FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
          (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))) ∂μ) +
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(rootPairMean μ Ω h d N T X)^2 := by
  unfold rootPairCovariance
  have he (z : Z) := pairObservableHistory_const (T z) m hend (fork h 2 d)
    (forkLeaf h 2 d 0) d (by omega) (fun x y => FiniteLaw.dot (X z x) (X z y))
  have hmarg (z : Z) : KernelTower.pairExpect (h+1+d) (T z) d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) =
      ((fork h 2 d).sampleLaw (T z)).expect (fun x =>
        FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
          (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))) := by
    have q := pair_marginal (fork h 2 d) (T z) (forkLeaf h 2 d 0) (forkLeaf h 2 d 1)
      (fun x y => FiniteLaw.dot (X z x) (X z y))
    rw [fork_split 0 1 (by decide)] at q
    exact q.symm
  simp_rw [he,hmarg]
  rw [integral_const_mul]
  change _ - rootPairMean μ Ω h d N T X *
    ((m ⟨d,by omega⟩-m ⟨d+1,by omega⟩)*rootPairMean μ Ω h d N T X) = _
  ring

/-- Disorder-averaged singleton inequality with the ACTUAL signed-history
covariance. Root variables and all reservoir alphabets may depend on z. -/
theorem singleton_root_bound
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (h+1+d)) = 1)
    (hX : ∀ z x i, |X z x i| ≤ 1)
    (hE : Integrable (fun z => KernelTower.prefixCovarianceEnergy h d (T z) (X z)) μ)
    (hA : Integrable (fun z => ((fork h 2 d).sampleLaw (T z)).expect (fun x =>
      FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
        (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x))^2)) μ)
    (hH : Integrable (fun z => pairObservableHistory (T z) m (fork h 2 d) (forkLeaf h 2 d 0) d
      (fun x y => FiniteLaw.dot (X z x) (X z y))
      (fun x => FiniteLaw.dot (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x))
        (X z ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x)))) μ) :
    (2*m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (∫ z, KernelTower.prefixCovarianceEnergy h d (T z) (X z) ∂μ) ≤
      m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ + rootPairCovariance μ Ω h d N T X m := by
  have hpoint (z : Z) := singleton_decorrelation_bound h d (T z) m hm hp hend (X z)
  have hi := integral_mono (hE.const_mul _) ((hA.const_mul _).add hH) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hA.const_mul _) hH,integral_const_mul] at hi
  rw [rootPairCovariance_center μ Ω h d N T X m hend]
  have hAone : rootPairSecond μ Ω h d N T X ≤ 1 := by
    unfold rootPairSecond
    calc
      _ ≤ ∫ _z : Z, (1:ℝ) ∂μ := integral_mono hA (integrable_const 1) (fun z => by
        calc
          _ ≤ ((fork h 2 d).sampleLaw (T z)).expect (fun _ => (1:ℝ)) :=
            FiniteLaw.expect_mono _ (fun x => (sq_le_one_iff_abs_le_one _).mpr
              (FiniteLaw.abs_dot_le_one _ _ (hX z _) (hX z _)))
          _ = _ := FiniteLaw.expect_const _ _)
      _ = 1 := by simp
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hv := mul_nonneg hδ (sq_nonneg (rootPairMean μ Ω h d N T X))
  have hs := mul_le_mul_of_nonneg_left hAone hδ
  dsimp only [rootPairSecond] at hs
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def rootTreeMean (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y =>
    (S.sampleLaw (KernelTower.tilt L (tower (rootArray n y) L T Q) m
      (logWeight (base h k x) (rootArray n y) old))).expect
      (fun w => f (fun b => physical (rootArray n y) L (S.pathAt b w)))) z

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootTreeMean_eq_selected (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    rootTreeMean S T Q m base (selectedFactor sel fixed D E t u) f =
      fullSelectedTreeMean S T Q m base sel fixed D E t u f := rfl

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def oldTreeAverage : ℝ :=
  ∫ z, rootTreeMean S T Q m base old f z ∂fullRootLaw ξ μ ν r s

lemma measurable_rootTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (rootTreeMean S T Q m base old f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootTreeMean S T Q m base old f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

omit [Countable I] [MeasurableSingletonClass I] in
lemma oldTreeAverage_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |oldTreeAverage ξ μ ν r s S T Q m base old f| ≤ B := by
  simpa only [oldTreeAverage, Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := fullRootLaw ξ μ ν r s)
      (f := rootTreeMean S T Q m base old f)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using rootTreeMean_bound S T Q m base old f hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I J X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def parameterError
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) : ℝ :=
  fullSelectedError ξ μ ν r s T Q m base (fun i => decide (key i = j))
    (parameterFactor key a b t D E u) D E (t j) (boundParameter (a j) (b j) (u j))

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma selectedParameterFactor_eq (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (j : J) (u : J → ℝ) :
    selectedFactor (fun i => decide (key i = j)) (parameterFactor key a b t D E u)
      D E (t j) (boundParameter (a j) (b j) (u j)) = parameterFactor key a b t D E u := by
  funext i x y
  by_cases h : key i = j <;> simp [selectedFactor,parameterFactor,h]

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [DecidableEq J] in
lemma parameterFactor_log_bound (key : I → J) (a b t : J → ℝ)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (u : J → ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |Real.log (parameterFactor key a b t D E u i x y)| ≤ 1 := by
  have hu : |boundParameter (a (key i)) (b (key i)) (u (key i))| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI (key i) (boundParameter_mem (hab (key i)) (u (key i)))).1],
      (hI (key i) (boundParameter_mem (hab (key i)) (u (key i)))).2⟩
  exact selectedFactor_log_bound (fun _ => true) (fun _ _ _ => 1) D E
    (fun _ _ _ => by simp) hD hE (ht (key i)) hu i x y

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma parameterError_nonneg (j : J) (u : J → ℝ) :
    0 ≤ parameterError ξ μ ν r s T Q m base key a b t D E j u :=
  fullSelectedError_nonneg ξ μ ν r s T Q m base _ _ D E (t j) _

lemma measurable_parameterError
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) (j : J) :
    Measurable (parameterError ξ μ ν r s T Q m base key a b t D E j) :=
  measurable_fullSelectedError_family T Q m base _ (parameterFactor key a b t D E) D E (t j)
    (fun u => boundParameter (a j) (b j) (u j)) hb
    (measurable_parameterFactor key a b t D E)
    ((measurable_boundParameter _ _).comp (measurable_pi_apply j)) ξ μ ν r s

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma parameterError_refresh (j : J) (u : J → ℝ) {v : ℝ} (hv : v ∈ Icc (a j) (b j)) :
    parameterError ξ μ ν r s T Q m base key a b t D E j (Function.update u j v) =
      fullSelectedError ξ μ ν r s T Q m base (fun i => decide (key i = j))
        (parameterFactor key a b t D E u) D E (t j) v := by
  unfold parameterError
  rw [Function.update_self,boundParameter_eq hv]
  exact fullSelectedError_congr ξ μ ν r s T Q m base _ _ _ D E
    (fun i hi => parameterFactor_refresh key a b t D E j u v i hi) (t j) v

lemma integrable_parameterError (π : Measure (J → ℝ)) [IsProbabilityMeasure π]
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1) (j : J) :
    Integrable (parameterError ξ μ ν r s T Q m base key a b t D E j) π := by
  apply (integrable_const (4*(s:ℝ)) : Integrable (fun _ : J → ℝ => 4*(s:ℝ)) π).mono'
    (measurable_parameterError ξ μ ν r s T Q m base key a b t D E hb j).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_of_nonneg (parameterError_nonneg ξ μ ν r s T Q m base key a b t D E j u)]
  exact fullSelectedError_bound ξ μ ν r s T Q m base _ _ D E (t j) hb hD hE
    (ht j) (abs_le.mpr ⟨by linarith [(hI j (boundParameter_mem (hab j) (u j))).1],
      (hI j (boundParameter_mem (hab j) (u j))).2⟩)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
