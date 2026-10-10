import OAI.Probability.DilutedSpin.MatrixRoot
import OAI.Probability.DilutedSpin.MeasurableProjector
import OAI.Probability.DilutedSpin.PrefixProjection

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {N : ℕ}
lemma measurable_dot {X Y : Z → Fin N → ℝ}
    (hX : ∀ i, Measurable (fun z => X z i)) (hY : ∀ i, Measurable (fun z => Y z i)) :
    Measurable (fun z => dot (X z) (Y z)) := by
  exact (Finset.measurable_sum _ (fun i _ => (hX i).mul (hY i))).div_const _

lemma l2_le_two {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ x, |f x|≤2) : P.l2 f≤2 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  exact (P.expect_mono (fun x => sq_le_sq.mpr (show |f x|≤|(2:ℝ)| by simpa using hf x))).trans_eq
    (P.expect_const _)
end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z C : Type} [Fintype Ω] [MeasurableSpace Z] [Fintype C] [DecidableEq C] {n L N : ℕ}

lemma measurable_tailMean_tilt (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (m : Fin (n+r) → ℝ)
    {f g : Z → FinitePath Ω (n+r) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (x : FinitePath Ω (n+r)) :
    Measurable (fun z => tailMean S r (KernelTower.tilt (n+r) T m (f z)) (g z) x) := by
  induction r with
  | zero => exact measurable_treeMean_tilt S T m hf hg
  | succ r ih =>
      exact ih (T.2 x.1) (fun j => m j.succ) (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

lemma measurable_splitProjector_tilt (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (m : Fin (n+r+1+d) → ℝ)
    {f g : Z → FinitePath Ω (n+r+1+d) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (x : FinitePath Ω (n+r+1+d)) :
    Measurable (fun z => splitProjector S r d (KernelTower.tilt (n+r+1+d) T m (f z)) (g z) x) := by
  induction d with
  | zero => exact measurable_tailMean_tilt S (r+1) T m hf hg x
  | succ d ih =>
      exact ih (T.2 x.1) (fun j => m j.succ) (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

omit [Fintype C] [DecidableEq C] in
lemma measurable_matrixProjectionError_tilt (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (m : Fin L → ℝ) (a c : C)
    {f : Z → FinitePath Ω L → ℝ} {A : Z → (C → FinitePath Ω L) → ℝ}
    {X : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hA : ∀ y, Measurable (fun z => A z y))
    (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => matrixProjectionError T q (KernelTower.tilt L K m (f z)) a c (A z) (X z)) := by
  unfold matrixProjectionError FiniteLaw.l2
  apply Measurable.sqrt
  exact measurable_tilt_sample_expect T K m hf
    (fun y => ((hA _).sub (FiniteLaw.measurable_dot (hX _) (hX _))).pow_const 2)

lemma measurable_oldProjectionError_tilt (S : PrescribedTree L) (a b : S.Leaf)
    (K : KernelTower Ω L) (m : Fin L → ℝ)
    {f : Z → FinitePath Ω L → ℝ} {g : Z → Sample Ω S → ℝ}
    {X : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => oldProjectionError S (KernelTower.tilt L K m (f z)) a b (g z) (X z)) := by
  unfold oldProjectionError FiniteLaw.l2
  apply Measurable.sqrt
  exact measurable_tilt_sample_expect S K m hf
    (fun y => ((FiniteLaw.measurable_dot (hX _) (hX _)).sub (hg y)).pow_const 2)

omit [Fintype C] [DecidableEq C] in
lemma matrixProjectionError_le_two (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (a c : C) (A : (C → FinitePath Ω L) → ℝ)
    (X : FinitePath Ω L → Fin N → ℝ) (hA : ∀ y, |A y|≤1) (hX : ∀ y i, |X y i|≤1) :
    matrixProjectionError T q K a c A X≤2 := by
  apply FiniteLaw.l2_le_two
  intro y
  have ha := hA (fun b => T.pathAt (q b) y)
  have hx := FiniteLaw.abs_dot_le_one _ _ (hX (T.pathAt (q a) y)) (hX (T.pathAt (q c) y))
  exact (abs_sub _ _).trans (by linarith)

lemma oldProjectionError_le_two (S : PrescribedTree L) (K : KernelTower Ω L) (a b : S.Leaf)
    (g : Sample Ω S → ℝ) (X : FinitePath Ω L → Fin N → ℝ)
    (hg : ∀ y, |g y|≤1) (hX : ∀ y i, |X y i|≤1) : oldProjectionError S K a b g X≤2 := by
  apply FiniteLaw.l2_le_two
  intro y
  have ha := hg y
  have hx := FiniteLaw.abs_dot_le_one _ _ (hX (S.pathAt a y)) (hX (S.pathAt b y))
  exact (abs_sub _ _).trans (by linarith)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_tripleExpectAt_tilt (n d : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ}
    {F : Z → FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y))
    (hF : ∀ x y w, Measurable (fun z => F z x y w)) :
    Measurable (fun z => tripleExpectAt n (tilt n T m (f z)) d (F z)) := by
  induction n generalizing d with
  | zero => exact hF () () ()
  | succ n ih =>
    cases d with
    | zero => exact measurable_path_expect (n+1) T m hf (fun x =>
        measurable_path_expect (n+1) T m hf (fun y => measurable_path_expect (n+1) T m hf (hF x y)))
    | succ d =>
      apply T.1.measurable_tilt_expect (m 0)
      · intro a
        exact measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
      · intro a
        exact ih d (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
          (fun x y w => hF (a,x) (a,y) (a,w))

lemma abs_tripleExpectAt_le (n d : ℕ) (T : KernelTower Ω n)
    (F : FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ)
    {B : ℝ} (hF : ∀ x y w, |F x y w|≤B) : |tripleExpectAt n T d F|≤B := by
  induction n generalizing d with
  | zero => exact hF () () ()
  | succ n ih =>
    cases d with
    | zero => exact (law (n+1) T).abs_expect_le (fun x =>
        (law (n+1) T).abs_expect_le (fun y => (law (n+1) T).abs_expect_le (hF x y)))
    | succ d => exact T.1.abs_expect_le (fun a => ih d (T.2 a) _
        (fun x y w => hF (a,x) (a,y) (a,w)))

lemma measurable_halfTripleDifferenceAt_tilt (n d : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => halfTripleDifferenceAt n (tilt n T m (f z)) d (X z)) := by
  apply Measurable.const_mul
  exact measurable_tripleExpectAt_tilt n d T m hf (fun x y w =>
    ((FiniteLaw.measurable_dot (hX x) (hX y)).sub (FiniteLaw.measurable_dot (hX x) (hX w))).pow_const 2)

lemma abs_halfTripleDifferenceAt_le_two (n d : ℕ) (T : KernelTower Ω n)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ x i, |X x i|≤1) : |halfTripleDifferenceAt n T d X|≤2 := by
  have h : |tripleExpectAt n T d (fun x y w => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X w))^2)|≤4 := by
    apply abs_tripleExpectAt_le
    intro x y w
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_le.mp (FiniteLaw.abs_dot_le_one _ _ (hX x) (hX y))
    have h2 := abs_le.mp (FiniteLaw.abs_dot_le_one _ _ (hX x) (hX w))
    nlinarith [sq_nonneg (FiniteLaw.dot (X x) (X y)+FiniteLaw.dot (X x) (X w))]
  unfold halfTripleDifferenceAt
  rw [abs_mul]
  norm_num
  linarith

end DilutedSpinGlass.KernelTower
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z C ι : Type} [Fintype Ω] [MeasurableSpace Z] [Fintype C]
    [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype Ω] [Fintype C] in
lemma measurable_labeledHistory (m : Fin (L+1) → ℝ)
    (V : Z → (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hV : ∀ S pos (g : Z → Sample Ω S → ℝ),
      (∀ x, Measurable (fun z => g z x)) → Measurable (fun z => V z S pos (g z)))
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Z → Sample Ω S → ℝ)
    (hf : ∀ x, Measurable (fun z => f z x)) :
    Measurable (fun z => labeledHistory m (V z) cs S U loc pos (f z)) := by
  induction cs generalizing S U with
  | nil => exact hV S pos f hf
  | cons c cs ih =>
    unfold labeledHistory
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun i _ => ih S (U.erase i) loc _ f hf)
    · exact Finset.measurable_sum _ (fun v _ =>
        (ih (grow S v) U _ _ _ (fun x => hf (oldSample S v x))).const_mul _)

lemma measurable_matrixObservableHistory_tilt (K : KernelTower Ω L) (m : Fin L → ℝ)
    (m' : Fin (L+1) → ℝ) (T S : PrescribedTree L) (q : C → T.Leaf) (cs : List C) (a : S.Leaf)
    {f : Z → FinitePath Ω L → ℝ} {A : Z → (C → FinitePath Ω L) → ℝ}
    {g : Z → Sample Ω S → ℝ}
    (hf : ∀ x, Measurable (fun z => f z x))
    (hA : ∀ x, Measurable (fun z => A z x)) (hg : ∀ x, Measurable (fun z => g z x)) :
    Measurable (fun z => matrixObservableHistory T q (KernelTower.tilt L K m (f z)) m' cs S a (A z) (g z)) := by
  classical
  unfold matrixObservableHistory weightedMatrixHistory
  apply measurable_labeledHistory
  · intro R pos g' hg'
    by_cases h : ∀ a b, splitDepth R (pos a) (pos b)=splitDepth T (q a) (q b)
    · simp only [ite_eq_left h]
      exact measurable_tilt_sample_expect R K m hf (fun x => (hg' x).mul (hA _))
    · simp only [ite_eq_right h]
      exact measurable_const
  · exact hg

/-- A crude finite mass bound used ONLY for integrability. It is not a
replacement for the signed centered covariance or the depth charging bound. -/
lemma matrixObservableHistory_bound (K : KernelTower Ω L) (T S : PrescribedTree L)
    (q : C → T.Leaf) (cs : List C) (a : S.Leaf)
    (A : (C → FinitePath Ω L) → ℝ) (g : Sample Ω S → ℝ)
    (hA : ∀ x, |A x|≤1) (hg : ∀ x, |g x|≤1) :
    |matrixObservableHistory T q K (grid L 0 L) cs S a A g|≤
      historyMass (fun _ => 1) cs.length S ((Finset.univ.erase a).card) := by
  classical
  unfold matrixObservableHistory weightedMatrixHistory
  apply labeledHistory_abs_le_mass (fun _ => 1)
  · intro R pos g' hg'
    by_cases h : ∀ a b, splitDepth R (pos a) (pos b)=splitDepth T (q a) (q b)
    · rw [ite_eq_left h]
      apply FiniteLaw.abs_expect_le
      intro x
      rw [abs_mul]
      exact (mul_le_mul (hg' x) (hA _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · rw [ite_eq_right h,abs_zero]
      norm_num
  · exact hg

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
