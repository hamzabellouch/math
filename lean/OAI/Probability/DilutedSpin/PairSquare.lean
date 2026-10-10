import OAI.Probability.DilutedSpin.GlobalSelectedAverage
import OAI.Probability.DilutedSpin.ParameterProduct
import OAI.Probability.DilutedSpin.ParameterScoreMeasurable

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance pairSiteAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma pairObservableHistory_sum {ι : Type*} (I : Finset ι)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : ι → FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => ∑ i ∈ I, R i x y) f =
      ∑ i ∈ I, pairObservableHistory T m S a d (R i) f := by
  classical
  unfold pairObservableHistory
  simp only [Finset.mul_sum,FiniteLaw.expect_sum,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp

lemma pairObservableHistory_div
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) (c : ℝ) :
    pairObservableHistory T m S a d (fun x y => R x y/c) f =
      pairObservableHistory T m S a d R f/c := by
  unfold pairObservableHistory
  simp only [← mul_div_assoc,FiniteLaw.expect_div,add_div,Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v hv <;> split_ifs <;> simp

/-- The empirical overlap is the physical iid-uniform site average of the
literal one-color histories. No independence from the old test is imposed. -/
theorem pair_history_dot (T : KernelTower Ω (n+1)) (m : Fin (n+2) → ℝ)
    (S : PrescribedTree (n+1)) (a : S.Leaf) (d : ℕ)
    (X : FinitePath Ω (n+1) → Fin N → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y)) f =
      (∑ i : Fin N, shapeHistory T m
        (fun M : Option (Fin 1) → Option (Fin 1) → ℕ => if M none (some 0) = d then 1 else 0)
        (fun _ x => X x i) S a f)/(N:ℝ) := by
  unfold FiniteLaw.dot
  rw [pairObservableHistory_div,pairObservableHistory_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (shapeHistory_one T m S a d (fun x => X x i) (fun x => X x i) f).symm

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance pairSquareDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable def pairFreshCost (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (a : S.Leaf) (d : ℕ) (v : S.Internal) : ℝ :=
  if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then -gamma S m v else 0

lemma pairFreshCost_nonneg (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (a : S.Leaf) (d : ℕ) (v : S.Internal) :
    0 ≤ pairFreshCost S m a d v := by
  unfold pairFreshCost
  split_ifs
  · exact neg_nonneg.mpr (gamma_nonpos S m hm hp v)
  · rfl

/-- The exact nonnegative-square identity before root averaging. It follows
from actual two-path marginals and complete old-law projectivity. -/
theorem pair_square_identity (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a b : S.Leaf)
    (hab : a ≠ b) (htwo : ∀ c : S.Leaf, c = a ∨ c = b)
    (d : ℕ) (hd : d < n) (hsplit : splitDepth S a b = d)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) :
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
  have hsum : (∑ v : S.Internal, pairFreshCost S m a d v) = 1-e := by
    have hh := pair_choice_total S a d hd m hend
    have ho : (∑ c : S.Leaf, if splitDepth S a c = d then (1:ℝ) else 0) = 1 := by
      rw [← pair_univ_erase S a d hd,erase_eq_of_two S a b hab htwo]
      rw [Finset.sum_singleton,ite_eq_left hsplit]
    rw [ho] at hh
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
  have hhist : pairObservableHistory T m S a d R X = A - ∑ v : S.Internal,
      pairFreshCost S m a d v*Q v := by
    unfold pairObservableHistory
    rw [erase_eq_of_two S a b hab htwo,Finset.sum_singleton,ite_eq_left hsplit]
    have ha : (S.sampleLaw T).expect (fun x => X x * R (S.pathAt a x) (S.pathAt b x)) = A := by
      apply FiniteLaw.expect_congr
      intro x
      change X x*X x = X x^2
      ring
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
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set

 
noncomputable def boundParameter (a b x : ℝ) : ℝ := max a (min b x)

lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma boundParameter_eq {a b x : ℝ} (hx : x ∈ Icc a b) : boundParameter a b x = x := by
  simp [boundParameter,min_eq_right hx.2,max_eq_right hx.1]

lemma measurable_boundParameter (a b : ℝ) : Measurable (boundParameter a b) :=
  measurable_const.max (measurable_const.min measurable_id)

namespace HeterogeneousMarks
open scoped BigOperators NNReal ENNReal
variable {Ω I X Y U : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
theorem otherLog_congr (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (f g : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) : otherLog base roots sel f = otherLog base roots sel g := by
  unfold otherLog
  congr 1
  funext i x y
  cases hi : sel i
  · simp only [Bool.false_eq_true,ite_false]
    rw [h i hi]
  · rfl

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_congr
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (f g D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) (t u : ℝ) (z : FullRootState Y X I M) :
    fullSelectedRawScore T Q m base sel f D E t z u = fullSelectedRawScore T Q m base sel g D E t z u := by
  dsimp only [fullSelectedRawScore,packRoot,selectedScore]
  simp_rw [← selected_perturbLog_eq,otherLog_congr _ _ sel f g h]

omit [Countable I] [MeasurableSingletonClass I] in
theorem fullSelectedError_congr
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (f g D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) (t u : ℝ) :
    fullSelectedError ξ μ ν r s T Q m base sel f D E t u =
      fullSelectedError ξ μ ν r s T Q m base sel g D E t u := by
  unfold fullSelectedError
  simp_rw [fullSelectedRawScore_congr T Q m base sel f g D E h t u]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp only [fullSelectedDeviation]
  rw [otherLog_congr _ _ sel f g h]

/-- The entire dictionary factor family, with its original two coordinates
and no truncation in the number of types. -/
noncomputable def parameterFactor {J : Type} (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (u : J → ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  1+t (key i)*D i x y+boundParameter (a (key i)) (b (key i)) (u (key i))*E i x y

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma measurable_parameterFactor {J : Type} (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    Measurable (fun u => parameterFactor key a b t D E u i x y) :=
  measurable_const.add (((measurable_boundParameter _ _).comp
    (measurable_pi_apply (key i))).mul_const _)

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma parameterFactor_refresh {J : Type} [DecidableEq J] (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (v : ℝ) (i : I) (hi : decide (key i = j) = false) :
    parameterFactor key a b t D E (Function.update u j v) i = parameterFactor key a b t D E u i := by
  have h : key i ≠ j := of_decide_eq_false hi
  funext x y
  simp only [parameterFactor,Function.update_of_ne h]

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
