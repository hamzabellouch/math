import OAI.Probability.DilutedSpin.ProductTowers

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω A I : Type} [Fintype Ω] [Fintype A] [Fintype I]

/-- Palm identity for the actual finite selected-type marked reservoir statistic.
No permutation or add-one property of the score is assumed. The base tower and
base weight are unchanged on the right: all the other types remain present. -/
theorem physical_marked_palm {L : ℕ} (S : PrescribedTree L) (a : S.Leaf)
    (r : ℝ≥0) (P : FiniteLaw I) (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ)
    (factor numerator : I → FinitePath Ω L → FinitePath A L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    (∫ n : ℕ, (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun roots =>
      ∑ q, markedTreeScore S a T Q m base roots factor numerator f q) ∂poissonMeasure r) =
    (r : ℝ) * ∫ n : ℕ, P.expect (fun i =>
      (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun roots =>
        markedTreeScore S a T Q m base (Fin.cons i roots) factor numerator f 0))
      ∂poissonMeasure r := by
  apply poisson_marked_add_one r P
  · intro n roots q
    exact abs_markedTreeScore_le S a T Q m base roots factor numerator f q hf hn hA
  · intro n σ roots q
    exact markedTreeScore_perm S a T Q m base roots factor numerator f σ q

end DilutedSpinGlass

namespace DilutedSpinGlass
variable {Ω A : Type} [Fintype Ω] [Fintype A]

/-- An independent mark prior with no physical state. -/
noncomputable def markPrior : (L : ℕ) → (Fin L → FiniteLaw A) → KernelTower A L
  | 0, _ => ()
  | L+1, Q => (Q 0, fun _ => markPrior L (fun j => Q j.succ))

/-- Move the distinguished Poisson-rooted mark out of the old mark row. -/
def splitRow (k : ℕ) : (Ω × (Fin (k+1) → A)) ≃ ((Ω × (Fin k → A)) × A) where
  toFun y := ((y.1, Fin.tail y.2), y.2 0)
  invFun z := (z.1.1, Fin.cons z.2 z.1.2)
  left_inv y := by simp only [Fin.cons_self_tail]
  right_inv z := by simp only [Fin.tail_cons, Fin.cons_zero]

/-- Counts n+1 in the Palm model have exactly the original n-mark law times
one unused independent prior process. No term is removed from the base law. -/
theorem markedTower_split (k L : ℕ) (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A) :
    KernelTower.transport (splitRow k) L (markedTower (k+1) L T Q) =
      KernelTower.prod L (markedTower k L T Q) (markPrior L Q) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 * (∏ i : Fin (k+1), (Q 0).weight ((Fin.cons z.2 z.1.2 : Fin (k+1) → A) i)) =
        (T.1.weight z.1.1 * ∏ i, (Q 0).weight (z.1.2 i)) * (Q 0).weight z.2
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun j => Q j.succ)

omit [Fintype Ω] [Fintype A] in
theorem physicalPath_split (k L : ℕ) (y : FinitePath (Ω × (Fin (k+1) → A)) L) :
    physicalPath k L (KernelTower.pathFst L (KernelTower.pathEquiv (splitRow k) L y)) =
      physicalPath (k+1) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physicalPath k L (KernelTower.pathFst L
      (KernelTower.pathEquiv (splitRow k) L y.2))) = (y.1.1, physicalPath (k+1) L y.2)
    rw [ih]

omit [Fintype Ω] [Fintype A] in
theorem markPath_split_succ {k : ℕ} (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × (Fin (k+1) → A)) L) :
    markPath q L (KernelTower.pathFst L (KernelTower.pathEquiv (splitRow k) L y)) =
      markPath q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, markPath q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (splitRow k) L y.2))) = (y.1.2 q.succ, markPath q.succ L y.2)
    rw [ih]

omit [Fintype Ω] [Fintype A] in
theorem markPath_split_zero (k L : ℕ) (y : FinitePath (Ω × (Fin (k+1) → A)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (splitRow k) L y) = markPath 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (splitRow k) L y.2)) =
      (y.1.2 0, markPath 0 L y.2)
    rw [ih]

variable {I : Type} {k L : ℕ}

/-- Logarithmic weight after one truly independent added factor on the base
which still contains all original selected-type terms. -/
noncomputable def insertedMarkedLog (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (newFactor : FinitePath Ω L → FinitePath A L → ℝ)
    (y : FinitePath ((Ω × (Fin k → A)) × A) L) : ℝ :=
  markedLog base roots factor (KernelTower.pathFst L y) +
    Real.log (newFactor (physicalPath k L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y))

omit [Fintype Ω] [Fintype A] in
theorem insertedMarkedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (y : FinitePath (Ω × (Fin (k+1) → A)) L) :
    insertedMarkedLog base roots factor (factor i) (KernelTower.pathEquiv (splitRow k) L y) =
      markedLog base (Fin.cons i roots) factor y := by
  simp only [insertedMarkedLog, markedLog, physicalPath_split, markPath_split_succ,
    markPath_split_zero, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass
variable {Ω A I : Type} [Fintype Ω] [Fintype A] {k L : ℕ}

/-- The actual quenched root free energy of the marked model. -/
noncomputable def markedRoot (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) : ℝ :=
  KernelTower.backwardLog L (markedTower k L T Q) m (markedLog base roots factor)

/-- Add/delete a marked Poisson point using a common product prior; the old
mark row is not reweighted before the comparison. -/
theorem markedRoot_cons_bound (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hfactor : ∀ x y, |Real.log (factor i x y)| ≤ C) :
    |markedRoot T Q m base (Fin.cons i roots) factor -
      markedRoot T Q m base roots factor| ≤ C := by
  have h := KernelTower.backwardLog_transport (splitRow k) L
    (markedTower (k+1) L T Q) m (insertedMarkedLog base roots factor (factor i))
  have heq : insertedMarkedLog base roots factor (factor i) ∘
      KernelTower.pathEquiv (splitRow k) L = markedLog base (Fin.cons i roots) factor :=
    funext (fun y => insertedMarkedLog_split base roots i factor y)
  rw [heq, markedTower_split] at h
  unfold markedRoot
  rw [← h, ← KernelTower.backwardLog_prod_fst L (markedTower k L T Q) (markPrior L Q) m
    (markedLog base roots factor)]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [insertedMarkedLog, add_sub_cancel_left] using hfactor
    (physicalPath k L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)

/-- Replacing a physical root block acts only on the base log weight. -/
theorem markedRoot_base_stability (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base base' : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hb : ∀ x, |base x - base' x| ≤ C) :
    |markedRoot T Q m base roots factor - markedRoot T Q m base' roots factor| ≤ C := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [markedLog, add_sub_add_right_eq_sub] using hb (physicalPath k L y)

/-- One changed type/site label changes exactly one bounded log factor. -/
theorem markedRoot_update_bound (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (q : Fin k) (i : I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hf : ∀ x y, |Real.log (factor i x y) - Real.log (factor (roots q) x y)| ≤ C) :
    |markedRoot T Q m base (Function.update roots q i) factor -
      markedRoot T Q m base roots factor| ≤ C := by
  classical
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [markedLog, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have heq : (∑ j : Fin k,
      (Real.log (factor (Function.update roots q i j) (physicalPath k L y) (markPath j L y)) -
        Real.log (factor (roots j) (physicalPath k L y) (markPath j L y)))) =
      Real.log (factor i (physicalPath k L y) (markPath q L y)) -
        Real.log (factor (roots q) (physicalPath k L y) (markPath q L y)) := by
    rw [Finset.sum_eq_single q]
    · simp only [Function.update_self]
    · intro j _ hj
      simp only [Function.update_of_ne hj, sub_self]
    · simp
  rw [heq]
  exact hf _ _

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The recursive independent-root product and the finite indexed root array
are the same labeled data. No exchangeability is needed here. -/
def rootArray {I : Type*} : (n : ℕ) → RootPath I n → Fin n → I
  | 0, _ => Fin.elim0
  | n+1, x => Fin.cons x.1 (rootArray n x.2)

theorem rootArray_replace {I : Type*} (n : ℕ) (x : RootPath I n) (j : Fin n) (i : I) :
    rootArray n (replaceRoot n x j i) = Function.update (rootArray n x) j i := by
  classical
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q <;> simp [rootArray, replaceRoot]
    · funext q
      refine Fin.cases ?_ (fun q => ?_) q
      · simp [rootArray, replaceRoot, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      · simp only [rootArray, replaceRoot, Fin.cases_succ, Fin.cons_succ, ih]
        by_cases h : q = j
        · subst q; simp
        · simp [h, show q.succ ≠ j.succ by simpa using h]

instance rootPathCountable (I : Type*) [Countable I] : (n : ℕ) → Countable (RootPath I n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n+1 => by
    let := rootPathCountable I n
    exact inferInstanceAs (Countable (I × RootPath I n))

instance rootPathSingleton (I : Type*) [MeasurableSpace I] [MeasurableSingletonClass I] :
    (n : ℕ) → MeasurableSingletonClass (RootPath I n)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | n+1 => by
    let := rootPathSingleton I n
    exact inferInstanceAs (MeasurableSingletonClass (I × RootPath I n))

variable {Ω A I : Type} [Fintype Ω] [Fintype A] {L : ℕ}

/-- A linear bound in the actual random point count, from the prior coupling. -/
theorem markedRoot_count_bound (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) (n : ℕ) (x : RootPath I n) :
    |markedRoot T Q m base (rootArray n x) factor| ≤
      |markedRoot T Q m base (fun j : Fin 0 => j.elim0) factor| + (n : ℝ)*C := by
  induction n with
  | zero => simp [rootArray]
  | succ n ih =>
    have h := markedRoot_cons_bound T Q m hm base (rootArray n x.2) x.1 factor (hf x.1)
    have ht := abs_add_le
      (markedRoot T Q m base (rootArray (n+1) x) factor -
        markedRoot T Q m base (rootArray n x.2) factor)
      (markedRoot T Q m base (rootArray n x.2) factor)
    simp only [sub_add_cancel] at ht
    have hi := ih x.2
    change |markedRoot T Q m base (rootArray (n+1) x) factor -
      markedRoot T Q m base (rootArray n x.2) factor| ≤ C at h
    push_cast
    linarith

/-- Literal random-count marked-root concentration. The auxiliary rows change
with the count, and their comparison is justified by markedRoot_cons_bound,
not by an assumed concentration of an already averaged auxiliary score. -/
theorem markedRoot_poisson_variance [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I] (μ : Measure I) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    let F := fun n (x : RootPath I n) => markedRoot T Q m base (rootArray n x) factor
    (∫ n : ℕ, ∫ x, (F n x-(∫ k, rootAverage μ F k ∂poissonMeasure r))^2
      ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤ 3*C^2*(r : ℝ) := by
  dsimp only
  let F := fun n (x : RootPath I n) => markedRoot T Q m base (rootArray n x) factor
  have hmeas (n : ℕ) : Measurable (F n) := measurable_of_countable _
  have hrep (n : ℕ) (j : Fin n) (x : RootPath I n) (i : I) :
      |F n x - F n (replaceRoot n x j i)| ≤ 2*C := by
    dsimp only [F]
    rw [rootArray_replace, abs_sub_comm]
    apply markedRoot_update_bound T Q m hm
    intro z y
    calc
      _ ≤ |Real.log (factor i z y)| + |Real.log (factor (rootArray n x j) z y)| := abs_sub _ _
      _ ≤ C+C := add_le_add (hf _ _ _) (hf _ _ _)
      _ = 2*C := by ring
  have hadd (n : ℕ) (i : I) (x : RootPath I n) : |F (n+1) (i,x)-F n x| ≤ C :=
    markedRoot_cons_bound T Q m hm base (rootArray n x) i factor (hf i)
  have h := poisson_random_root_variance μ r hmeas
    (markedRoot_count_bound T Q m hm base factor hf) hC hrep hadd
  convert h using 1
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FiniteLaw
variable {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]

theorem measurable_expect (P : FiniteLaw Ω) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) : Measurable (fun x => P.expect (f x)) := by
  unfold expect
  exact Finset.measurable_sum _ (fun a _ => (hf a).const_mul _)

theorem measurable_logMean (P : FiniteLaw Ω) (m : ℝ) {f : X → Ω → ℝ}
    (hf : ∀ a, Measurable (fun x => f x a)) : Measurable (fun x => P.logMean m (f x)) := by
  unfold logMean expMoment
  exact (P.measurable_expect (fun a => ((hf a).const_mul m).exp)).log.div_const m

end FiniteLaw

namespace KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_backwardLog (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : X → FinitePath Ω L → ℝ} (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => backwardLog L T m (f x)) := by
  induction L with
  | zero => exact hf ()
  | succ L ih =>
    apply FiniteLaw.measurable_logMean
    intro a
    exact ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b))

end KernelTower

/-- Coordinate evaluation is measurable for the genuine independent root
product, including arbitrary (not necessarily discrete) interaction marks. -/
theorem measurable_rootArray {I : Type*} [MeasurableSpace I] (n : ℕ) (j : Fin n) :
    Measurable (fun x : RootPath I n => rootArray n x j) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun q => ?_) j
    · exact measurable_fst
    · exact (ih q).comp measurable_snd

variable {Ω A I : Type} [Fintype Ω] [Fintype A] [MeasurableSpace I] {L : ℕ}

theorem measurable_markedRoot (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (hf : ∀ x y, Measurable (fun i => factor i x y)) (n : ℕ) :
    Measurable (fun z : RootPath I n => markedRoot T Q m base (rootArray n z) factor) := by
  apply KernelTower.measurable_backwardLog
  intro y
  unfold markedLog
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun j _ =>
    ((hf (physicalPath n L y) (markPath j L y)).comp (measurable_rootArray n j)).log)

/-- Physical-root concentration for general measurable interaction labels.
In particular no finite-support or countability condition is imposed on the
bounded physical disorder by this application of the random-count bound. -/
theorem markedRoot_poisson_variance_measurable
    (μ : Measure I) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (hfmeas : ∀ x y, Measurable (fun i => factor i x y)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    let F := fun n (x : RootPath I n) => markedRoot T Q m base (rootArray n x) factor
    (∫ n : ℕ, ∫ x, (F n x-(∫ k, rootAverage μ F k ∂poissonMeasure r))^2
      ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤ 3*C^2*(r : ℝ) := by
  dsimp only
  let F := fun n (x : RootPath I n) => markedRoot T Q m base (rootArray n x) factor
  have hrep (n : ℕ) (j : Fin n) (x : RootPath I n) (i : I) :
      |F n x - F n (replaceRoot n x j i)| ≤ 2*C := by
    dsimp only [F]
    rw [rootArray_replace, abs_sub_comm]
    apply markedRoot_update_bound T Q m hm
    intro z y
    calc
      _ ≤ |Real.log (factor i z y)| + |Real.log (factor (rootArray n x j) z y)| := abs_sub _ _
      _ ≤ C+C := add_le_add (hf _ _ _) (hf _ _ _)
      _ = 2*C := by ring
  have hadd (n : ℕ) (i : I) (x : RootPath I n) : |F (n+1) (i,x)-F n x| ≤ C :=
    markedRoot_cons_bound T Q m hm base (rootArray n x) i factor (hf i)
  have h := poisson_random_root_variance μ r (measurable_markedRoot T Q m base factor hfmeas)
    (markedRoot_count_bound T Q m hm base factor hf) hC hrep hadd
  convert h using 1
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Root averaging followed by the genuine Poisson count average. -/
noncomputable def poissonRootAverage (r : ℝ≥0)
    (F : (n : ℕ) → RootPath Ω n → ℝ) : ℝ :=
  ∫ n, rootAverage μ F n ∂poissonMeasure r

/-- A parameter in a Poisson root average stays measurable, despite the
count-dependent dimension of the actual root state. -/
theorem measurable_poissonRootAverage (r : ℝ≥0)
    {F : X → (n : ℕ) → RootPath Ω n → ℝ}
    (hF : ∀ n, Measurable (fun z : X × RootPath Ω n => F z.1 n z.2)) :
    Measurable (fun x => poissonRootAverage μ r (F x)) := by
  have hm : Measurable (fun z : X × ℕ => rootAverage μ (F z.1) z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun x => ∫ y, F x n y ∂rootLaw n (fun _ => μ))
    exact (hF n).stronglyMeasurable.integral_prod_right'.measurable
  change Measurable (fun x => ∫ n, rootAverage μ (F x) n ∂poissonMeasure r)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual random-count squared displacement around any center. Both
conditional root fluctuations and random-count fluctuations are retained. -/
theorem poisson_root_second_moment (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hD : 0 ≤ D)
    (hrep : ∀ n (i : Fin n) x y, |F n x-F n (replaceRoot n x i y)| ≤ C)
    (hadd : ∀ n x y, |F (n+1) (x,y)-F n y| ≤ D) (c : ℝ) :
    (∫ n : ℕ, ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤
      (C^2/2+D^2)*(r : ℝ) + (poissonRootAverage μ r F-c)^2 := by
  have hvar (n : ℕ) : variance (F n) (rootLaw n (fun _ => μ)) ≤ C^2/2*(n : ℝ) := by
    have h := root_variance_bound n (fun _ => μ) (hF n) (hB n) (fun _ => C) (hrep n)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hvint : Integrable (fun n => variance (F n) (rootLaw n (fun _ => μ))) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := C^2/2)
    intro n
    rw [abs_of_nonneg (variance_nonneg _ _), zero_add]
    exact hvar n
  have hmeanLp := poisson_memLp_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  have hcount := poisson_variance_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  simp_rw [integral_sq_sub_center (bounded_memLp (hF _) (hB _) 2)]
  change (∫ n, variance (F n) (rootLaw n (fun _ => μ)) + (rootAverage μ F n-c)^2
    ∂poissonMeasure r) ≤ _
  have hsq : Integrable (fun n => (rootAverage μ F n-c)^2) (poissonMeasure r) :=
    (hmeanLp.sub (memLp_const c)).integrable_sq
  rw [integral_add hvint hsq,
    integral_sq_sub_center hmeanLp c]
  have hi := integral_mono hvint ((poisson_integrable_count r).const_mul (C^2/2)) hvar
  rw [integral_const_mul,poisson_mean] at hi
  change _ ≤ (C^2/2+D^2)*(r : ℝ) + ((∫ n, rootAverage μ F n ∂poissonMeasure r)-c)^2
  nlinarith

/-- Full physical-root variance, with an extra independent root block. It is
not conditioned on the Poisson count or on the other root disorder. -/
theorem independent_block_poisson_variance (r : ℝ≥0) (ν : Measure X)
    [IsProbabilityMeasure ν] {F : X → (n : ℕ) → RootPath Ω n → ℝ}
    {B : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ x n, Measurable (F x n)) (hB : ∀ x n y, |F x n y| ≤ B n)
    (hD : 0 ≤ D)
    (hrep : ∀ x n (i : Fin n) y z, |F x n y-F x n (replaceRoot n y i z)| ≤ C)
    (hadd : ∀ x n y z, |F x (n+1) (y,z)-F x n z| ≤ D)
    (hmean : MemLp (fun x => poissonRootAverage μ r (F x)) 2 ν) :
    (∫ x, ∫ n : ℕ, ∫ y, (F x n y-(∫ z, poissonRootAverage μ r (F z) ∂ν))^2
      ∂rootLaw n (fun _ => μ) ∂poissonMeasure r ∂ν) ≤
      (C^2/2+D^2)*(r : ℝ) + variance (fun x => poissonRootAverage μ r (F x)) ν := by
  have hi : Integrable (fun x => (poissonRootAverage μ r (F x) -
      (∫ z, poissonRootAverage μ r (F z) ∂ν))^2) ν :=
    (hmean.sub (memLp_const _)).integrable_sq
  have h := integral_mono_of_nonneg (μ := ν)
    (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
    ((integrable_const ((C^2/2+D^2)*(r : ℝ))).add hi)
    (ae_of_all _ (fun x => poisson_root_second_moment μ r (hF x) (hB x) hD
      (hrep x) (hadd x) _))
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hi] at h
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,
    ← variance_eq_integral hmean.aemeasurable] using h

/-- A linear root bound is sufficient for all count averages in the physical
model; no bounded support for the Poisson count is introduced. -/
theorem poissonRootAverage_bound (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {A D : ℝ}
    (hB : ∀ n x, |F n x| ≤ A+D*n) :
    |poissonRootAverage μ r F| ≤ A+D*(r : ℝ) := by
  have hm (n : ℕ) : |rootAverage μ F n| ≤ A+D*n := abs_integral_le_bound (hB n)
  have hi : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r hm
  have h := integral_mono (hi.norm) ((integrable_const A).add ((poisson_integrable_count r).const_mul D)) hm
  simp only [Real.norm_eq_abs,Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((poisson_integrable_count r).const_mul D),
    integral_const_mul,poisson_mean] at h
  have hnorm := norm_integral_le_integral_norm (μ := poissonMeasure r) (f := rootAverage μ F)
  simpa only [poissonRootAverage,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using
    hnorm.trans h

/-- Uniform stability passes through the entire marked-Poisson root law. -/
theorem poissonRootAverage_stability (r : ℝ≥0)
    {F G : (n : ℕ) → RootPath Ω n → ℝ} {A B D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hBF : ∀ n x, |F n x| ≤ A+B*n) (hBG : ∀ n x, |G n x| ≤ A+B*n)
    (hdiff : ∀ n x, |F n x-G n x| ≤ D) :
    |poissonRootAverage μ r F-poissonRootAverage μ r G| ≤ D := by
  have hiF : Integrable (rootAverage μ F) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBF n))
  have hiG : Integrable (rootAverage μ G) (poissonMeasure r) :=
    poisson_integrable_linear r (fun n => abs_integral_le_bound (hBG n))
  unfold poissonRootAverage
  rw [← integral_sub hiF hiG]
  apply abs_integral_le_bound
  intro n
  unfold rootAverage
  rw [← integral_sub ((bounded_memLp (hF n) (hBF n) 1).integrable le_rfl)
    ((bounded_memLp (hG n) (hBG n) 1).integrable le_rfl)]
  exact abs_integral_le_bound (hdiff n)

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

variable {Ω A I X : Type} [Fintype Ω] [Fintype A]
    [MeasurableSpace I] [MeasurableSpace X] {L M : ℕ}

omit [MeasurableSpace I] in
/-- A bound for the root log partition uniform also in the physical base. -/
theorem markedRoot_uniform_bound (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    {B C : ℝ} (hb : ∀ y, |base y| ≤ B)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) (n : ℕ) (x : RootPath I n) :
    |markedRoot T Q m base (rootArray n x) factor| ≤ B+C*n := by
  have h := KernelTower.backwardLog_stability L (markedTower n L T Q) m hm
    (f := markedLog base (rootArray n x) factor) (g := fun _ => 0) (c := B+C*n) (by
      intro y
      simp only [markedLog,sub_zero]
      calc
        _ ≤ |base (physicalPath n L y)| +
            |∑ j : Fin n, Real.log (factor (rootArray n x j) (physicalPath n L y) (markPath j L y))| :=
          abs_add_le _ _
        _ ≤ B+∑ j : Fin n, |Real.log (factor (rootArray n x j) (physicalPath n L y) (markPath j L y))| :=
          add_le_add (hb _) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ B+∑ _j : Fin n, C := add_le_add_right (Finset.sum_le_sum (fun j _ => hf _ _ _)) _
        _ = B+C*n := by simp [mul_comm])
  rw [KernelTower.backwardLog_const L _ m (fun j => ne_of_gt (hm j)) 0,sub_zero] at h
  exact h

/-- Joint measurability in physical fields and in the actual independent
Poisson labels; no discrete-law assumption occurs. -/
theorem measurable_markedRoot_base (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (hf : ∀ x y, Measurable (fun i => factor i x y)) (n : ℕ) :
    Measurable (fun z : X × RootPath I n => markedRoot T Q m (base z.1) (rootArray n z.2) factor) := by
  apply KernelTower.measurable_backwardLog
  intro y
  unfold markedLog
  exact ((hb _).comp measurable_fst).add (Finset.measurable_sum _ (fun j _ =>
    ((hf _ _).comp ((measurable_rootArray n j).comp measurable_snd)).log))

/-- Unconditional root concentration for the actual marked model with an
independent block of physical fields. The old and fresh mark priors change
with the Poisson count and are not averaged before the log partition. -/
theorem markedRoot_full_variance
    (μ : Measure I) [IsProbabilityMeasure μ] (ν : Fin M → Measure X)
    [∀ i, IsProbabilityMeasure (ν i)] (r : ℝ≥0)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath X M → FinitePath Ω L → ℝ)
    (hbmeas : ∀ y, Measurable (fun x => base x y))
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (hfmeas : ∀ x y, Measurable (fun i => factor i x y))
    {B C : ℝ} (hC : 0 ≤ C) (hb : ∀ x y, |base x y| ≤ B)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C)
    (E : Fin M → ℝ)
    (hbase : ∀ j x z y, |base x y-base (replaceRoot M x j z) y| ≤ E j) :
    let F := fun h n (x : RootPath I n) => markedRoot T Q m (base h) (rootArray n x) factor
    let G := fun h => poissonRootAverage μ r (F h)
    (∫ h, ∫ n : ℕ, ∫ x, (F h n x-(∫ z, G z ∂rootLaw M ν))^2
      ∂rootLaw n (fun _ => μ) ∂poissonMeasure r ∂rootLaw M ν) ≤
        3*C^2*(r : ℝ) + ∑ j, (E j)^2/2 := by
  dsimp only
  let F := fun h n (x : RootPath I n) => markedRoot T Q m (base h) (rootArray n x) factor
  let G := fun h => poissonRootAverage μ r (F h)
  have hF (h : RootPath X M) (n : ℕ) : Measurable (F h n) :=
    measurable_markedRoot T Q m (base h) factor hfmeas n
  have hB (h : RootPath X M) (n : ℕ) (x : RootPath I n) : |F h n x| ≤ B+C*n :=
    markedRoot_uniform_bound T Q m hm (base h) factor (hb h) hf n x
  have hG : Measurable G := measurable_poissonRootAverage μ r
    (measurable_markedRoot_base T Q m base hbmeas factor hfmeas)
  have hGB (h : RootPath X M) : |G h| ≤ B+C*(r : ℝ) :=
    poissonRootAverage_bound μ r (hB h)
  have hGE (j : Fin M) (h : RootPath X M) (z : X) : |G h-G (replaceRoot M h j z)| ≤ E j := by
    apply poissonRootAverage_stability μ r (hF h) (hF (replaceRoot M h j z))
      (hB h) (hB (replaceRoot M h j z))
    intro n x
    exact markedRoot_base_stability T Q m hm (base h) (base (replaceRoot M h j z))
      (rootArray n x) factor (hbase j h z)
  have hv := root_variance_bound M ν hG hGB E hGE
  have hrep (h : RootPath X M) (n : ℕ) (j : Fin n) (x : RootPath I n) (i : I) :
      |F h n x-F h n (replaceRoot n x j i)| ≤ 2*C := by
    dsimp only [F]
    rw [rootArray_replace,abs_sub_comm]
    apply markedRoot_update_bound T Q m hm
    intro y z
    calc
      _ ≤ |Real.log (factor i y z)|+|Real.log (factor (rootArray n x j) y z)| := abs_sub _ _
      _ ≤ C+C := add_le_add (hf _ _ _) (hf _ _ _)
      _ = 2*C := by ring
  have hadd (h : RootPath X M) (n : ℕ) (i : I) (x : RootPath I n) :
      |F h (n+1) (i,x)-F h n x| ≤ C :=
    markedRoot_cons_bound T Q m hm (base h) (rootArray n x) i factor (hf i)
  have hvfull := independent_block_poisson_variance μ r (rootLaw M ν) hF hB hC hrep hadd
    (bounded_memLp hG hGB 2)
  change _ ≤ 3*C^2*(r : ℝ)+∑ j, (E j)^2/2
  convert hvfull.trans (add_le_add_right hv (((2*C)^2/2+C^2)*(r : ℝ))) using 1
  first | rfl | ring

end DilutedSpinGlass

namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

noncomputable def point (a : Ω) : FiniteLaw Ω := by
  classical
  exact { weight := fun x => if x = a then 1 else 0
          nonneg := fun x => by split_ifs <;> norm_num
          total := by simp }

@[simp] theorem expect_point (a : Ω) (f : Ω → ℝ) : (point a).expect f = f a := by
  classical
  simp [expect,point]

@[simp] theorem logMean_point (a : Ω) (m : ℝ) (hm : m ≠ 0) (f : Ω → ℝ) :
    (point a).logMean m f = f a := by
  simp [logMean,expMoment,hm]

noncomputable def uniform [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

theorem logMean_uniform [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).logMean 1 f =
      Real.log (∑ a, Real.exp (f a))-Real.log (Fintype.card Ω) := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hsum : 0 < ∑ a, Real.exp (f a) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [logMean,expMoment,expect,uniform,one_mul,div_one,← Finset.mul_sum]
  rw [Real.log_mul (inv_ne_zero hcard) (ne_of_gt hsum),Real.log_inv]
  ring
end FiniteLaw

namespace KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Auxiliary levels contain no physical spin randomness. The last level is
exactly the Gibbs sum under its uniform spin prior. -/
noncomputable def terminalTower (a : Ω) (P : FiniteLaw Ω) : (r : ℕ) → KernelTower Ω (r+1)
  | 0 => (P, fun _ => ())
  | r+1 => (FiniteLaw.point a, fun _ => terminalTower a P r)

def terminalState : (r : ℕ) → FinitePath Ω (r+1) → Ω
  | 0, x => x.1
  | r+1, x => terminalState r x.2

theorem backwardLog_terminalTower (a : Ω) (P : FiniteLaw Ω) (r : ℕ)
    (m : Fin (r+1) → ℝ) (hm : ∀ j, m j ≠ 0) (f : Ω → ℝ) :
    backwardLog (r+1) (terminalTower a P r) m (fun y => f (terminalState r y)) =
      P.logMean (m (Fin.last r)) f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (FiniteLaw.point a).logMean (m 0)
      (fun _ => backwardLog (r+1) (terminalTower a P r) (fun j => m j.succ)
        (fun y => f (terminalState r y))) = _
    rw [FiniteLaw.logMean_point _ _ (hm 0),ih (fun j => m j.succ) (fun j => hm j.succ)]
    rfl
end KernelTower

variable {Ω A I : Type} [Fintype Ω] [Fintype A]

theorem backwardLog_marked_base (k L : ℕ) (T : KernelTower Ω L)
    (Q : Fin L → FiniteLaw A) (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) :
    KernelTower.backwardLog L (markedTower k L T Q) m (fun y => base (physicalPath k L y)) =
      KernelTower.backwardLog L T m base := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (T.1.bind (fun _ => FiniteLaw.pi (fun _ : Fin k => Q 0))).logMean (m 0)
      (fun z => KernelTower.backwardLog L (markedTower k L (T.2 z.1) (fun j => Q j.succ))
        (fun j => m j.succ) (fun y => base (z.1, physicalPath k L y))) = _
    have hh : (fun z : Ω × (Fin k → A) => KernelTower.backwardLog L
        (markedTower k L (T.2 z.1) (fun j => Q j.succ)) (fun j => m j.succ)
        (fun y => base (z.1, physicalPath k L y))) =
        (fun z => KernelTower.backwardLog L (T.2 z.1) (fun j => m j.succ)
          (fun y => base (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (fun j => Q j.succ) (fun j => m j.succ) (fun y => base (z.1,y))
    rw [hh]
    change _ = T.1.logMean (m 0) (fun z => KernelTower.backwardLog L (T.2 z)
      (fun j => m j.succ) (fun y => base (z,y)))
    exact FiniteLaw.logMean_bind_fst T.1 (FiniteLaw.pi (fun _ : Fin k => Q 0)) (m 0)
      (fun z => KernelTower.backwardLog L (T.2 z) (fun j => m j.succ) (fun y => base (z,y)))

 
theorem markedRoot_distance_base {k L : ℕ} (T : KernelTower Ω L)
    (Q : Fin L → FiniteLaw A) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |markedRoot T Q m base roots factor-KernelTower.backwardLog L T m base| ≤ C*k := by
  rw [markedRoot,← backwardLog_marked_base k L T Q m base]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [markedLog,add_sub_cancel_left]
  calc
    _ ≤ ∑ j : Fin k, |Real.log (factor (roots j) (physicalPath k L y) (markPath j L y))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, C := Finset.sum_le_sum (fun j _ => hf _ _ _)
    _ = C*k := by simp [mul_comm]

end DilutedSpinGlass

namespace DilutedSpinGlass

 
theorem backwardLog_physical {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (r : ℕ)
    (m : Fin (r+1) → ℝ) (hm : ∀ j, m j ≠ 0) (hend : m (Fin.last r) = 1) :
    KernelTower.backwardLog (r+1)
      (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) m
      (fun y => logWeight theta h indices (KernelTower.terminalState r y)) =
      logPartition theta h indices-N*Real.log 2 := by
  rw [KernelTower.backwardLog_terminalTower _ _ _ _ hm, hend, FiniteLaw.logMean_uniform]
  simp only [logPartition,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]

/-- Perturbing the actual finite Ising system changes its hierarchical root
logarithm by the sum of the bounded perturbation log-factors. -/
theorem markedRoot_physical_distance {p N k n : ℕ} {A I : Type} [Fintype A]
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (r : ℕ)
    (Q : Fin (r+1) → FiniteLaw A) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1) (roots : Fin n → I)
    (factor : I → FinitePath (Fin N → Spin) (r+1) → FinitePath A (r+1) → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |markedRoot (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r)
      Q m (fun y => logWeight theta h indices (KernelTower.terminalState r y)) roots factor
        +N*Real.log 2-logPartition theta h indices| ≤ C*n := by
  have hh := markedRoot_distance_base
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r)
    Q m hm (fun y => logWeight theta h indices (KernelTower.terminalState r y)) roots factor hf
  rw [backwardLog_physical theta h indices r m (fun j => ne_of_gt (hm j)) hend] at hh
  convert hh using 1; congr 1; ring

end DilutedSpinGlass

end

end OAI
