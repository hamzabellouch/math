import OAI.Probability.DilutedSpin.CountableReservoir

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- A relabeling of heterogeneous marks, without identification of their alphabets. -/
def rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) :
    (Ω × Row (A := A) roots) ≃ (Ω × Row (A := A) (roots ∘ σ)) :=
  (Equiv.refl Ω).prodCongr (Equiv.piCongrLeft (fun q => A (roots q)) σ).symm

theorem tower_transport {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (rowPerm roots σ) L (tower roots L T Q) =
      tower (roots ∘ σ) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro x
      change T.1.weight x.1 * (∏ q, (Q (roots q) 0).weight
          (Equiv.piCongrLeft (fun q => A (roots q)) σ x.2 q)) =
        T.1.weight x.1 * ∏ q, (Q (roots (σ q)) 0).weight (x.2 q)
      congr 1
      symm
      exact Fintype.prod_equiv σ _ _ (fun q => by rw [Equiv.piCongrLeft_apply_apply])
    · funext x
      exact ih (T.2 x.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      physical roots L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical (roots ∘ σ) L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.1, physical roots L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_rowPerm {k : ℕ} (roots : Fin k → I) (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) L) (q : Fin k) :
    mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y) = mark (σ q) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 (σ q), mark q L (KernelTower.pathEquiv (rowPerm roots σ) L y.2)) =
      (y.1.2 (σ q), mark (σ q) L y.2)
    rw [ih]

variable {k L : ℕ}
omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem logWeight_rowPerm (roots : Fin k → I) (σ : Equiv.Perm (Fin k))
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    logWeight base (roots ∘ σ) factor (KernelTower.pathEquiv (rowPerm roots σ) L y) =
      logWeight base roots factor y := by
  simp only [logWeight, physical_rowPerm, mark_rowPerm, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem root_perm (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (σ : Equiv.Perm (Fin k)) :
    root T Q m base (roots ∘ σ) factor = root T Q m base roots factor := by
  have h := KernelTower.backwardLog_transport (rowPerm roots σ) L (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor)
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  simpa only [tower_transport, heq, root] using h

/-- The exact tree-score summand for one term of the full reservoir. -/
noncomputable def treeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots factor))).expect (fun x =>
      f (fun b => physical roots L (S.pathAt b x)) *
        (numerator (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)) /
          factor (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x))))

theorem treeScore_perm (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (σ : Equiv.Perm (Fin k)) (q : Fin k) :
    treeScore S a T Q m base (roots ∘ σ) factor numerator f q =
      treeScore S a T Q m base roots factor numerator f (σ q) := by
  have h := PrescribedTree.tiltedSampleExpect_transport (rowPerm roots σ) S (tower roots L T Q) m
    (logWeight base (roots ∘ σ) factor) (fun x =>
      f (fun b => physical (roots ∘ σ) L (S.pathAt b x)) *
        (numerator (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x)) /
          factor (roots (σ q)) (physical (roots ∘ σ) L (S.pathAt a x)) (mark q L (S.pathAt a x))))
  have heq : logWeight base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm roots σ) L =
      logWeight base roots factor := funext (fun y => logWeight_rowPerm roots σ base factor y)
  rw [heq] at h
  rw [tower_transport] at h
  refine h.trans ?_
  apply congrArg
  funext x
  simp only [Function.comp_apply, PrescribedTree.pathAt_sampleEquiv, physical_rowPerm, mark_rowPerm]

theorem abs_treeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    |treeScore S a T Q m base roots factor numerator f q| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
  have hd : |numerator (roots q) (physical roots L (S.pathAt a x))
      (mark q L (S.pathAt a x))| /
      factor (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)) ≤ 2 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
    linarith [hn (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x)),
      hA (roots q) (physical roots L (S.pathAt a x)) (mark q L (S.pathAt a x))]
  calc
    _ ≤ |f (fun b => physical roots L (S.pathAt b x))| * 2 :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ ≤ B * 2 := mul_le_mul_of_nonneg_right (hf _) (by norm_num)
    _ = 2 * B := mul_comm _ _

end DilutedSpinGlass.HeterogeneousMarks

 

namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L : ℕ}

/-- Replacement may change the complete mark alphabet and prior of that term;
it is proved by two independent insertions, not by identifying the alphabets. -/
theorem root_update_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I) (q : Fin k) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Function.update roots q i) factor - root T Q m base roots factor| ≤ 2*C := by
  classical
  cases k with
  | zero => exact Fin.elim0 q
  | succ k =>
    let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 q
    let row := roots ∘ σ
    let tail := Fin.tail row
    have hrows : Function.update roots q i ∘ σ = Fin.cons i tail := by
      funext j
      refine Fin.cases ?_ (fun t => ?_) j
      · simp [σ]
      · have hneq : σ t.succ ≠ q := by
          have h0 : σ 0 = q := Equiv.swap_apply_left _ _
          rw [← h0]
          exact fun h => Fin.succ_ne_zero t (σ.injective h)
        simp only [Function.comp_apply, Function.update_of_ne hneq, Fin.cons_succ]
        rfl
    have hold : roots ∘ σ = Fin.cons (roots q) tail := by
      have hzero : row 0 = roots q := by simp [row, σ]
      rw [← hzero]
      exact (Fin.cons_self_tail row).symm
    rw [← root_perm T Q m base (Function.update roots q i) factor σ,
      ← root_perm T Q m base roots factor σ, hrows, hold]
    have hnew := root_cons_bound T Q m hm base tail i factor (hf i)
    have hold' := root_cons_bound T Q m hm base tail (roots q) factor (hf (roots q))
    calc
      _ ≤ |root T Q m base (Fin.cons i tail) factor - root T Q m base tail factor| +
          |root T Q m base tail factor - root T Q m base (Fin.cons (roots q) tail) factor| :=
        abs_sub_le _ _ _
      _ ≤ C+C := by rw [abs_sub_comm (root T Q m base tail factor)]; exact add_le_add hnew hold'
      _ = 2*C := by ring

/-- Physical disorder changes only the base energy, even with all countably
many type laws available to the finite realized auxiliary row. -/
theorem root_base_stability (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base base' : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hb : ∀ x, |base x-base' x| ≤ C) :
    |root T Q m base roots factor-root T Q m base' roots factor| ≤ C := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [logWeight, add_sub_add_right_eq_sub] using hb (physical roots L y)

end DilutedSpinGlass.HeterogeneousMarks

 

namespace DilutedSpinGlass.HeterogeneousMarks
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Add-one score on an old n-factor model with an independent mark process.
The old Gibbs tower includes every one of its original selected-type terms. -/
noncomputable def insertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) m
      (logWeight base roots factor)) (markPrior L (Q i))) m
    (fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
      (KernelTower.pathSnd L y))))).expect (fun x =>
        f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)) /
            factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
              (KernelTower.pathSnd L (S.pathAt a x))))

/-- Literal change-of-variables and successive-tilt proof of the Palm insertion.
No conditional factorization of the tilted mark rows is being assumed. -/
theorem treeScore_insertion (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 =
      insertedTreeScore S a T Q m base roots i factor numerator f := by
  have h := PrescribedTree.tiltedSampleExpect_transport (split roots i) S
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
    (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
      (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
        (KernelTower.pathSnd L (S.pathAt a x)) /
        factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
          (KernelTower.pathSnd L (S.pathAt a x))))
  have heq : insertedLog base roots factor i ∘
      KernelTower.pathEquiv (split roots i) L = logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  have ht : KernelTower.tilt L (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) m
      (insertedLog base roots factor i) =
      KernelTower.tilt L (KernelTower.prod L
        (KernelTower.tilt L (tower roots L T Q) m (logWeight base roots factor))
        (markPrior L (Q i))) m
        (fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
          (KernelTower.pathSnd L y))) := by
    rw [← KernelTower.tilt_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
      (logWeight base roots factor), KernelTower.tilt_insertion]
    rfl
  rw [ht] at h
  simp only [Function.comp_def, PrescribedTree.pathAt_sampleEquiv,
    physical_split, mark_split_zero] at h
  change _ = insertedTreeScore S a T Q m base roots i factor numerator f
  exact h.symm

/-- Density version of the same identity. The numerator is at the selected
anchor and its own new factor occurs exactly once in the denominator. -/
theorem insertedTreeScore_density (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hroot : m 0 = 0)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    let U := KernelTower.prod L
      (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ) (logWeight base roots factor))
      (markPrior L (Q i))
    let g := fun y => Real.log (factor i (physical roots L (KernelTower.pathFst L y))
      (KernelTower.pathSnd L y))
    insertedTreeScore S a T Q (fun j => m j.succ) base roots i factor numerator f =
      (S.sampleLaw U).expect (fun x =>
        (f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          (numerator i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)) /
            factor i (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
              (KernelTower.pathSnd L (S.pathAt a x)))) *
                Real.exp (S.vertexPotential U m g x)) := by
  dsimp only
  exact PrescribedTree.sampleLaw_tilt_expect S _ m hm hroot _ _

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Full countable-type Palm for the literal tilted tree statistic. Its right
side uses the same original reservoir, plus one independently sampled mark. -/
theorem full_reservoir_palm {L : ℕ} (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    (∫ n : ℕ, ∫ roots, ∑ q, treeScore S a T Q m base roots factor numerator f q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots,
        insertedTreeScore S a T Q m base roots i factor numerator f
          ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  rw [CountableReservoir.poisson_add_label ν s
    (fun n roots q => treeScore S a T Q m base roots factor numerator f q)
    (fun _ roots q => abs_treeScore_le S a T Q m base roots factor numerator f q hf hn hA)
    (fun _ σ roots q => treeScore_perm S a T Q m base roots factor numerator f σ q)]
  simp_rw [treeScore_insertion]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
