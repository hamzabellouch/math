import OAI.Probability.DilutedSpin.MeasurableProjectionError
import OAI.Probability.DilutedSpin.ParameterRate
import OAI.Probability.DilutedSpin.ShapeMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N L : ℕ}
omit [Fintype Ω] in
lemma measurable_treeOverlap (S : PrescribedTree L) {f : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y i, Measurable (fun z => f z y i)) (x : Sample Ω S) :
    Measurable (fun z => treeOverlap S (f z) x) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => measurable_leafProduct S (fun y => hf y i) x)
omit [Fintype Ω] in
lemma treeOverlap_eq_spatialProduct (S : PrescribedTree L) (f : FinitePath Ω L → Fin N → ℝ)
    (x : Sample Ω S) : treeOverlap S f x=spatialProduct (fun _ : S.Leaf => f) (fun b => S.pathAt b x) := by
  simp only [treeOverlap,spatialProduct,leafProduct_eq_prod]
end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y C : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [DecidableEq C] {M N n : ℕ}
attribute [local irreducible] PrescribedTree.matrixProjectionError PrescribedTree.oldProjectionError
    KernelTower.halfTripleDifferenceAt PrescribedTree.splitProjector

variable (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (Q : (i : I) → Fin (n+r+1+d) → FiniteLaw (A i))
    (m : Fin (n+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+r+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+r+1+d) → FinitePath (A i) (n+r+1+d) → ℝ)
    (V : FinitePath Ω (n+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootSplitProjector (z : FullRootState Y X I M)
    (x : FinitePath (rootAlphabet (Ω := Ω) (A := A) z) (n+r+1+d)) (i : Fin N) : ℝ :=
  splitProjector S r d (rootTower T Q m base old z) (fun y => rootVector V z y i) x

include hb in
lemma measurable_rootProjectedTriple : Measurable (fun z : FullRootState Y X I M =>
    KernelTower.halfTripleDifferenceAt (n+r+1+d) (rootTower T Q m base old z) d
      (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    KernelTower.halfTripleDifferenceAt _
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) d
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine KernelTower.measurable_halfTripleDifferenceAt_tilt _ d (tower (rootArray nt y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSplitProjector_bound (hV : ∀ y i, |V y i|≤1) (z : FullRootState Y X I M)
    (x : FinitePath (rootAlphabet (Ω := Ω) (A := A) z) (n+r+1+d)) (i : Fin N) :
    |rootSplitProjector S r d T Q m base old V z x i|≤1 :=
  splitProjector_bound S r d _ _ (fun _ => hV _ i) x

include hb in
lemma integrable_rootProjectedTriple (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
    KernelTower.halfTripleDifferenceAt (n+r+1+d) (rootTower T Q m base old z) d
      (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootProjectedTriple S r d T Q m base old V hb).aestronglyMeasurable 2
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs]
    exact KernelTower.abs_halfTripleDifferenceAt_le_two _ d _ _
      (rootSplitProjector_bound S r d T Q m base old V hV z))

include hb in
omit [Fintype C] [DecidableEq C] in
lemma measurable_rootTargetError (R : PrescribedTree (n+r+1+d)) (q : C → R.Leaf) (a c : C)
    (F : (C → FinitePath Ω (n+r+1+d)) → ℝ) :
    Measurable (fun z : FullRootState Y X I M =>
      matrixProjectionError R q (rootTower T Q m base old z) a c
        (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
        (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    matrixProjectionError R q
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) a c
      (fun w => F (fun b => physical (rootArray nt y) _ (w b)))
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_matrixProjectionError_tilt R q (tower (rootArray nt y) _ T Q) m a c ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

include hb in
omit [Fintype C] [DecidableEq C] in
lemma integrable_rootTargetError (R : PrescribedTree (n+r+1+d)) (q : C → R.Leaf) (a c : C)
    (F : (C → FinitePath Ω (n+r+1+d)) → ℝ)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) (hF : ∀ x, |F x|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      matrixProjectionError R q (rootTower T Q m base old z) a c
        (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
        (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootTargetError S r d T Q m base old V hb R q a c F).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ matrixProjectionError R q (rootTower T Q m base old z) a c
    (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
    (rootSplitProjector S r d T Q m base old V z) from by
      unfold matrixProjectionError; exact FiniteLaw.l2_nonneg _ _)]
  exact matrixProjectionError_le_two R q _ a c _ _ (fun x => hF _)
    (rootSplitProjector_bound S r d T Q m base old V hV z)

include hb in
lemma measurable_rootOldError (R : PrescribedTree (n+r+1+d)) (a b : R.Leaf) :
    Measurable (fun z : FullRootState Y X I M =>
      oldProjectionError R (rootTower T Q m base old z) a b (treeOverlap R (rootVector V z))
        (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    oldProjectionError R
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) a b
      (treeOverlap R (fun w => V (physical (rootArray nt y) _ w)))
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_oldProjectionError_tilt R a b (tower (rootArray nt y) _ T Q) m ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

include hb in
lemma integrable_rootOldError (R : PrescribedTree (n+r+1+d)) (a b : R.Leaf)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      oldProjectionError R (rootTower T Q m base old z) a b (treeOverlap R (rootVector V z))
        (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootOldError S r d T Q m base old V hb R a b).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ oldProjectionError R (rootTower T Q m base old z) a b
    (treeOverlap R (rootVector V z)) (rootSplitProjector S r d T Q m base old V z) from by
      unfold oldProjectionError; exact FiniteLaw.l2_nonneg _ _)]
  exact oldProjectionError_le_two R _ a b _ _ (treeOverlap_bound R _ (fun x i => hV _ i))
    (rootSplitProjector_bound S r d T Q m base old V hV z)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y C : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [DecidableEq C] {L M : ℕ}
attribute [local irreducible] PrescribedTree.matrixObservableHistory

variable (R S : PrescribedTree L) (q : C → R.Leaf) (cs : List C) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (F : (C → FinitePath Ω L) → ℝ) (g : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootMatrixObservableHistory (m' : Fin (L+1) → ℝ) :
    Measurable (fun z : FullRootState Y X I M =>
      matrixObservableHistory R q (rootTower T Q m base old z) m' cs S a
        (fun x => F (fun c => physical (rootArray z.2.2.1 z.2.2.2) L (x c)))
        (fun x => g (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))) := by
  change Measurable (packRoot (fun h k x n y =>
    matrixObservableHistory R q
      (KernelTower.tilt L (tower (rootArray n y) L T Q) m
        (logWeight (base h k x) (rootArray n y) old)) m' cs S a
      (fun x => F (fun c => physical (rootArray n y) L (x c)))
      (fun x => g (fun b => physical (rootArray n y) L (S.pathAt b x)))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_matrixObservableHistory_tilt (tower (rootArray n y) L T Q) m m' R S q cs a ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · exact fun _ => measurable_const

include hb in
/-- Ordinary integrability of the literal signed multileaf history at the
actual variable-alphabet root. This does NOT take its absolute value in the
concentration identity: the crude bound is used only to justify integration. -/
lemma integrable_rootMatrixObservableHistory (μ : Measure (FullRootState Y X I M))
    [IsFiniteMeasure μ] (hF : ∀ x, |F x|≤1) (hg : ∀ x, |g x|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      matrixObservableHistory R q (rootTower T Q m base old z) (grid L 0 L) cs S a
        (fun x => F (fun c => physical (rootArray z.2.2.1 z.2.2.2) L (x c)))
        (fun x => g (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))) μ := by
  classical
  apply Integrable.of_bound (measurable_rootMatrixObservableHistory R S q cs a T Q m base old F g hb
    (grid L 0 L)).aestronglyMeasurable (historyMass (fun _ => 1) cs.length S ((Finset.univ.erase a).card))
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  exact matrixObservableHistory_bound _ R S q cs a _ _ (fun x => hF _) (fun x => hg _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
