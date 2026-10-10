import OAI.Probability.DilutedSpin.FullRegularSelection
import OAI.Probability.DilutedSpin.RootMarkerEstimate

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance (β : Type) : DecidableEq β := Classical.decEq β
variable {Z : Type} [MeasurableSpace Z] {h N k : ℕ}

noncomputable def markerMatrixCovariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree h) (a : S.Leaf) (T : PrescribedTree h) (q : Option (Fin k) → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) h) (m : Fin (h+1) → ℝ)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) : ℝ :=
  matrixRootCovariance μ Ω T S q K m
    (List.ofFn (fun c : Fin k => (some c : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
    (fun z => treeOverlap S (V z))

@[simp] lemma markerMatrixCovariance_heightCast {h' : ℕ} (e : h=h')
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree h) (a : S.Leaf) (T : PrescribedTree h) (q : Option (Fin k) → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) h) (m : Fin (h+1) → ℝ)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) :
    markerMatrixCovariance μ Ω (heightCast e S) (leafHeightCast e S a)
      (heightCast e T) (fun c => leafHeightCast e T (q c))
      (fun z => kernelHeightCast e (K z)) (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
      (fun z => vectorHeightCast e (V z)) = markerMatrixCovariance μ Ω S a T q K m V := by
  cases e
  rfl

@[simp] lemma overlapVariance_heightCast {h' : ℕ} (e : h=h')
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)] (S : PrescribedTree h)
    (K : (z : Z) → KernelTower (Ω z) h)
    (V : (z : Z) → FinitePath (Ω z) h → Fin N → ℝ) :
    overlapVariance μ Ω (heightCast e S) (fun z => kernelHeightCast e (K z))
      (fun z => vectorHeightCast e (V z)) = overlapVariance μ Ω S K V := by
  cases e
  rfl

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

noncomputable def physicalMarkerMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) : ℝ :=
  markerMatrixCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S a T q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma physicalShape_marker (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    physicalShapeCovariance m S a M C H N u (matrixSplitTest T q) false
      (spatialProduct (fun _ : S.Leaf => readVector
        (fun v x => readSpin (KernelTower.terminalState L x) v))) =
      physicalMarkerMatrixCovariance m S a M C H N u T q := by
  have hh := shapeCovariance_marker S a
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) T q
    (spatialProduct (fun _ : S.Leaf => readVector
      (fun v x => readSpin (KernelTower.terminalState L x) v)))
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend
    (by norm_num : (0:ℝ)≤1) (fun x => spatialProduct_bound _ (fun _ y i => readVector_bound _ y i) x)
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hk
  refine hh.trans ?_
  unfold physicalMarkerMatrixCovariance markerMatrixCovariance
  congr 1
  funext z x
  rw [treeOverlap_eq_spatialProduct]
  rfl

lemma FullShapeControl.marker {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ) (hk : 0<k)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    Tendsto (fun n => physicalMarkerMatrixCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) T q) atTop (𝓝 0) := by
  let F := fun n => spatialProduct (fun _ : S.Leaf =>
    readVector (fun v x => readSpin (KernelTower.terminalState L x) v) (N := Ns n+1))
  have hF : ∀ n x, |F n x|≤1 := fun n x => spatialProduct_bound _
    (fun _ y i => readVector_bound _ y i) x
  have hs := h.shape S a F 1 (by norm_num) hF k (matrixSplitTest T q) false
  simpa only [F,physicalShape_marker hk (gridExponents L) (gridExponents_pos L)
    (gridExponents_mono L) (gridExponents_last L)] using hs

end DilutedSpinGlass.UniversalDictionary

end

end OAI
