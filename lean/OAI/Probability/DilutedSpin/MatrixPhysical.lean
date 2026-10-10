import OAI.Probability.DilutedSpin.CompleteShapeSelection
import OAI.Probability.DilutedSpin.ShapeMatrixPhysical

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Centered exact-matrix multioverlap history of the actual physical root.
The root alphabet includes every sampled marker, and its entire old test is
retained. This definition uses no analytic decorrelation identity. -/
noncomputable def physicalMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  matrixRootCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m) (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun _ => rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
    (fun z x => f (fun b => physical (rootArray z.2.2.1 z.2.2.2) (L+1) (S.pathAt b x)))

lemma physicalShape_matrix (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    physicalShapeCovariance m S a M C H N u (matrixSplitTest T q) true f =
      physicalMatrixCovariance m S a M C H N u T q f := by
  exact shapeCovariance_matrix S a
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) T q f
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend hB hf
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hk

/-- The centered matrix term in `root_matrix_energy` really tends to zero,
simultaneously for all target shapes, old trees and bounded physical tests,
on the SAME concrete low-increment sequence supplied by the perturbation. -/
theorem physical_matrix_selection (m : Fin (L+1) → ℝ)
    (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior m direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ (S : PrescribedTree (L+1)) (a : S.Leaf)
        (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
        (B : ℝ), 0 ≤ B → (∀ n x, |f n x| ≤ B) →
        ∀ (k : ℕ), 0 < k → ∀ (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf),
        Tendsto (fun n => physicalMatrixCovariance m S a M C H (Ns n+1) (us n)
          T q (f n)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,hshape⟩ := complete_shape_selection m M hC hH hc
    hθ hh hθi hhi hm hmono hend hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro S a f B hB hf k hk T q
  have h := hshape S a f B hB hf k (matrixSplitTest T q) true
  simpa only [physicalShape_matrix hk m (fun j => hc.trans_le (hm j)) hmono hend
      S a M C H _ _ T q _ hB (hf _)] using h

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
