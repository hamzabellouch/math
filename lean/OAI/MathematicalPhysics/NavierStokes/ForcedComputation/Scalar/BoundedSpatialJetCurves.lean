import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetProduct
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! Uniform spatial derivative estimates give continuous coefficient curves in jet norm. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets
open scoped Topology NNReal BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_sub_le_of_jets (k : ℕ) (J K : Space E F k) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (i : Fin (k+1)) (x : E), ‖J.val i x - K.val i x‖ ≤ C) :
    ‖J-K‖ ≤ C := by
  change ‖J.val-K.val‖ ≤ C
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le hC).mpr
  exact h i

/-- A common modulus for each derivative controls the Banach-space distance. -/
theorem lipschitzWith_of_jets {A : Type*} [PseudoMetricSpace A] (k : ℕ)
    (J : A → Space E F k) (L : ℝ≥0)
    (h : ∀ s t (i : Fin (k+1)) (x : E),
      ‖(J s).val i x - (J t).val i x‖ ≤ L * dist s t) : LipschitzWith L J := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  exact norm_sub_le_of_jets E F k (J s) (J t) (mul_nonneg L.coe_nonneg dist_nonneg)
    (h s t)

/-- Bounded derivatives on a compact time interval, with a uniform time modulus. -/
def ofFunctionCurve (k : ℕ) (T : ℝ) (f : ℝ → E → F)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ k (f t)) (C : ℝ)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ C)
    (L : ℝ≥0)
    (hL : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x‖ ≤ L * |s-t|) :
    C(Set.Icc (0 : ℝ) T, Space E F k) where
  toFun := fun t => ofFunction E F k (f t) (hf t t.property) C (hC t t.property)
  continuous_toFun := by
    apply LipschitzWith.continuous (K := L)
    apply lipschitzWith_of_jets E F k _ L
    intro s t i x
    change ‖iteratedFDeriv ℝ i.val (f s) x - iteratedFDeriv ℝ i.val (f t) x‖ ≤
      L * dist s t
    simpa only [Subtype.dist_eq, Real.dist_eq] using
      hL s s.property t t.property i.val (Nat.le_of_lt_succ i.isLt) x

@[simp] theorem function_ofFunctionCurve (k : ℕ) (T : ℝ) (f : ℝ → E → F)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ k (f t)) (C : ℝ)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ C)
    (L : ℝ≥0)
    (hL : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x‖ ≤ L * |s-t|)
    (t : Set.Icc (0 : ℝ) T) (x : E) :
    function E F k (ofFunctionCurve E F k T f hf C hC L hL t) x = f t x :=
  function_ofFunction E F k _ _ _ _ x

end ForcedComputation.BoundedSpatialJets

end

end OAI
