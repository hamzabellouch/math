import OAI.Analysis.Mahler.SourceRawOrientation
import OAI.Analysis.Mahler.SourceCoordinateMeasure

namespace OAI

namespace Mahler
noncomputable section

/-- The calculated top-slot order is the positive
interleaved real/imaginary order. -/
theorem sourceTopSlots_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    (sourceTopSlots k s).val = (finProdFinEquiv (pairSlotEquiv (k+1) s)).val := by
  cases s with
  | inl b => fin_cases b <;> rfl
  | inr s =>
    change 1 + (1 + ((pairSlotEquiv k s).2.val + 2 * (pairSlotEquiv k s).1.val)) =
      (pairSlotEquiv k s).2.val + 2 * ((pairSlotEquiv k s).1.val + 1)
    omega

def coordinateCast {a b : ℕ} (h : a = b) : (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) := by
  subst b
  exact ContinuousLinearEquiv.refl ℝ _

lemma coordinateCast_basis {a b : ℕ} (h : a = b) (i : Fin a) :
    coordinateCast h (MahlerStokes.coordinateBasis a i) =
      MahlerStokes.coordinateBasis b (finCongr h i) := by
  subst b
  rfl

def sourceCoordinates (k : ℕ) : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean (k+1) :=
  (coordinateCast (show (2*k+1)+1 = (k+1)*2 by omega)).trans
    (MahlerStokes.complexCoordinates (k+1))

/-- No unproved orientation factor remains in the coordinate frame. -/
theorem sourceCoordinates_top_basis (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sourceCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) (sourceTopSlots k s)) =
      interleavedBasis s := by
  change MahlerStokes.complexCoordinates (k+1)
    (coordinateCast _ (MahlerStokes.coordinateBasis _ (sourceTopSlots k s))) = _
  rw [coordinateCast_basis]
  have hi : finCongr (show (2*k+1)+1 = (k+1)*2 by omega) (sourceTopSlots k s) =
      finProdFinEquiv (pairSlotEquiv (k+1) s) :=
    Fin.ext (sourceTopSlots_interleaved k s)
  rw [hi]
  exact complexCoordinates_wedge_basis s

end
end Mahler

end OAI
