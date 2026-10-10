import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureInformation
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixWindows

namespace OAI

/-! # Boundedness and finite mass survive the one-step future shift -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

theorem ae_bounded_one_future_of_zero (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (μ : Measure (X (d+1)))
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (hbound : ∀ᵐ x ∂μ, c.remainingFutureAtom ell hell Q 0 x ⊆ c.cube 1) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, c.remainingFutureAtom ell hell Q 1 x ⊆ c.cube R := by
  let E := c.rootDilation ell 1
  have hK : IsCompact (E ⁻¹' c.closedCube 1) := by
    rw [← E.image_symm]
    exact (c.closedCube_compact 1).image E.symm.continuous
  obtain ⟨j,hj⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ _)
    (c.remainingWindow_mono 1).directed_le
  filter_upwards [hT.quasiMeasurePreserving.ae hbound] with x hx
  refine ⟨1+j,?_⟩
  rw [← c.remainingFutureAtom_shift ell hell Q x]
  exact fun v hv => hj (c.cube_subset_closedCube 1 (hx hv))

theorem ae_one_future_mass_pos_ne_top (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x) ≠ 0 ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x) ≠ ∞ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M k x := c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q k x)
  let C x := c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  filter_upwards [hmass,hT.quasiMeasurePreserving.ae hmass,
    c.ae_remainingTimeProduct_futureAtom d hP hf μ hA ell hell Q hQ,
    c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA] with x hx hTx hcov hC
  have hmono : M 0 x ≤ M 1 x :=
    measure_mono (c.remainingFutureAtom_zero_subset_one ell hell Q x)
  refine ⟨(hx.1.trans_le hmono).ne',?_⟩
  have he : M 1 x = C x * M 0 (T x) := by
    change M 0 (T x) = (C x)⁻¹ * M 1 x at hcov
    rw [hcov,←mul_assoc,ENNReal.mul_inv_cancel hC.1.ne' hC.2,one_mul]
  change M 1 x ≠ ∞
  rw [he]
  exact ENNReal.mul_ne_top hC.2 (ne_of_lt (hTx.2.trans_lt ENNReal.one_lt_top))

end EliminationChain
end DukePrimeDegree

end

end OAI
