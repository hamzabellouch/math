import OAI.NumberTheory.DukePrimeDegree.Geometry.ProjectiveLeafEquality
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixFactorChart

namespace OAI

/-! # Projective root-leaf comparison with different coordinate origins -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

lemma factorSlice_orbit (k : Fin n) (z : C.factorPivotDomain s g k) (t : ℝ) :
    rootQuotientParametrization s.distinct (C.factorSlice s g k z,t) =
      rightAction (Quotient.mk _ ((g * z.val.1.1.val) * C.base z.val.1.2))
        (z.val.2.val * Matrix.SpecialLinearGroup.transvection s.distinct
          (t - rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) := by
  rw [C.factorSlice_param s g k z t]
  change Quotient.mk _ ((g * (z.val.1.1.val * (C.base z.val.1.2 * z.val.2.val))) *
      Matrix.SpecialLinearGroup.transvection s.distinct _) =
    Quotient.mk _ (((g * z.val.1.1.val) * C.base z.val.1.2) *
      (z.val.2.val * Matrix.SpecialLinearGroup.transvection s.distinct _))
  simp only [mul_assoc]

end RootPrefixCoordinates

theorem exists_nullset_shifted_initial_root_leaves (d : ℕ)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d+1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (s : InitialRootStep (d+1)) (x : X (d+1))
        (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root))
        (t u a b : ℝ) (ν ρ : Measure ℝ),
        IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure ρ →
        0 < ν (Metric.ball t 1) → 0 < ρ (Metric.ball u 1) →
        let y₁ := rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct (t+a))
        let y₂ := rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct (u+b))
        y₁ ∉ N → y₂ ∉ N →
        intrinsicRootLeaf s.distinct μ y₁ = basedRealMeasure ν t →
        intrinsicRootLeaf s.distinct μ y₂ = basedRealMeasure ρ u →
        ∀ J : Set ℝ, anchorNormalize (ν.map (Homeomorph.addRight a)) J =
          anchorNormalize (ρ.map (Homeomorph.addRight b)) J := by
  obtain ⟨N,hN,hN0,hhol⟩ := exists_nullset_all_initial_root_holonomy d μ hA
  refine ⟨N,hN,hN0,?_⟩
  intro s x w₁ w₂ t u a b ν ρ hν hρ hνt hρu y₁ y₂ hy₁ hy₂ h₁ h₂ J
  let : IsLocallyFiniteMeasure ν := hν
  let : IsLocallyFiniteMeasure ρ := hρ
  have H := hhol s x w₁ w₂ (t+a) (u+b) hy₁ hy₂
  rw [h₁,h₂] at H
  exact anchorNormalize_eq_of_shifted_rebasedRealMeasure_eq ν ρ J t u a b hνt hρu H

end DukePrimeDegree

end

end OAI
