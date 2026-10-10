import OAI.Analysis.CircleDomains.Modulus.PhysicalPieceLength

namespace OAI

/-! Finite physical length of the actual collar concatenation. The bound
is proved before applying allowed-path stability. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalDyadicLength_collarPieces_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (η : C(PathTime, X))
    (hmatch : ∀ n s, η (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s)
    (k : ℕ) (i : Fin (2 ^ k)) :
    physicalDyadicLength e y₀ k i η ≤
      ∑' n, physicalTimeLength e y₀ (γ n)
        (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
          (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) := by
  by_cases hη : η ∈ pathsInsideOn U (dyadicLeft k i) (dyadicRight k i)
  · rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ k i η hη,
      collar_variation_sum]
    apply ENNReal.tsum_le_tsum
    intro n
    exact physicalSubpath_piece_length e hU y₀ (γ n) η
      (collarTime_strictAnti (Nat.lt_succ_self n)) (hmatch n) (dyadicLeft_le_right k i) hη
  · simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hη]
    have hz : eVariationOn (ContinuousMap.const PathTime y₀) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact bot_le

theorem physicalDomainLength_collarPieces_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (η : C(PathTime, X))
    (hmatch : ∀ n s, η (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalDomainLength e y₀ η ≤ ∑' n, physicalDomainLength e y₀ (γ n).val := by
  apply iSup_le
  intro k
  calc
    physicalStageLength e y₀ k η ≤
        ∑ i : Fin (2 ^ k), ∑' n, physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) :=
      Finset.sum_le_sum fun i _ => physicalDyadicLength_collarPieces_le e hU y₀ γ η hmatch k i
    _ = ∑' n, ∑ i : Fin (2 ^ k), physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) := by
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun i : Fin (2 ^ k) =>
        fun n => physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i)))))
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [sum_monotone_dyadic_mass _ _
        (rescalePathTime_monotone (collarTime_strictAnti (Nat.lt_succ_self n))),
        ← physicalTimeLength_univ e y₀ (γ n)]
      exact measure_mono (subset_univ _)

def finitePhysicalCollarConcatenation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (p : X) (γ : ℕ → FinitePhysicalPath e y₀)
    (hjoin : ∀ n, (γ (n + 1)).val ⊤ = (γ n).val ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, (γ n).val s ∈ V)
    (hfinite : (∑' n, physicalDomainLength e y₀ (γ n).val) < ∞) :
    FinitePhysicalPath e y₀ :=
  ⟨collarConcatenation p (fun n => (γ n).val) hjoin htail,
    (physicalDomainLength_collarPieces_le e hU y₀ γ _
      (collarConcatenation_affine p (fun n => (γ n).val) hjoin htail)).trans_lt hfinite⟩

end CircleDomainRigidity

end

end OAI
