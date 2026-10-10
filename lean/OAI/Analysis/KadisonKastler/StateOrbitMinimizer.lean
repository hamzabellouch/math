import OAI.Analysis.KadisonKastler.StateOrbitCompact

namespace OAI

/-! # The unique least-vector-norm point of an asymptotic orbit hull

Weak compactness supplies a minimizer; the Hilbert parallelogram law
and a separating reference vector make it unique.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_unique_stateOrbitCore_minimizer
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ∃ B ∈ stateOrbitCore ξ a,
      (∀ C ∈ stateOrbitCore ξ a, ‖B ξ‖^2 ≤ ‖C ξ‖^2) ∧
      ∀ C ∈ stateOrbitCore ξ a, ‖C ξ‖^2 ≤ ‖B ξ‖^2 → C=B := by
  have hl : LowerSemicontinuous (fun T : H →WOT[ℂ] H => ‖T ξ‖^2) := by
    simpa only [sub_zero] using wot_vector_sqDistance_lowerSemicontinuous ξ (0 : H)
  obtain ⟨B,hB,hm⟩ := (hl.lowerSemicontinuousOn (stateOrbitCore ξ a)).exists_isMinOn
    ⟨_,self_mem_stateOrbitCore ξ a⟩ (stateOrbitCore_compact ξ a)
  have hmin := isMinOn_iff.mp hm
  refine ⟨B,hB,hmin,?_⟩
  intro C hC hnorm
  let S := (1/2 : ℝ) • B+(1/2 : ℝ) • C
  have hS : S ∈ stateOrbitCore ξ a := stateOrbitCore_convex ξ a hB hC
    (by norm_num) (by norm_num) (by norm_num)
  have hbm := hmin S hS
  have he : S ξ=(1/2 : ℝ) • (B ξ+C ξ) := by
    change (1/2 : ℝ) • B ξ+(1/2 : ℝ) • C ξ=_
    rw [smul_add]
  rw [he,norm_smul] at hbm
  have hp := parallelogram_law_with_norm ℂ (B ξ) (C ξ)
  norm_num at hbm
  have hn : ‖B ξ-C ξ‖=0 := by
    nlinarith [sq_nonneg ‖B ξ-C ξ‖,norm_nonneg (B ξ-C ξ)]
  have hvec : B ξ=C ξ := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hbM := (stateOrbitCore_subset_ball ξ a hB).1
  have hcM := (stateOrbitCore_subset_ball ξ a hC).1
  have hab := hsep (a₁ := ⟨B.toCLM,hbM⟩) (a₂ := ⟨C.toCLM,hcM⟩) hvec
  have heq := congrArg (fun x : Algebra M => x.val) hab
  exact (ContinuousLinearMapWOT.equiv.injective heq).symm

end

end KadisonKastler

end OAI
