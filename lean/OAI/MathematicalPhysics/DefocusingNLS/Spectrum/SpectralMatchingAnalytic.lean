import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingMatrix

namespace OAI

/-! The actual regular/outgoing matching determinant is holomorphic. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)
local notation "J₄" => Fin 2 × Fin 2

theorem spectralMatchingDeterminant_analyticAt (R₀ R₁ O₀ O₁ : ℂ → E₄) (z : ℂ)
    (hR₀ : AnalyticAt ℂ R₀ z) (hR₁ : AnalyticAt ℂ R₁ z)
    (hO₀ : AnalyticAt ℂ O₀ z) (hO₁ : AnalyticAt ℂ O₁ z) :
    AnalyticAt ℂ (fun lam => spectralMatchingDeterminant (R₀ lam) (R₁ lam) (O₀ lam) (O₁ lam)) z := by
  have hc (j : J₄) : AnalyticAt ℂ
      (fun lam => spectralMatchingColumns (R₀ lam) (R₁ lam) (O₀ lam) (O₁ lam) j) z := by
    rcases j with ⟨i,j⟩
    fin_cases i <;> fin_cases j
    · exact hR₀
    · exact hR₁
    · exact hO₀
    · exact hO₁
  have hentry (i j : J₄) : AnalyticAt ℂ
      (fun lam => spectralMatchingMatrix (R₀ lam) (R₁ lam) (O₀ lam) (O₁ lam) i j) z := by
    let L := (ContinuousLinearMap.proj i).comp spectralStateCoordinates.toLinearMap.toContinuousLinearMap
    exact (L.analyticAt _).comp
      (f := fun lam => spectralMatchingColumns (R₀ lam) (R₁ lam) (O₀ lam) (O₁ lam) j)
      (x := z) (hc j)
  simp_rw [spectralMatchingDeterminant,Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hentry (σ i) i

end DefocusingNLS

end OAI
