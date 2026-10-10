import OAI.Analysis.KadisonKastler.SupportCompressedMatrix
import OAI.Analysis.KadisonKastler.CentralSupportScalar

namespace OAI

/-! # Increasing matrix stages in the full support corner -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def supportCompressedStages (A : ℕ → FiniteMatrixStage M)
    (v : Algebra M) (hv : star v * v = 1)
    (hc : ∀ n i j, (v * star v) * (A n).units.entry i j =
      (A n).units.entry i j * (v * star v)) : ℕ → FiniteMatrixStage M :=
  fun n => ⟨(A n).size,(A n).positive,supportCompressedMatrixUnits (A n).units v hv (hc n)⟩

theorem supportCompressedStages_mono (A : ℕ → FiniteMatrixStage M)
    (v : Algebra M) (hv : star v * v = 1)
    (hc : ∀ n i j, (v * star v) * (A n).units.entry i j =
      (A n).units.entry i j * (v * star v))
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    Monotone (fun n => (supportCompressedStages A v hv hc n).units.concreteAlgebra) := by
  intro m n hmn
  exact supportCompressedMatrixUnits_mono (A m).units (A n).units v hv (hc m) (hc n) (hA hmn)

theorem supportCompressedStages_irreducible
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ})
    (v : Algebra M) (hv : star v * v = 1)
    (hvp : v * star v = (vectorSupportProjection M ξ).val)
    (hc : ∀ n i j, (v * star v) * (A n).units.entry i j =
      (A n).units.entry i j * (v * star v)) :
    ∀ T ∈ M,
      (∀ r ∈ FiniteMatrixStage.generatedVonNeumann (supportCompressedStages A v hv hc),
        r * T = T * r) → ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  intro T hT hcomm
  let a : Algebra M := ⟨T,hT⟩
  let b : Algebra M := v * a * star v
  have hbp : b * (vectorSupportProjection M ξ).val = b := by
    rw [← hvp]
    dsimp [b]
    calc
      (v * a * star v) * (v * star v) = v * a * (star v * v) * star v := by
        simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one]
  have hbcomm (n : ℕ) (i j : Fin (A n).size) :
      (A n).units.entry i j * b = b * (A n).units.entry i j := by
    let F := supportCompressedMatrixUnits (A n).units v hv (hc n)
    have hF : F.entry i j * a = a * F.entry i j := by
      apply Subtype.ext
      exact hcomm (F.entry i j).val
        (FiniteMatrixStage.stage_le_generated (supportCompressedStages A v hv hc) n
          ((F.mem_concreteAlgebra _).mpr (F.entry_mem i j)))
    dsimp [b]
    calc
      _ = ((A n).units.entry i j * v) * a * star v := by simp only [mul_assoc]
      _ = v * (F.entry i j * a) * star v := by
        rw [supportCompressedMatrixUnits_intertwine (A n).units v hv (hc n) i j]
        rfl
      _ = v * (a * F.entry i j) * star v := by rw [hF]
      _ = v * a * (F.entry i j * star v) := by simp only [mul_assoc]
      _ = (v * a * star v) * (A n).units.entry i j := by
        rw [← supportCompressedMatrixUnits_intertwine_star (A n).units v hv (hc n) i j]
        simp only [mul_assoc]
  obtain ⟨z,hz⟩ := scalar_on_support_of_central_line A J hright ξ hξ hline b hbp hbcomm
  have he := congrArg (fun c : Algebra M => star v * c * v) hz
  have hr (x : Algebra M) : star v * (v * x * star v) * v = x := by
    calc
      _ = (star v * v) * x * (star v * v) := by simp only [mul_assoc]
      _ = x := by rw [hv,one_mul,mul_one]
  have hp : star v * (vectorSupportProjection M ξ).val * v = 1 := by
    rw [← hvp]
    simpa only [mul_one] using hr (1 : Algebra M)
  change star v * (v * a * star v) * v = star v * (z • (vectorSupportProjection M ξ).val) * v at he
  rw [hr,mul_smul_comm,smul_mul_assoc,hp] at he
  exact ⟨z,congrArg (fun c : Algebra M => c.val) he⟩

end

end KadisonKastler

end OAI
