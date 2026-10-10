import Mathlib
import OAI.Analysis.FreeWords.PatchingNearFull

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem unitary_admissible_small
    (hF : IsFactor M) (hD : IsDiffuse M)
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hXfin : X.Finite) (hKfin : K.Finite)
    (hXnorm : ∀ x∈X, ‖x‖≤1) (hXcenter : ∀ x∈X, τ.map x=0)
    (hKzero : ∀ k∈K, k≠0) (hK1 : 1∈K) (hKm1 : -1∈K)
    (ε : ℝ) (hε : 0<ε) :
    ∃ u : unitary (ConcreteAlgebra M), ∀ A, PatchingWord.Admissible X K N A →
      ‖τ.map (A.value (fun k => (u^k).val))‖<ε := by
  let D : ℝ := 2^N
  have hD0 : 0<D := by positivity
  let η := min (1/2:ℝ) (ε/(4*D))
  have hη : 0<η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η≤1 := (min_le_left _ _).trans (by norm_num)
  have hηsmall : D*η≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1/2:ℝ) (ε/(4*D))) hD0.le
    have he : D*(ε/(4*D))=ε/4 := by field_simp
    simpa only [he] using hh
  let C := D*(2/η+1)
  have hC : 0≤C := by positivity
  let E := Real.exp (C*(1-η))
  have hE : 0<E := Real.exp_pos _
  let δ := ε/(4*(E+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have hδsmall : patchingBudget δ C (1-η)≤ε/4 := by
    change δ*(E-1)≤ε/4
    have he : δ*(E+1)=ε/4 := by dsimp only [δ]; field_simp
    calc
      _ ≤ δ*(E+1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := he
  obtain ⟨u,hu⟩ := unitary_admissible_bound τ hF hD hXfin hKfin hXnorm hXcenter
    hKzero hK1 hKm1 hδ hC hη hη1 (le_refl C)
  refine ⟨u,fun A hA => ?_⟩
  have hb := hu A hA
  change _≤patchingBudget δ C (1-η)+D*η at hb
  linarith

end

end KKLocalPatching
end

end OAI
