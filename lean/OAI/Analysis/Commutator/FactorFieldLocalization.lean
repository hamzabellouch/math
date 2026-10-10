import Mathlib
import OAI.Analysis.Commutator.CentralAverage
import OAI.Analysis.Commutator.DiagonalCommute
import OAI.Analysis.Commutator.FactorFieldBound

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω : Type*} {H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem localized_matrix_commutator_bound
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0≤c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h Y*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*
        ‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ := by
  obtain ⟨Z,hz,hd,_⟩ := CentralAverage.exists_center_average P Y
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute Z (indicatorOperator μ s hs) :=
    hz _ (hdiag s hs).1 (hdiag s hs).2
  obtain ⟨T,hT,hb,he⟩ := exists_field_of_commutes_indicator μ Z hcomm
  have hbnd := matrix_commutator_bound_of_countable_factor_fields μ P Q hfac T hT
    (norm_nonneg Z) hb test ht htb htmem htdense h hh X hX hc0 hc hmem
  rw [←he] at hbnd
  convert matrix_commutator_perturb P Y Z hd 3122 (by norm_num) h
    (fun i j => operator μ (X i j) (hX i j) (hc i j)) hbnd using 1
  norm_num

end Kadison.Decomposable

end

end
end

end OAI
