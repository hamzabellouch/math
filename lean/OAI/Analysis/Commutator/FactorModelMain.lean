import Mathlib
import OAI.Analysis.Commutator.FactorFieldLocalization
import OAI.Analysis.Commutator.FieldMembership

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_in_factor_model
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htP : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htQ : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (hfiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (hglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  choose T hm hb he hq using (fun i j => exists_member_field μ P Q
    (fun s hs => (hdiag s hs).2) test ht htb htQ hglobaldense (X i j) (hX i j))
  have hmem : ∀ᵐ a ∂μ,∀ i j,T i j a∈Q a :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hq i j))
  have hg := localized_matrix_commutator_bound μ P Q hfac hdiag test ht htb htP
    hfiberdense Y h hh T hm (fun i j => norm_nonneg (X i j)) hb hmem
  simpa only [←he] using hg

end Kadison.Decomposable

end

end
end

end OAI
