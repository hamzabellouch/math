import Mathlib
import OAI.Analysis.Commutator.FactorModelMain
import OAI.Analysis.Commutator.FiberCommutes
import OAI.Analysis.Commutator.FiberFactorProducer

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

theorem uniform_commutator_in_central_model
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q R : Ω → VonNeumannAlgebra H)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test cotest : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (hs : ∀ n ξ,AEStronglyMeasurable (fun a => cotest n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (hsb : ∀ n,∀ᵐ a ∂μ,‖cotest n a‖≤1)
    (htP : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (hsP : ∀ n,operator μ (cotest n) (hs n) (hsb n)∈P.commutant)
    (htQ : ∀ n,∀ᵐ a ∂μ,test n a∈Q a)
    (hsR : ∀ n,∀ᵐ a ∂μ,cotest n a∈R a)
    (hfiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (hcofiberdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈R a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => cotest (k n) a ξ) atTop (𝓝 (A ξ)))
    (hglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (test (k n)) (ht (k n)) (htb (k n)) f) atTop (𝓝 (A f)))
    (hcoglobaldense : ∀ A : Lp H 2 μ →L[ℂ] Lp H 2 μ,A∈P.commutant → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ f,Tendsto
        (fun n => operator μ (cotest (k n)) (hs (k n)) (hsb (k n)) f) atTop (𝓝 (A f)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ B : H →L[ℂ] H,Commute
        (operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  have hPd : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈Set.centralizer
        (P.commutant : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
    intro s hs B hB
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hB _ (hdiag s hs).1).symm
  have hPmem : ∀ A,A∈P → FieldMember μ Q A := by
    intro A hA
    obtain ⟨T,hm,hb,he,hmem⟩ := exists_member_field μ P Q (fun s hs => (hdiag s hs).2)
      test ht htb htQ hglobaldense A hA
    exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,hmem⟩
  have hPcmem : ∀ A,A∈P.commutant → FieldMember μ R A := by
    intro A hA
    obtain ⟨T,hm,hb,he,hmem⟩ := exists_member_field μ P.commutant R hPd
      cotest hs hsb hsR hcoglobaldense A hA
    exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,hmem⟩
  have hRQ := commutant_ae_of_dense_commuting_fields μ Q R test cotest ht hs htb hsb
    (fun i j => VonNeumannAlgebra.mem_commutant_iff.mp (hsP j) _ (htP i))
    hfiberdense hcofiberdense
  have hfac := factors_ae_of_central_geometry μ P Q R hPmem hPcmem hRQ hcenter
  exact uniform_commutator_in_factor_model μ P Q hfac hdiag test ht htb htP htQ
    hfiberdense hglobaldense Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
