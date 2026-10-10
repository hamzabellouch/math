import Mathlib
import OAI.Analysis.Commutator.CentralGeometryModel
import OAI.Analysis.Commutator.RepresentationFieldTests

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A B : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

theorem uniform_commutator_in_representation_model
    (P : VonNeumannAlgebra (Lp H 2 μ))
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρc : B →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σc : Ω → B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
    (hmc : ∀ b ξ,AEStronglyMeasurable (fun x => σc x b ξ) μ)
    (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x))
    (hactc : ∀ b (f : Lp H 2 μ),ρc b f =ᵐ[μ] fun x => σc x b (f x))
    (hP : NormalGNS.bicommutant ρ.range=P)
    (hPc : NormalGNS.bicommutant ρc.range=P.commutant)
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ C : H →L[ℂ] H,Commute
        (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z)
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (Lp H 2 μ →L[ℂ] Lp H 2 μ)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨test,ht,hb,htP,htQ,hfd,hgd⟩ := exists_common_tests μ ρ σ hm hact
  obtain ⟨cotest,hs,hc,hsP,hsR,hcfd,hcgd⟩ := exists_common_tests μ ρc σc hmc hactc
  rw [hP] at htP hgd
  rw [hPc] at hsP hcgd
  exact uniform_commutator_in_central_model μ P
    (fun x => NormalGNS.bicommutant (σ x).range)
    (fun x => NormalGNS.bicommutant (σc x).range) hdiag test cotest ht hs hb hc
    htP hsP htQ hsR hfd hcfd hgd hcgd hcenter Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
