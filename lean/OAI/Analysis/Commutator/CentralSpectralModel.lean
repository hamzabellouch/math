import Mathlib
import OAI.Analysis.Commutator.CentralRepresentationModel
import OAI.Analysis.Commutator.ClosedCStarOrder
import OAI.Analysis.Commutator.PointwiseStarHom

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]

theorem uniform_commutator_in_central_spectral_model_nonzero [NeZero μ]
    (P : VonNeumannAlgebra (Lp H 2 μ))
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
  obtain ⟨S,hclosedS,hsepS,hSP,hSS⟩ := exists_separable_cstar_bicommutant P
  obtain ⟨T,hclosedT,hsepT,hTP,hTT⟩ := exists_separable_cstar_bicommutant P.commutant
  let : IsClosed (S:Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := hclosedS
  let : IsClosed (T:Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := hclosedT
  let : CStarAlgebra S := StarSubalgebra.cstarAlgebra S
  let : CStarAlgebra T := StarSubalgebra.cstarAlgebra T
  let : StarOrderedRing S := ClosedCStar.starOrderedRing S
  let : StarOrderedRing T := ClosedCStar.starOrderedRing T
  let : TopologicalSpace.SeparableSpace S := hsepS
  let : TopologicalSpace.SeparableSpace T := hsepT
  obtain ⟨σ,hm,hact⟩ := exists_pointwise_starHom μ S.subtype (by
    intro a s hs
    exact (hdiag s hs).2 a (hSP a.property))
  obtain ⟨σc,hmc,hactc⟩ := exists_pointwise_starHom μ T.subtype (by
    intro a s hs
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hTP a.property) _ (hdiag s hs).1).symm)
  have hrS : S.subtype.range=S := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a,ha⟩,rfl⟩
  have hrT : T.subtype.range=T := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a,ha⟩,rfl⟩
  exact uniform_commutator_in_representation_model μ P S.subtype σ T.subtype σc
    hm hmc hact hactc (by rwa [hrS]) (by rwa [hrT]) hdiag hcenter Y h hh X hX

theorem uniform_commutator_in_central_spectral_model
    (P : VonNeumannAlgebra (Lp H 2 μ))
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
  by_cases hz : μ=0
  · have hY : Y=0 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      simp only [hz,MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    have hd : diagonalAmplification h Y=0 := by
      ext f i
      simp [hY,diagonalAmplification_apply]
    rw [hd,zero_mul,mul_zero,sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
  · let : NeZero μ := ⟨hz⟩
    exact uniform_commutator_in_central_spectral_model_nonzero μ P hdiag hcenter Y h hh X hX

end Kadison.Decomposable

end

end
end

end OAI
