import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.TransformedGaussProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTransport

namespace OAI

/-!
One rational program approximates transported Gauss nodes uniformly
for separated manufactured fields, under the smooth flow hypothesis.
-/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

theorem exists_uniform_transport_program (hpublished : PublishedC4FlowInput) :
    ∃ rho U C K : ℕ, 0 < rho ∧ 0 < U ∧ 0 < C ∧
      Nonempty (Turing.TM2ComputableInPolyTime inputCode CappedKernelProgram.tripleCode (output rho U C K)) ∧
      ∃ L J : ℝ≥0, 0 < L ∧ 0 < J ∧ ∀ (scale S : ℚ),
        (1:ℝ) ≤ scale → (1:ℝ) ≤ S → ∀ (m : ℕ) (u : Fin m → ℚ×ℚ),
        Function.Injective u →
        (∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
        (∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
          (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) →
        ∃ G : Position → ℝ → Position,
          IsUnitTimeFlow (moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
            scale S (fun i => PlanarForcingProgram.position (u i)))) G ∧
          Function.Bijective (fun x => G x 1) ∧
          LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith J (fun x => G x 1) ∧
          (∀ x, x ∉ tsupport (manufacturedWellField (GaussianFrequency.frequency rho)
            scale S (fun i => PlanarForcingProgram.position (u i))) → G x 1 = x) ∧
          ContDiff ℝ 4 (fun x => G x 1) ∧
          ∀ (P N : ℕ), 0 < N → ∀ (k : Registers) (b : Signs),
            ‖position (value rho U C K P N scale S (List.ofFn u) k b)-
              G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index k b)) 1‖ ≤ ((P:ℝ)+1)⁻¹ := by
  obtain ⟨rho,hrho,L,J,hL,hJ,hfamily⟩ := manufactured_transport_family_with_charge hpublished
  obtain ⟨U,C,hU,hC,herror⟩ := exists_uniform_constants rho hrho
  obtain ⟨K,hK⟩ := exists_nat_gt (L:ℝ)
  refine ⟨rho,U,C,K,hrho,hU,hC,⟨certificate rho U C K⟩,L,J,hL,hJ,?_⟩
  intro scale S hs hS m u hu hsep hc
  have hs' : (0:ℝ) < scale := lt_of_lt_of_le zero_lt_one hs
  obtain ⟨hcharge,G,hflow,hbij,hLip,hAnti,hfix,hreg,_⟩ :=
    hfamily (GaussianFrequency.frequency rho) scale S hs' hS m
      (fun i => PlanarForcingProgram.position (u i)) hsep hc
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hreg,?_⟩
  intro P N hN k b
  exact herror K P N hN scale S hs hS m u hu hsep hc hcharge G hflow L hLip hK.le k b

end ContinuumCoulomb.TransformedGauss

end

end OAI
