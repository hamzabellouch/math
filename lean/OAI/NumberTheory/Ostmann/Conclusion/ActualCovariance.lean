import OAI.NumberTheory.Ostmann.Conclusion.ActualSymmetrization

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

def actualPermutationCovariance {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    (a b : Γ) : ℝ :=
  pairCovariance
    (fun y : AmplitudeSample sources seed giant spectator m l × AllowedFrequency V l =>
      (amplitudePrior sources seed giant spectator m l).mass y.1)
    (fun γ y => actualCoefficientRow sources seed V giant spectator m X G g bins l
      (amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ) y.1) y.2) a b

theorem actualSymmetrizedEnergy_le_of_covariance
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    {r n : ℕ} (hr : 0<r) (hn : 0<n)
    (σ : Equiv.Perm (Fin r × Fin n) → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    {B ε : ℝ} (hB : 0≤B) (hε : 0≤ε)
    (hbad : ∀a b,TransferBadArrangement (a⁻¹*b) →
      actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b≤B)
    (hgood : ∀a b,¬TransferBadArrangement (a⁻¹*b) →
      actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b≤ε) :
    actualSymmetrizedEnergy sources seed V giant spectator m X G g bins l σ hσ ≤
      (r:ℝ)^(2*r)*Real.exp ((2-(3/4:ℝ)*Real.log r)*(r:ℝ)*n)*B+ε := by
  have h := slot_average_energy_bound hr hn
    (fun y : AmplitudeSample sources seed giant spectator m l × AllowedFrequency V l =>
      (amplitudePrior sources seed giant spectator m l).mass y.1)
    (fun γ y => actualCoefficientRow sources seed V giant spectator m X G g bins l
      (amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ) y.1) y.2)
    hB hε hbad hgood
  simpa only [actualSymmetrizedEnergy,priorSymmetrizedCoefficient,FinitePrior.mean,
    Fintype.sum_prod_type,Finset.mul_sum] using h

theorem actualRegularEnergy_nonneg (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (l : ℕ) :
    0≤actualRegularEnergy sources seed V giant spectator m g giantTransform l := by
  unfold actualRegularEnergy FinitePrior.mean
  exact Finset.sum_nonneg (fun y hy => mul_nonneg
    ((amplitudePrior sources seed giant spectator m l).mass_nonneg y)
    (Finset.sum_nonneg (fun s hs => sq_nonneg _)))

theorem actualAmplitude_sq_le_of_covariance
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    {r n : ℕ} (hr : 0<r) (hn : 0<n)
    (σ : Equiv.Perm (Fin r × Fin n) → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    {R B ε : ℝ} (hB : 0≤B) (hε : 0≤ε)
    (hreg : actualRegularEnergy sources seed V giant spectator m g giantTransform l≤R)
    (hbad : ∀a b,TransferBadArrangement (a⁻¹*b) →
      actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b≤B)
    (hgood : ∀a b,¬TransferBadArrangement (a⁻¹*b) →
      actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b≤ε) :
    ‖actualAmplitude sources seed V giant spectator m X G g giantTransform bins l‖^2 ≤
      R*((r:ℝ)^(2*r)*Real.exp ((2-(3/4:ℝ)*Real.log r)*(r:ℝ)*n)*B+ε) := by
  refine (actualAmplitude_symmetrized_bound sources seed V giant spectator m X G g giantTransform bins l σ hσ).trans ?_
  calc
    _ ≤ actualRegularEnergy sources seed V giant spectator m g giantTransform l *
        ((r:ℝ)^(2*r)*Real.exp ((2-(3/4:ℝ)*Real.log r)*(r:ℝ)*n)*B+ε) :=
      mul_le_mul_of_nonneg_left
        (actualSymmetrizedEnergy_le_of_covariance sources seed V giant spectator m X G g bins l hr hn σ hσ hB hε hbad hgood)
        (actualRegularEnergy_nonneg _ _ _ _ _ _ _ _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hreg (by positivity)

end Ostmann.Conclusion

end

end OAI
