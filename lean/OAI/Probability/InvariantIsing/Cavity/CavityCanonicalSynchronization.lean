import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalLabels
import OAI.Probability.InvariantIsing.Spectral.SpectralCanonicalIdentification

namespace OAI

/-! The limiting Ward equations give the canonical monotone spectral
labels on every off-diagonal entry, not only along quantile parameters. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_canonical_group_synchronization {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0) :
    let p := spectralSpinQuantilePath Q hP hn
    (∀ a, q a.castSucc = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j → ∀ a : Fin m,
        (x (i,j) a.castSucc : ℝ) =
          cavityCanonicalCoordinate ρ eig hρ hρsum p a (spectralSpinArray x i j) := by
  intro p
  obtain ⟨hdq, hc⟩ := spectralCanonical_identification hgg hG q hq hd hE hP hn
    ρ eig hρ hρsum hoff hdiag
  refine ⟨hdq, ?_⟩
  have hall (a : Fin m) : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
      (x (i,j) a.castSucc : ℝ) =
        cavityCanonicalCoordinate ρ eig hρ hρsum p a (spectralSpinArray x i j) := by
    apply spectral_factor_all_off_diagonal hE a _
      (continuous_cavityCanonicalCoordinate ρ eig hρ hρsum p a)
    have hsingle : ∀ b, 0 ≤ (Pi.single a.castSucc 1 : Fin (m + 1) → ℝ) b := by
      intro b
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hp : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
        spectralLinearArray (spectralSpinWeight m) x 0 1 ∈ Icc (0 : ℝ) 1 := by
      simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
    have he := factor_of_pair_law pathMeasure (Q : Measure (SpectralArray (m + 1)))
      p (spectralGroupQuantilePath Q hn a)
      (fun x => spectralLinearArray (spectralSpinWeight m) x 0 1)
      (fun x => spectralLinearArray (Pi.single a.castSucc 1) x 0 1)
      p.measurable (spectralGroupQuantilePath Q hn a).measurable
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (spectralQuantilePath_pair_law hgg hG q hq hd (fun e => hE e e.injective)
        (spectralSpinWeight m) (Pi.single a.castSucc 1) (spectralSpinWeight_nonneg m)
        hsingle hp (spectralCoordinate_unit hn a.castSucc))
      (cavityCanonicalCoordinate ρ eig hρ hρsum p a)
      (continuous_cavityCanonicalCoordinate ρ eig hρ hρsum p a)
      (by
        filter_upwards [hc] with s hs
        exact (hs a).trans (cavityCanonicalCoordinate_at_path ρ eig hρ hρsum p a s).symm)
    simpa only [spectralLinearArray_spinWeight, spectralLinearArray_single,
      spectralCoordinateArray] using he
  filter_upwards [ae_all_iff.mpr hall] with x hx
  intro i j hij a
  exact hx a i j hij

end InvariantIsing

end

end OAI
