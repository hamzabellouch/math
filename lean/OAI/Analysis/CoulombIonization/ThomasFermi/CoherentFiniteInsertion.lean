import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoherentPhaseBasis
import OAI.Analysis.CoulombIonization.Variational.SpinFinite

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma coherentOrbital_tsupport_subset {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) :
    tsupport (coherentOrbital hg hcg μ i) ⊆ coherentSpatialSupport g K := by
  apply closure_minimal _ (coherentSpatialSupport_compact hcg hK).isClosed
  intro x hx
  by_contra hn
  exact hx (coherentOrbital_zero_outside hg hcg μ hμ i hn)

theorem price_le_coherent_finite_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμle : μ ≤ volume)
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (coherentSpatialSupport g K))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOrbitalEnergy Z lam
        (fun i : Fin 2 × s => coherentWeight hg.continuous hcg μ i.2.1.1)
        (fun i => spinLift (coherentOrbital hg.continuous hcg μ i.2.1.1) i.1) +
      ∑ i : Fin 2 × s, coherentWeight hg.continuous hcg μ i.2.1.1 *
        orbitalCoreInteraction ψ (spinLift (coherentOrbital hg.continuous hcg μ i.2.1.1) i.1) := by
  classical
  apply price_le_correlated_fintype_insertion hψ
  · intro i σ
    exact spinLift_smooth (coherentOrbital_smooth hg hcg μ hK hμ i.2.1.1) i.1 σ
  · intro i σ
    exact spinLift_compact (coherentOrbital_compact hg.continuous hcg μ hK hμ i.2.1.1) i.1 σ
  · apply spinFinite_orthonormal (u := fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)
    intro i j
    rw [coherentOrbital_inner hg hcg μ hK hμ i.1.1 j.1.1 i.1.2.ne' j.1.2.ne']
    simp only [(orthonormal_iff_ite.mp (coherentBasis hg.continuous hcg μ).orthonormal),
      Subtype.ext_iff]
  · exact hcore
  · intro i σ
    exact spinLift_separated (hsep.mono_right
      (coherentOrbital_tsupport_subset hg.continuous hcg μ hK hμ i.2.1.1)) i.1 σ
  · exact hZ
  · exact hlam
  · intro i
    exact ⟨i.2.1.2.le,coherentWeight_le_one hg hcg hgn μ hμle i.2.1.1⟩

end CoulombAtom

end

end OAI
