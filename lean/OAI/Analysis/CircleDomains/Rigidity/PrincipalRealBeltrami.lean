import OAI.Analysis.CircleDomains.Rigidity.ConductivityAlgebra
import OAI.Analysis.CircleDomains.Rigidity.ConductivityCoefficient
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates

namespace OAI

/-! The precise classical real-coefficient principal Beltrami input.

Published source: Clop and Cruz, *Weighted estimates for Beltrami
equations*, Ann. Acad. Sci. Fenn. Math. 38 (2013), 91–113,
DOI 10.5186/aasfm.2013.3818, section 4, opening paragraph, p. 107.
Their theorem states existence of a principal W^{1,2}_loc plane homeomorphism
for compactly supported measurable coefficients mu, nu with
|mu|+|nu| bounded by k<1. We use only mu=0 and real nu=q.

No height, energy inequality, extremality, circle model, or limiting
assertion is included in this input. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

structure PlaneLocalWeakComplex (f : EuclideanPlane → ℂ) where
  realGradient : EuclideanPlane → EuclideanPlane
  imagGradient : EuclideanPlane → EuclideanPlane
  real_weak : DeGiorgi.HasWeakGrad realGradient (fun x => (f x).re) univ
  imag_weak : DeGiorgi.HasWeakGrad imagGradient (fun x => (f x).im) univ
  real_memLp : ∀ R i, MemLp (fun x => realGradient x i) 2
    (volume.restrict (Metric.ball 0 R))
  imag_memLp : ∀ R i, MemLp (fun x => imagGradient x i) 2
    (volume.restrict (Metric.ball 0 R))

 def PrincipalRealBeltrami : Prop :=
  ∀ (q : EuclideanPlane → ℝ), AEStronglyMeasurable q volume →
    (∃ K : Set EuclideanPlane, IsCompact K ∧ ∀ x ∉ K, q x = 0) →
    ∀ k : ℝ≥0, k < 1 → (∀ᵐ x ∂volume, ‖q x‖ ≤ k) →
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z - z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᵐ x ∂volume,
        planarDbar (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1) =
        q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1))

 def conductivityValue (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) : ℝ := by
  classical
  exact if x ∈ F then (n : ℝ) else 1

 theorem conductivityCoefficient_ratio (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) :
    conductivityCoefficient F n x =
      (conductivityValue F n x - 1) / (conductivityValue F n x + 1) := by
  classical
  by_cases hx : x ∈ F <;> simp [conductivityCoefficient, conductivityValue, hx]

 theorem exists_principal_conductivity_coordinate (hprincipal : PrincipalRealBeltrami)
    {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z - z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0 := by
  obtain ⟨φ, D, ht, he⟩ := hprincipal (conductivityCoefficient F n)
    (conductivityCoefficient_memLp hF n).aestronglyMeasurable
    ⟨F, hF, fun x hx => indicator_of_notMem hx _⟩
    (conductivityRatio n hn) (conductivityRatio_lt_one n hn)
    (Eventually.of_forall (conductivityCoefficient_bound F n hn))
  refine ⟨φ, D, ht, ?_⟩
  filter_upwards [he] with x hx
  have hk : 0 ≤ conductivityValue F n x := by
    classical
    unfold conductivityValue
    split <;> positivity
  apply (conductivity_system_iff hk).mp
  rwa [conductivityCoefficient_ratio] at hx

end CircleDomainRigidity

end

end OAI
