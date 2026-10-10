import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoherentKinetic
import OAI.Analysis.CoulombIonization.ThomasFermi.CoherentFiniteInsertion
import OAI.Analysis.CoulombIonization.Variational.SpinEnergy

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

def coherentSpinKinetic (g : Space → ℂ) (μ : Measure (Space × Space)) : ℝ :=
  coherentFactor * ∑ a : Fin 3, ∫ q, (∫ x : Space,
    ‖fderiv ℝ (coherentPacket g q.1 q.2) x (EuclideanSpace.single a 1)‖^2) ∂μ

lemma coherentFinite_kinetic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    (∑ a : Fin 3, ∑ i : s, coherentWeight hg.continuous hcg μ i.1.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1.1) x (EuclideanSpace.single a 1)‖^2) ≤
      coherentSpinKinetic g μ := by
  unfold coherentSpinKinetic
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.sum_coe_sort s (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
    coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x (EuclideanSpace.single a 1)‖^2)]
  exact coherentOrbital_kinetic_le hg hcg μ hK hμ s (EuclideanSpace.single a 1)

lemma coherentFinite_direct_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    (∫ r : Space × Space,
      spatialFiniteDensity (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i => coherentOrbital hg.continuous hcg μ i.1.1) r.1 *
      spatialFiniteDensity (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i => coherentOrbital hg.continuous hcg μ i.1.1) r.2 / ‖r.1-r.2‖) ≤
      ∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖ := by
  let p : s → ℝ := fun i => coherentWeight hg.continuous hcg μ i.1.1
  let u : s → Space → ℂ := fun i => coherentOrbital hg.continuous hcg μ i.1.1
  have hc : ∀ i : s, Continuous (u i) := fun i => (coherentOrbital_smooth hg hcg μ hK hμ i.1.1).continuous
  have ht : ∀ i : s, HasCompactSupport (u i) := fun i => coherentOrbital_compact hg.continuous hcg μ hK hμ i.1.1
  have hn : ∀ i : s, 0 ≤ p i := fun i => i.1.2.le
  apply compact_direct_mono (f := spatialFiniteDensity p u) (g := coherentDensity g μ)
    (spatialFiniteDensity_continuous p hc) (coherentDensity_continuous hg.continuous μ hK hμ)
    (spatialFiniteDensity_compact p ht) (coherentDensity_compact hcg μ hK hμ)
    (spatialFiniteDensity_nonneg hn)
  intro x
  change (∑ i : s, coherentWeight hg.continuous hcg μ i.1.1 *
    ‖coherentOrbital hg.continuous hcg μ i.1.1 x‖^2) ≤ _
  rw [Finset.sum_coe_sort s (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
    coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)]
  exact coherentOrbital_density_le hg.continuous hcg μ hK hμ s x

theorem price_le_coherent_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμle : μ ≤ volume)
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (coherentSpatialSupport g K))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N + coherentSpinKinetic g μ +
      2 * (∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖) -
      2*Z*CoulombAnalysis.tfPotential (coherentDensity g μ) 0 +
      2*lam*(∫ x : Space, coherentDensity g μ x) +
      2*coreDensityInteraction ψ (coherentDensity g μ) := by
  classical
  let b (i : CoherentPositiveIndex hg.continuous hcg μ) : ℝ :=
    -(2*Z) * (coherentWeight hg.continuous hcg μ i.1 *
      CoulombAnalysis.tfPotential (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) 0) +
    (2*lam) * coherentWeight hg.continuous hcg μ i.1 +
    2 * (coherentWeight hg.continuous hcg μ i.1 * coreDensityInteraction ψ
      (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2))
  have hm : HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1) (∫ x : Space, coherentDensity g μ x) := by
    rw [coherentDensity_mass hg.continuous hcg μ hK hμ]
    exact coherentPositiveWeight_hasSum hg.continuous hcg μ
  have hs : HasSum b (-(2*Z)*CoulombAnalysis.tfPotential (coherentDensity g μ) 0 +
      (2*lam)*(∫ x : Space, coherentDensity g μ x) + 2*coreDensityInteraction ψ (coherentDensity g μ)) :=
    (((coherentOrbital_pole_hasSum hg hcg μ hK hμ 0).mul_left (-(2*Z))).add
      (hm.mul_left (2*lam))).add ((coherentOrbital_core_hasSum hψ.sobolevFermion.sobolevVector hg hcg μ hK hμ).mul_left 2)
  have hb (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
      priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N + coherentSpinKinetic g μ +
        2 * (∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖) +
        ∑ i ∈ s, b i := by
    have hf := price_le_coherent_finite_insertion hψ hg hcg hgn μ hμle hK hμ A hcore hsep hZ hlam s
    rw [spinFinite_energy (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
      (u := fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)
      (fun i => (coherentOrbital_smooth hg hcg μ hK hμ i.1.1).continuous) Z lam,
      spinFinite_core ψ (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)] at hf
    have hk := coherentFinite_kinetic_le hg hcg μ hK hμ s
    have hd := coherentFinite_direct_le hg hcg μ hK hμ s
    rw [← Finset.sum_coe_sort s b]
    simp only [b,Finset.sum_add_distrib,← Finset.mul_sum]
    linarith
  have hh := ge_of_tendsto (tendsto_const_nhds.add hs) (Eventually.of_forall hb)
  convert hh using 1
  first | rfl | ring

end CoulombAtom

end

end OAI
