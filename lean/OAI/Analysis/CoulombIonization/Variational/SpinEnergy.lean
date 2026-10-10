import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoherentDensityTrace
import OAI.Analysis.CoulombIonization.Variational.CompactPotential

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinEnergy_scope

open MeasureTheory
open scoped BigOperators ContDiff

lemma spinFinite_energy {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, Continuous (u i)) (Z lam : ℝ) :
    finiteOrbitalEnergy Z lam (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) =
      (∑ a : Fin 3, ∑ i, p i * ∫ x : Space, ‖fderiv ℝ (u i) x (EuclideanSpace.single a 1)‖^2) -
      2*Z*(∑ i, p i * CoulombAnalysis.tfPotential (fun y => ‖u i y‖^2) 0) +
      2 * (∫ r : Space × Space, spatialFiniteDensity p u r.1 * spatialFiniteDensity p u r.2 / ‖r.1-r.2‖) +
      2*lam*(∑ i, p i) := by
  have ht (i : Fin 2 × ι) :
      (∫ z : SlaterParticle, ‖spinLift (u i.2) i.1 z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) =
      CoulombAnalysis.tfPotential (fun y => ‖u i.2 y‖^2) 0 := by
    simpa only [orbitalPole,zero_sub,norm_neg] using spinLift_pole (u i.2) i.1 0
  have hd := spatialFiniteDensity_continuous p hu
  have hm : Measurable (fun r : Space × Space =>
      spatialFiniteDensity p u r.1 * spatialFiniteDensity p u r.2 / ‖r.1-r.2‖) :=
    ((hd.measurable.comp measurable_fst).mul (hd.measurable.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)
  simp only [finiteOrbitalEnergy,spinFinite_kinetic,ht,spinFinite_density]
  rw [spinPair_integral_spatial hm]
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma spinFinite_core {N : ℕ} {ι : Type*} [Fintype ι] (ψ : FormVector N) (p : ι → ℝ)
    (u : ι → Space → ℂ) :
    (∑ i : Fin 2 × ι, p i.2 * orbitalCoreInteraction ψ (spinLift (u i.2) i.1)) =
      2 * ∑ i, p i *coreDensityInteraction ψ (fun y => ‖u i y‖^2) := by
  simp only [spinLift_core_interaction,Fintype.sum_prod_type,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]

end Work_SpinEnergy_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma coherentOrbital_pole_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) (a : Space) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 *
        CoulombAnalysis.tfPotential (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) a)
      (CoulombAnalysis.tfPotential (coherentDensity g μ) a) := by
  have hd := coherentDensity_continuous hg.continuous μ hK hμ
  have hs := coherentDensity_compact hcg μ hK hμ
  have hi := CoulombAnalysis.tfPotential_integrable (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs) a
  have hw : Integrable (fun x : Space => |‖a-x‖⁻¹| * coherentDensity g μ x) := by
    simpa only [abs_inv,abs_norm,div_eq_mul_inv,mul_comm] using hi
  have hW : AEStronglyMeasurable (fun x : Space => ‖a-x‖⁻¹) volume :=
    (continuous_const.sub continuous_id).norm.measurable.inv.aestronglyMeasurable
  simpa only [CoulombAnalysis.tfPotential,div_eq_mul_inv,mul_comm] using
    coherentOrbital_weight_hasSum hg hcg μ hK hμ hW hw

lemma coherentOrbital_core_coordinate_hasSum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Spins N) (j : Fin N) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ∫ x : Configuration N,
        ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential
          (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) (x j))
      (∫ x : Configuration N, ‖ψ.value s x‖^2 *
        CoulombAnalysis.tfPotential (coherentDensity g μ) (x j)) := by
  have hi := core_compact_potential_integrable hψ
    (coherentDensity_continuous hg.continuous μ hK hμ) (coherentDensity_compact hcg μ hK hμ) s j
  have hh := nonneg_series_weight_hasSum volume
    (f := fun (i : CoherentPositiveIndex hg.continuous hcg μ) (x : Configuration N) =>
      coherentWeight hg.continuous hcg μ i.1 * CoulombAnalysis.tfPotential
        (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) (x j))
    (W := fun x : Configuration N => ‖ψ.value s x‖^2)
    (d := fun x : Configuration N => CoulombAnalysis.tfPotential (coherentDensity g μ) (x j))
    (fun i => by
      have hd := (coherentOrbital_smooth hg hcg μ hK hμ i.1).continuous.norm.pow 2
      have hs := compact_norm_sq (coherentOrbital_compact hg.continuous hcg μ hK hμ i.1)
      exact continuous_const.mul ((CoulombAnalysis.tfPotential_continuous
        (hd.integrable_of_hasCompactSupport hs) (hd.memLp_of_hasCompactSupport hs)).comp
          (continuous_apply j)) |>.aestronglyMeasurable)
    (fun i x => mul_nonneg i.2.le (integral_nonneg (fun y => div_nonneg (sq_nonneg _) (norm_nonneg _))))
    ((hψ.1 s).aestronglyMeasurable.norm.pow 2)
    (by simpa only [abs_pow,abs_norm] using hi)
    (Eventually.of_forall (fun x => coherentOrbital_pole_hasSum hg hcg μ hK hμ (x j)))
  simpa only [mul_left_comm (‖ψ.value s _‖^2) (coherentWeight _ _ _ _),integral_const_mul] using hh

lemma coherentOrbital_core_hasSum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * coreDensityInteraction ψ
        (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2))
      (coreDensityInteraction ψ (coherentDensity g μ)) := by
  have hh := hasSum_sum (s := (Finset.univ : Finset (Spins N))) (fun s _ =>
    hasSum_sum (s := (Finset.univ : Finset (Fin N))) (fun j _ =>
      coherentOrbital_core_coordinate_hasSum hψ hg hcg μ hK hμ s j))
  simpa only [coreDensityInteraction,Finset.mul_sum] using hh

end CoulombAtom

end

end OAI
