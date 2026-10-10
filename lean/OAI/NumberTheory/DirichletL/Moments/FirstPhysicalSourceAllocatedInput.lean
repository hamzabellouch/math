import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocatedInputDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

theorem common_energy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (haS : a≤s.lower) (hbS : s.upper≤b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
      (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑B : actualAllocations s.pools C,
          (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
            childNormalizedGaussSource s C R L B τ t W K := by
  have hh := CenteredMomentFirstAllocationGaussEnergy.normalized_common_energy_bound N a b ha
    (original s R seed) hcard s.pools_ne s.prime C hC hseed τ t L W K hK hW
    s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos s.M
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.ν_bound s.W_bound
    (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
  rw [← commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
    (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
      ∑B : actualAllocations s.pools C,
        (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
          (CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
            CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)) at hh
  simpa only [allocated_input_energy] using hh

lemma allocated_input_masked_energy (s : Input ι) (C R T seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s (R*T) seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s (R*T) seed) C L B)=
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) L).columns
      (CenteredMomentFirstMaskedFamily.maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) L).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) := by
  rw [allocated_input_energy,CenteredMomentFirstMaskedInput.normalized_child_mask]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
