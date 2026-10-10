import OAI.NumberTheory.DirichletL.Energy.ZeroBalancedAdmission
import OAI.NumberTheory.DirichletL.Energy.SourceInputReindexGates

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentSourceInputReindex
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstRetainedNorm CenteredMomentAmplificationChildInput
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α β:Type*}[Fintype α][Fintype β]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance : DecidableEq (β⊕Fin 2):=Classical.decEq _

lemma physical_mass_map (e:α≃β)(s:Input α)(R seed:Ideal O)(m A:O)
    (Ψ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass (reindex e s) R seed m A Ψ K Z ξ=physicalMass s R seed m A Ψ K Z ξ:=by
  have hc:coefficient (reindex e s) R seed=coefficient s R seed:=by
    simpa only [CenteredMomentFirstAmplificationChoice.OriginalData.beta,
      CenteredMomentFirstAmplificationChoice.OriginalData.profile,original,coefficient]
      using coefficient_map e s R seed
  have hp:CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools)=
      CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools):=by
    rw [←pools_map e s,CenteredMomentSourceMass.finiteColumns,Finset.image_image]
    congr 1
    funext v
    exact tupleMap_product e v
  have hv:CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData=
      CenteredMomentExceptionalAmplitudePair.volume s.toData:=volume_map e s
  have hs (T:Finset (Ideal O))(C D:Ideal O)
      (hC:CanonicalQuadraticSieve.Supported C)(hD:CanonicalQuadraticSieve.Supported D)
      (t X:ℝ):
      sectorMass (reindex e s) R seed m A t T C D hC hD Ψ K X Z ξ=
      sectorMass s R seed m A t T C D hC hD Ψ K X Z ξ:=by
    unfold sectorMass
    rw [sourceRadius_map e s]
    simp only [hc, show (reindex e s).η=s.η from rfl]
  let sumAt (T:Finset (Ideal O))(t X:ℝ):ℝ:=
    ∑p:CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns T) (CenteredMomentSourceRow.supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).1
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).2 Ψ K X Z ξ
  have hl:physicalMass (reindex e s) R seed m A Ψ K Z ξ=
      sumAt (CenteredMomentActiveSource.activeSource
        (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools))
        (coefficient (reindex e s) R seed)) s.t
        (CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData):=by
    unfold physicalMass
    dsimp only
    exact Finset.sum_congr rfl (fun p _=>hs _ _ _ _ _ _ _)
  rw [hl]
  rw [hc,hp,hv]
  rfl

def emptyEquiv (α:Type*)[Fintype α]:Fin 0≃(∅:Finset α):=Equiv.equivOfIsEmpty _ _

variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def emptyBalanced (α:Type*)[Fintype α]:Input (∅:Finset α):=
  reindex (emptyEquiv α)
    (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)

lemma empty_balanced_mass (R seed:Ideal O)(m A:O)(Ψ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α) R seed m A Ψ K Z₀ ξ=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        R seed m A Ψ K Z₀ ξ:=
  physical_mass_map (emptyEquiv α) _ R seed m A Ψ K Z₀ ξ

lemma empty_balanced_volume : volume (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α)=X₁*X₂:=by
  rw [emptyBalanced,volume_map,CenteredMomentEnergyZeroReferencePhysical.balanced_volume]

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex

end

end OAI
