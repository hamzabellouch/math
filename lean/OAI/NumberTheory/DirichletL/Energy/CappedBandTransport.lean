import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedBandTransport
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma saturated_successor (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (hsaturated:bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k=Mcap)
    (h:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε k):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0<reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hwidth:bandWidth Mcap Bs ε (k+1)≤bandWidth Mcap Bs ε k:=by
    rw [hsaturated]
    exact bandWidth_le _ _ _ _
  have hloss:stageLoss Mcap Bs ε k≤stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨degree,S,hcert⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCz,hCp,hbound⟩:=hcert η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCz,hCp,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le hlower le_rfl le_rfl le_rfl
      hlength hwidth hloss le_rfl (Finset.Subset.refl _) hCz.le le_rfl hZ.2.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      hlower le_rfl le_rfl le_rfl hlength hwidth hloss le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hZ.2.2

end SevenEighths.CenteredMomentEnergyCappedBandTransport

end

end OAI
