import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyActiveChildRestoration
open ConcretePrimeRowBridge
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {β:Type*}:DecidableEq β:=Classical.decEq _

theorem allocated_row_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (z:O)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P D a W₁ W₂ X₁ X₂=
      allocatedPositiveRow e.η e.m e.A z e.t e.slots e.coefficient e.P D a W₁ W₂ X₁ X₂ := by
  change positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => (activeInput s).slots i.val.val)
      (fun i => (activeInput s).toData.coefficient i.val.val)
      (fun i => (activeInput s).P i.val.val) v _ _ =
    positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => s.slots i.val.val)
      (fun i => s.toData.coefficient i.val.val)
      (fun i => s.P i.val.val) v _ _
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have hz (f : Ideal O → ℂ) : heightCoefficient f 0 = f := by
    funext I
    simp [heightCoefficient]
  simpa only [hz] using rowSlot_active s i.val.val τ
    (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z v 0

theorem child_energy_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    childEnergy d rad D a = childEnergy e rad D a := by
  dsimp only
  unfold childEnergy
  apply tsum_congr
  intro z
  exact congrArg₂ (fun x y : ℂ => rad.weight z * (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.X₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.X₂ / Ideal.absNorm (B.val (Sum.inr 1))))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.Y₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.Y₂ / Ideal.absNorm (B.val (Sum.inr 1))))

end SevenEighths.CenteredMomentEnergyActiveChildRestoration

end

end OAI
