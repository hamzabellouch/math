import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialSourceDictionary
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (s:Data ι) (r:Radial) (S₁ S₂:Finset (Ideal O)) (R L B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R) (hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁) (hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁) (hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hcov₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁) (hcov₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂) :
    sourceRestrictedEnergy r.keep (finiteColumns (tuplePool s.slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)=energy s r L := by
  rw [source_restricted_energy_eq_rectangle s.η s.t r.keep s.slots S₁ S₂ R L
    s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂ r.profile r.scale]
  unfold energy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  have ht:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
  have hc:s.coefficient=(fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)):=rfl
  rw [hc]
  dsimp only [Radial.weight]
  rw [hm,hA,hX₁,hX₂,hY₁,hY₂]
  split_ifs <;> ring

end SevenEighths.CenteredMomentRadialSourceDictionary

end

end OAI
