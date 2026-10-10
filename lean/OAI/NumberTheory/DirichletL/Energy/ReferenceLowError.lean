import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError
import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceHomogeneousError QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem relative_slot_error {α:Type*}(F:Finset α)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi bshort:ℝ)(ha:0<aslot)
    (hs:Function.support Wslot⊆Set.Icc aslot bslot)(hc:Continuous Wslot):
    ∃C:ℝ,0<C ∧ ∀T:Finset α,T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(ν:α→Character)(pool:α→Finset (Ideal O))
        (P σ freq:α→ℝ)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) → (∀i∈T,lo≤σ i) → (∀i∈T,σ i≤hi) →
      (∀i∈T,∀I∈pool i,Prime I) → (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i)
          (heightCoefficient (fun I=>idealCoeff (ν i) I*
            HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  obtain ⟨B,hB,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi ha hs hc
  obtain ⟨C,hC,he⟩:=natural_reference_error_homogeneous F bshort
    (fun _=>bslot) (fun _=>B) (fun _ _=>hB.le)
  refine ⟨C,hC,?_⟩
  intro T hT W hW χ ν pool P σ freq t X K Φ keep hX hK hP hlo hhi hp hΦ
  apply he T hT W hW χ pool
    (fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
    P t X K Φ keep hX hK hP hp
  · intro i hi I hI
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hb
  · intro i hi I hI hn
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).2
    apply hb
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hΦ

end SevenEighths.CenteredMomentEnergyReferenceLowError

end

end OAI
