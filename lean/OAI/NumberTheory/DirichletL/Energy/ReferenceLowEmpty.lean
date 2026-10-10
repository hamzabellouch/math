import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem zero_low_positive_empty
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)(hC:0≤C)
    (h:ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C):
    PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hsmall
  have hh:=h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by simpa using hsmall)
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid]
  apply hh.trans
  have hp:(1+‖t‖)^degree≤(1+|t|+height)^degree:=by
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.norm_eq_abs]
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by unfold diagonalControl;positivity))
    (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI
