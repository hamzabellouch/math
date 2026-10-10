import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def averageWeight : ℂ := (RayQuotient.classNumber M H:ℂ)⁻¹^(Fintype.card ι)

def sectorValue (χ η₀ : Character) (R : Ideal O) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (θ : ι→RayQuotient.Characters M H) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (twistedIdealSum (excluded χ R) W₁ t X₁*twistedIdealSum (excluded χ R) W₂ t X₂)*
      ∏i,(P i:ℂ)^(Complex.I*t)*
        primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ (θ i))) R)
          (V i) (b i) (P i) (σ i) (t+v i)

theorem natural_relative_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*annularWeight (V i) (P i) (σ i) (v i) I) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ V b P σ v t X₁ X₂ θ := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ hX (fun i=>(hP i).le)]
  unfold selectedProduct
  simp_rw [F.masked_plain R hR]
  simp_rw [natural_relative_slot M H hH F η₀ R hR _ _ _ _ _ _ (hP _)]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.prod_sum,
    sectorValue,averageWeight]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  ring

theorem averageWeight_mass :
    ∑_θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖=1 := by
  have hc : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : (RayQuotient.classNumber M H:ℝ)≠0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  simp only [averageWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fun,hc,
    norm_pow,norm_inv,Complex.norm_natCast,nsmul_eq_mul,Nat.cast_pow]
  rw [inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hn)]

theorem sector_average_energy (f : (ι→RayQuotient.Characters M H)→ℂ) :
    ‖averageWeight (ι:=ι) M H*∑θ,f θ‖^2≤
      ∑θ,‖averageWeight (ι:=ι) M H‖*‖f θ‖^2 := by
  have hm:=averageWeight_mass (ι:=ι) M H
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hm
  have he:=CubicEisenstein.norm_sum_sq_le_card Finset.univ f
  rw [norm_mul,mul_pow]
  apply (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq
  rw [←Finset.mul_sum]
  change ‖averageWeight (ι:=ι) M H‖^2*
    ((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*∑θ,‖f θ‖^2)=_
  calc
    _=‖averageWeight (ι:=ι) M H‖*((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*
      ‖averageWeight (ι:=ι) M H‖)*(∑θ,‖f θ‖^2) := by ring
    _= _ := by rw [hm,mul_one]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
