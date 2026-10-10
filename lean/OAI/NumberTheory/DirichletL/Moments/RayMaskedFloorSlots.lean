import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime
import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel hbeta hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
